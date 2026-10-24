with AArch64.Encode;
with Ada.Containers.Vectors;
with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded;
with Diagnostics;
with GNAT.OS_Lib;
with GNAT.SHA256;
with Interfaces;

package body MachO.Executable is

   use Ada.Strings.Unbounded;
   use Interfaces;
   use Sections;

   package E renames AArch64.Encode;

   --  arm64 macOS의 가상 메모리 페이지와 코드 서명이 해시하는 페이지
   VM_Page   : constant := 16#4000#;
   Hash_Page : constant := 16#1000#;
   Base      : constant Unsigned_64 := 16#1_0000_0000#;

   Dylinker : constant String := "/usr/lib/dyld";

   function Align (N, A : Natural) return Natural is ((N + A - 1) / A * A);

   package Index_Vectors is new Ada.Containers.Vectors (Positive, Positive);

   function Write
     (Obj        : Sections.Object;
      Path       : String;
      Entry_Name : String;
      Identifier : String;
      Dylibs     : Libraries.Library_Vectors.Vector;
      Rpaths     : Libraries.String_Vectors.Vector) return Boolean
   is
      Buf  : Byte_Vectors.Vector;
      Code : Byte_Vectors.Vector := Obj.Contents (Text);

      ------------------------------------------------------------------
      --  바이트 쓰기 (Mach-O는 리틀 엔디언, 코드 서명은 빅 엔디언)

      procedure U8 (V : Natural) is
      begin
         Buf.Append (Byte (V));
      end U8;

      procedure U16 (V : Natural) is
      begin
         U8 (V mod 256);
         U8 (V / 256);
      end U16;

      procedure U32 (V : Unsigned_32) is
      begin
         for K in 0 .. 3 loop
            Buf.Append (Byte (Shift_Right (V, 8 * K) and 16#FF#));
         end loop;
      end U32;

      procedure U32 (V : Natural) is
      begin
         U32 (Unsigned_32 (V));
      end U32;

      procedure U64 (V : Unsigned_64) is
      begin
         U32 (Unsigned_32 (V and 16#FFFF_FFFF#));
         U32 (Unsigned_32 (Shift_Right (V, 32)));
      end U64;

      procedure U64 (V : Natural) is
      begin
         U64 (Unsigned_64 (V));
      end U64;

      procedure BE32_Word (V : Unsigned_32) is
      begin
         for K in reverse 0 .. 3 loop
            Buf.Append (Byte (Shift_Right (V, 8 * K) and 16#FF#));
         end loop;
      end BE32_Word;

      procedure BE32 (V : Natural) is
      begin
         BE32_Word (Unsigned_32 (V));
      end BE32;

      procedure BE64 (V : Natural) is
      begin
         BE32 (0);
         BE32 (V);
      end BE64;

      procedure Name16 (S : String) is
      begin
         for K in 1 .. 16 loop
            U8 (if K <= S'Length then Character'Pos (S (S'First + K - 1))
                else 0);
         end loop;
      end Name16;

      procedure Text_Bytes (S : String) is
      begin
         for C of S loop
            U8 (Character'Pos (C));
         end loop;
      end Text_Bytes;

      procedure Pad_To (N : Natural) is
      begin
         while Natural (Buf.Length) < N loop
            U8 (0);
         end loop;
      end Pad_To;

      function Word_At (V : Byte_Vectors.Vector; Off : Natural)
                        return Unsigned_32 is
        (Unsigned_32 (V.Element (Off))
         or Shift_Left (Unsigned_32 (V.Element (Off + 1)), 8)
         or Shift_Left (Unsigned_32 (V.Element (Off + 2)), 16)
         or Shift_Left (Unsigned_32 (V.Element (Off + 3)), 24));

      procedure Put_Word
        (V : in out Byte_Vectors.Vector; Off : Natural; W : Unsigned_32) is
      begin
         for K in 0 .. 3 loop
            V.Replace_Element
              (Off + K, Byte (Shift_Right (W, 8 * K) and 16#FF#));
         end loop;
      end Put_Word;

      procedure Segment
        (Name : String; VM_Addr, VM_Size : Unsigned_64;
         File_Off, File_Size : Natural; Prot : Natural; N_Sects : Natural;
         Flags : Natural := 0) is
      begin
         U32 (Natural'(16#19#));
         U32 (72 + 80 * N_Sects);
         Name16 (Name);
         U64 (VM_Addr);
         U64 (VM_Size);
         U64 (File_Off);
         U64 (File_Size);
         U32 (Prot);
         U32 (Prot);
         U32 (N_Sects);
         U32 (Flags);
      end Segment;

      procedure Section
        (Name, Seg : String; Off, Size, Align_Log2 : Natural;
         Flags : Unsigned_32; Reserved1, Reserved2 : Natural := 0) is
      begin
         Name16 (Name);
         Name16 (Seg);
         U64 (Base + Unsigned_64 (Off));
         U64 (Size);
         U32 (Off);
         U32 (Align_Log2);
         U32 (Natural'(0));
         U32 (Natural'(0));
         U32 (Flags);
         U32 (Reserved1);
         U32 (Reserved2);
         U32 (Natural'(0));
      end Section;

      ------------------------------------------------------------------
      --  가져오는 심볼과 진입점

      Imports  : Index_Vectors.Vector;
      Ordinals : Index_Vectors.Vector;  --  가져오는 심볼마다 라이브러리 순번
      Entry_Sym : Natural := 0;

      --  경로를 담는 로드 명령의 크기
      function Path_Command (Header : Natural; Text : String) return Natural
      is (Align (Header + Text'Length + 1, 8));

   begin
      for R of Obj.Relocs loop
         if not Obj.Symbols (R.Target).Defined then
            if R.Kind /= Branch26 then
               Diagnostics.Report
                 (Diagnostics.Error,
                  "unimplemented: data imported through #dyn (§10.5)");
               return False;
            elsif not Imports.Contains (R.Target) then
               Imports.Append (R.Target);
            end if;
         end if;
      end loop;
      for I in Obj.Symbols.First_Index .. Obj.Symbols.Last_Index loop
         if Obj.Symbols (I).Name = Entry_Name
           and then Obj.Symbols (I).Defined
           and then Obj.Symbols (I).Section = Text
         then
            Entry_Sym := I;
         end if;
      end loop;
      --  가져오는 심볼마다 처음 내보내는 라이브러리. 내보내기를 다 알지
      --  못하는 라이브러리는 다른 데서 찾지 못했을 때의 마지막 후보다.
      for I of Imports loop
         declare
            Name    : constant String := To_String (Obj.Symbols (I).Name);
            Found   : Natural := 0;
            Partial : Natural := 0;
         begin
            for D in Dylibs.First_Index .. Dylibs.Last_Index loop
               if Found = 0 and then Dylibs (D).Exports.Contains (Name) then
                  Found := D;
               elsif Partial = 0 and then Dylibs (D).Partial then
                  Partial := D;
               end if;
            end loop;
            if Found = 0 then
               Found := Partial;
            end if;
            if Found = 0 then
               Diagnostics.Report
                 (Diagnostics.Error,
                  "link edit failed: undefined symbol '" & Name
                  & "' in the linked libraries");
               return False;
            end if;
            Ordinals.Append (Found);
         end;
      end loop;

      if Entry_Sym = 0 then
         Diagnostics.Report
           (Diagnostics.Error,
            "link edit failed: no entry point '" & Entry_Name & "'");
         return False;
      end if;

      declare
         N_Imp    : constant Natural := Natural (Imports.Length);
         Has_Data : constant Boolean := N_Imp > 0;
         N_Segs   : constant Natural := (if Has_Data then 4 else 3);

         Dylinker_Cmd : constant Natural :=
           Align (12 + Dylinker'Length + 1, 8);
         Dylib_Cmds   : constant Natural :=
           [for L of Dylibs => Path_Command
              (24, To_String (L.Install_Name))]'Reduce ("+", 0);
         Rpath_Cmds   : constant Natural :=
           [for R of Rpaths => Path_Command (12, R)]'Reduce ("+", 0);
         N_Cmds : constant Natural :=
           N_Segs + 7 + Natural (Dylibs.Length) + Natural (Rpaths.Length);
         Cmds : constant Natural :=
           72 + (72 + 3 * 80) + (if Has_Data then 72 + 80 else 0) + 72
           + 16 + 24 + 80 + Dylinker_Cmd + 24 + 24 + Dylib_Cmds + Rpath_Cmds
           + 16;

         --  __TEXT: 헤더, 로드 명령, __text, __stubs, __const
         Text_Off  : constant Natural := Align (32 + Cmds, 16);
         Text_Len  : constant Natural := Natural (Code.Length);
         Stubs_Off : constant Natural := Align (Text_Off + Text_Len, 4);
         Stubs_Len : constant Natural := 12 * N_Imp;
         Const_Off : constant Natural := Align (Stubs_Off + Stubs_Len, 8);
         Const_Len : constant Natural := Size (Obj, Const);
         Text_Seg  : constant Natural :=
           Align (Const_Off + Const_Len, VM_Page);

         --  __DATA_CONST: __got
         Data_Off  : constant Natural := Text_Seg;
         Got_Len   : constant Natural := 8 * N_Imp;
         Data_Seg  : constant Natural :=
           (if Has_Data then Align (Got_Len, VM_Page) else 0);
         LE_Off    : constant Natural := Data_Off + Data_Seg;

         --  chained fixups (LE_Off에서 시작하는 덩어리 안의 오프셋)
         Image_Size   : constant Natural := 4 + 4 * N_Segs;
         Seg_Info     : constant Natural :=
           (if Has_Data then Align (32 + Image_Size, 8)
            else 32 + Image_Size);
         Data_Pages   : constant Natural := Data_Seg / VM_Page;
         Seg_Size     : constant Natural :=
           (if Has_Data then 22 + 2 * Data_Pages else 0);
         Imports_Off  : constant Natural := Align (Seg_Info + Seg_Size, 4);
         Symbols_Off  : constant Natural := Imports_Off + 4 * N_Imp;

         function Import_Name (K : Positive) return String is
           (To_String (Obj.Symbols (Imports (K)).Name));

         Symbols_Len : Natural := 0;
      begin
         for K in 1 .. N_Imp loop
            Symbols_Len := Symbols_Len + Import_Name (K)'Length + 1;
         end loop;

         declare
            Fixups_Size : constant Natural :=
              Align (Symbols_Off + Symbols_Len, 8);

            --  심볼 표: 지역, 정의된 외부(이름 순), 가져온 것
            Locals, Externals : Index_Vectors.Vector;
            Header_Name : constant String := "__mh_execute_header";
            N_Syms : Natural;

            function Name_Of (I : Positive) return String is
              (To_String (Obj.Symbols (I).Name));
         begin
            for I in Obj.Symbols.First_Index .. Obj.Symbols.Last_Index loop
               if Obj.Symbols (I).Defined then
                  if Obj.Symbols (I).Global then
                     declare
                        Pos : Positive := Externals.Last_Index + 1;
                     begin
                        for J in Externals.First_Index .. Externals.Last_Index
                        loop
                           if Name_Of (I) < Name_Of (Externals (J)) then
                              Pos := J;
                              exit;
                           end if;
                        end loop;
                        Externals.Insert (Pos, I);
                     end;
                  else
                     Locals.Append (I);
                  end if;
               end if;
            end loop;
            N_Syms := Natural (Locals.Length) + 1
              + Natural (Externals.Length) + N_Imp;

            declare
               Sym_Off  : constant Natural := LE_Off + Fixups_Size;
               Ind_Off  : constant Natural := Sym_Off + 16 * N_Syms;
               Str_Off  : constant Natural := Ind_Off + 8 * N_Imp;

               Strings  : Unbounded_String :=
                 To_Unbounded_String ("" & ASCII.NUL);
               Str_Size : Natural;
               Sig_Off  : Natural;
               Slots    : Natural;
               CD_Len   : Natural;
               Sig_Size : Natural;
               LE_Size  : Natural;

               function Addr_Of (I : Positive) return Natural is
                 (Obj.Symbols (I).Offset
                  + (if Obj.Symbols (I).Section = Text then Text_Off
                     else Const_Off));

               function Undefined_Index (K : Positive) return Natural is
                 (Natural (Locals.Length) + 1 + Natural (Externals.Length)
                  + K - 1);

               procedure Nlist
                 (Name : String; N_Type, Sect, Desc : Natural;
                  Value : Unsigned_64) is
               begin
                  U32 (Length (Strings));
                  Append (Strings, Name & ASCII.NUL);
                  U8 (N_Type);
                  U8 (Sect);
                  U16 (Desc);
                  U64 (Value);
               end Nlist;

               procedure Defined_Nlist (I : Positive; Ext : Boolean) is
               begin
                  Nlist (Name_Of (I), 16#0E# + (if Ext then 1 else 0),
                         (if Obj.Symbols (I).Section = Text then 1 else 3),
                         0, Base + Unsigned_64 (Addr_Of (I)));
               end Defined_Nlist;

            begin
               --  문자열 표의 크기를 먼저 정한다
               declare
                  Total : Natural := 1 + Header_Name'Length + 1;
               begin
                  for I of Locals loop
                     Total := Total + Name_Of (I)'Length + 1;
                  end loop;
                  for I of Externals loop
                     Total := Total + Name_Of (I)'Length + 1;
                  end loop;
                  for K in 1 .. N_Imp loop
                     Total := Total + Import_Name (K)'Length + 1;
                  end loop;
                  Str_Size := Align (Total, 8);
               end;
               Sig_Off := Align (Str_Off + Str_Size, 16);
               Slots := (Sig_Off + Hash_Page - 1) / Hash_Page;
               CD_Len := 88 + Identifier'Length + 1 + 32 * Slots;
               Sig_Size := Align (20 + CD_Len, 16);
               LE_Size := Sig_Off + Sig_Size - LE_Off;

               ---------------------------------------------------------
               --  재배치 적용 (파일 오프셋 = 가상 주소 - Base)

               for R of Obj.Relocs loop
                  declare
                     P : constant Natural := Text_Off + R.Offset;
                     T : Natural;
                     W : Unsigned_32 := Word_At (Code, R.Offset);
                  begin
                     if Obj.Symbols (R.Target).Defined then
                        T := Addr_Of (R.Target);
                     else
                        T := Stubs_Off + 12 * (Imports.Find_Index (R.Target)
                                               - 1);
                     end if;
                     case R.Kind is
                        when Branch26 =>
                           W := E.Patch_Branch (W, (T - P) / 4);
                        when Page21 =>
                           W := E.Patch_Page (W, T / 4096 - P / 4096);
                        when Page_Off12 =>
                           W := E.Patch_Imm12 (W, T mod 4096);
                     end case;
                     Put_Word (Code, R.Offset, W);
                  end;
               end loop;

               ---------------------------------------------------------
               --  mach_header_64

               U32 (Unsigned_32'(16#FEED_FACF#));
               U32 (Unsigned_32'(16#0100_000C#));
               U32 (Natural'(0));
               U32 (Natural'(2));                     --  MH_EXECUTE
               U32 (N_Cmds);
               U32 (Cmds);
               --  NOUNDEFS | DYLDLINK | TWOLEVEL | PIE
               U32 (Unsigned_32'(16#0020_0085#));
               U32 (Natural'(0));

               Segment ("__PAGEZERO", 0, Base, 0, 0, 0, 0);
               Segment ("__TEXT", Base, Unsigned_64 (Text_Seg), 0, Text_Seg,
                        5, 3);
               Section ("__text", "__TEXT", Text_Off, Text_Len, 2,
                        16#8000_0400#);
               Section ("__stubs", "__TEXT", Stubs_Off, Stubs_Len, 2,
                        16#8000_0408#, 0, 12);
               Section ("__const", "__TEXT", Const_Off, Const_Len, 3, 0);
               if Has_Data then
                  --  SG_READ_ONLY: 바인딩을 마치면 읽기 전용
                  Segment ("__DATA_CONST", Base + Unsigned_64 (Data_Off),
                           Unsigned_64 (Data_Seg), Data_Off, Data_Seg, 3, 1,
                           16#10#);
                  Section ("__got", "__DATA_CONST", Data_Off, Got_Len, 3,
                           16#6#, N_Imp);
               end if;
               Segment ("__LINKEDIT", Base + Unsigned_64 (LE_Off),
                        Unsigned_64 (Align (LE_Size, VM_Page)), LE_Off,
                        LE_Size, 1, 0);

               --  LC_DYLD_CHAINED_FIXUPS
               U32 (Unsigned_32'(16#8000_0034#));
               U32 (Natural'(16));
               U32 (LE_Off);
               U32 (Fixups_Size);

               --  LC_SYMTAB
               U32 (Natural'(2));
               U32 (Natural'(24));
               U32 (Sym_Off);
               U32 (N_Syms);
               U32 (Str_Off);
               U32 (Str_Size);

               --  LC_DYSYMTAB
               U32 (Natural'(16#B#));
               U32 (Natural'(80));
               U32 (Natural'(0));
               U32 (Natural (Locals.Length));
               U32 (Natural (Locals.Length));
               U32 (Natural (Externals.Length) + 1);
               U32 (Natural (Locals.Length) + Natural (Externals.Length) + 1);
               U32 (N_Imp);
               for K in 1 .. 6 loop
                  U32 (Natural'(0));
               end loop;
               U32 ((if N_Imp > 0 then Ind_Off else 0));
               U32 (2 * N_Imp);
               for K in 1 .. 4 loop
                  U32 (Natural'(0));
               end loop;

               --  LC_LOAD_DYLINKER
               declare
                  Start : constant Natural := Natural (Buf.Length);
               begin
                  U32 (Natural'(16#E#));
                  U32 (Dylinker_Cmd);
                  U32 (Natural'(12));
                  Text_Bytes (Dylinker);
                  Pad_To (Start + Dylinker_Cmd);
               end;

               --  LC_BUILD_VERSION: macOS 15.0
               U32 (Natural'(16#32#));
               U32 (Natural'(24));
               U32 (Natural'(1));
               U32 (Natural'(16#000F_0000#));
               U32 (Natural'(16#000F_0000#));
               U32 (Natural'(0));

               --  LC_MAIN
               U32 (Unsigned_32'(16#8000_0028#));
               U32 (Natural'(24));
               U64 (Addr_Of (Entry_Sym));
               U64 (Natural'(0));

               --  LC_LOAD_DYLIB: 순번은 이 순서로 1부터
               for L of Dylibs loop
                  declare
                     Name  : constant String := To_String (L.Install_Name);
                     Start : constant Natural := Natural (Buf.Length);
                  begin
                     U32 (Natural'(16#C#));
                     U32 (Path_Command (24, Name));
                     U32 (Natural'(24));
                     U32 (Natural'(2));
                     U32 (L.Current);
                     U32 (L.Compat);
                     Text_Bytes (Name);
                     Pad_To (Start + Path_Command (24, Name));
                  end;
               end loop;

               --  LC_RPATH
               for R of Rpaths loop
                  declare
                     Start : constant Natural := Natural (Buf.Length);
                  begin
                     U32 (Unsigned_32'(16#8000_001C#));
                     U32 (Path_Command (12, R));
                     U32 (Natural'(12));
                     Text_Bytes (R);
                     Pad_To (Start + Path_Command (12, R));
                  end;
               end loop;

               --  LC_CODE_SIGNATURE
               U32 (Natural'(16#1D#));
               U32 (Natural'(16));
               U32 (Sig_Off);
               U32 (Sig_Size);

               ---------------------------------------------------------
               --  섹션 내용

               Pad_To (Text_Off);
               for B of Code loop
                  Buf.Append (B);
               end loop;
               Pad_To (Stubs_Off);
               for K in 1 .. N_Imp loop
                  declare
                     S : constant Natural := Stubs_Off + 12 * (K - 1);
                     G : constant Natural := Data_Off + 8 * (K - 1);
                  begin
                     U32 (E.Patch_Page (E.Adrp (16), G / 4096 - S / 4096));
                     U32 (E.Load_Store_Unsigned
                            (False, 8, False, 16, 16, G mod 4096));
                     U32 (E.Br (16));
                  end;
               end loop;
               Pad_To (Const_Off);
               for B of Obj.Contents (Const) loop
                  Buf.Append (B);
               end loop;
               Pad_To (Text_Seg);

               --  GOT: DYLD_CHAINED_PTR_64 바인드. next는 4바이트 단위.
               for K in 1 .. N_Imp loop
                  U64 (Shift_Left (Unsigned_64'(1), 63)
                       or Shift_Left (Unsigned_64 (if K < N_Imp then 2
                                                   else 0), 51)
                       or Unsigned_64 (K - 1));
               end loop;
               Pad_To (LE_Off);

               ---------------------------------------------------------
               --  __LINKEDIT: chained fixups

               U32 (Natural'(0));                     --  fixups_version
               U32 (Natural'(32));                    --  starts_offset
               U32 (Imports_Off);
               U32 (Symbols_Off);
               U32 (N_Imp);
               U32 (Natural'(1));                     --  DYLD_CHAINED_IMPORT
               U32 (Natural'(0));                     --  압축 없음
               Pad_To (LE_Off + 32);
               U32 (N_Segs);
               for S in 0 .. N_Segs - 1 loop
                  U32 ((if Has_Data and then S = 2 then Seg_Info - 32
                        else 0));
               end loop;
               if Has_Data then
                  Pad_To (LE_Off + Seg_Info);
                  U32 (Seg_Size);
                  U16 (VM_Page);
                  U16 (2);                            --  DYLD_CHAINED_PTR_64
                  U64 (Data_Off);
                  U32 (Natural'(0));
                  U16 (Data_Pages);
                  for P in 1 .. Data_Pages loop
                     U16 (if P = 1 then 0 else 16#FFFF#);
                  end loop;
               end if;
               Pad_To (LE_Off + Imports_Off);
               declare
                  Name_Off : Natural := 0;
               begin
                  for K in 1 .. N_Imp loop
                     --  lib_ordinal | name_offset << 9
                     U32 (Ordinals (K) + Name_Off * 512);
                     Name_Off := Name_Off + Import_Name (K)'Length + 1;
                  end loop;
               end;
               for K in 1 .. N_Imp loop
                  Text_Bytes (Import_Name (K) & ASCII.NUL);
               end loop;
               Pad_To (Sym_Off);

               --  nlist_64
               for I of Locals loop
                  Defined_Nlist (I, Ext => False);
               end loop;
               --  REFERENCED_DYNAMICALLY
               Nlist (Header_Name, 16#0F#, 1, 16#10#, Base);
               for I of Externals loop
                  Defined_Nlist (I, Ext => True);
               end loop;
               for K in 1 .. N_Imp loop
                  --  N_EXT, n_desc의 상위 바이트가 라이브러리 순번
                  Nlist (Import_Name (K), 16#01#, 0, 256 * Ordinals (K), 0);
               end loop;

               --  간접 심볼 표: __stubs, 그다음 __got
               for Pass in 1 .. 2 loop
                  for K in 1 .. N_Imp loop
                     U32 (Undefined_Index (K));
                  end loop;
               end loop;

               Text_Bytes (To_String (Strings));
               Pad_To (Sig_Off);

               ---------------------------------------------------------
               --  ad-hoc 코드 서명: SuperBlob 하나에 CodeDirectory 하나

               declare
                  Hashes : Unbounded_String;
               begin
                  for Slot in 0 .. Slots - 1 loop
                     declare
                        First : constant Natural := Slot * Hash_Page;
                        Last  : constant Natural :=
                          Natural'Min (Sig_Off, First + Hash_Page) - 1;
                        Page  : String (1 .. Last - First + 1);
                        Hex   : GNAT.SHA256.Message_Digest;
                     begin
                        for K in Page'Range loop
                           Page (K) := Character'Val (Buf (First + K - 1));
                        end loop;
                        Hex := GNAT.SHA256.Digest (Page);
                        for K in 0 .. 31 loop
                           Append (Hashes, Character'Val
                             (Integer'Value
                                ("16#" & Hex (2 * K + 1 .. 2 * K + 2) & "#")));
                        end loop;
                     end;
                  end loop;

                  BE32_Word (16#FADE_0CC0#);           --  CSMAGIC_EMBEDDED
                  BE32 (20 + CD_Len);
                  BE32 (1);
                  BE32 (0);                            --  CSSLOT_CODEDIRECTORY
                  BE32 (20);

                  BE32_Word (16#FADE_0C02#);           --  CODEDIRECTORY
                  BE32 (CD_Len);
                  BE32 (16#0002_0400#);                --  version
                  BE32 (16#0002_0002#);       --  adhoc | linker-signed
                  BE32 (88 + Identifier'Length + 1);   --  hashOffset
                  BE32 (88);                           --  identOffset
                  BE32 (0);                            --  nSpecialSlots
                  BE32 (Slots);
                  BE32 (Sig_Off);                      --  codeLimit
                  U8 (32);                             --  hashSize
                  U8 (2);                              --  SHA-256
                  U8 (0);                              --  platform
                  U8 (12);                             --  log2 pageSize
                  BE32 (0);                            --  spare2
                  BE32 (0);                            --  scatterOffset
                  BE32 (0);                            --  teamOffset
                  BE32 (0);                            --  spare3
                  BE64 (0);                            --  codeLimit64
                  BE64 (0);                            --  execSegBase
                  BE64 (Text_Seg);                     --  execSegLimit
                  BE64 (1);                    --  CS_EXECSEG_MAIN_BINARY
                  Text_Bytes (Identifier & ASCII.NUL);
                  Text_Bytes (To_String (Hashes));
                  Pad_To (Sig_Off + Sig_Size);
               end;
            end;
         end;
      end;

      declare
         use Ada.Streams.Stream_IO;
         F : File_Type;
      begin
         Create (F, Out_File, Path);
         for B of Buf loop
            Byte'Write (Stream (F), B);
         end loop;
         Close (F);
         GNAT.OS_Lib.Set_Executable (Path);
         return True;
      exception
         when others =>
            Diagnostics.Report
              (Diagnostics.Halt, "cannot write '" & Path & "'");
            return False;
      end;
   end Write;

end MachO.Executable;
