with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded;
with Interfaces;

package body MachO is

   use Ada.Strings.Unbounded;
   use Interfaces;
   use Sections;

   --  <mach-o/loader.h>, <mach-o/nlist.h>, <mach-o/arm64/reloc.h>
   MH_MAGIC_64       : constant := 16#FEED_FACF#;
   CPU_TYPE_ARM64    : constant := 16#0100_000C#;
   MH_OBJECT         : constant := 1;
   LC_SEGMENT_64     : constant := 16#19#;
   LC_SYMTAB         : constant := 16#2#;
   LC_DYSYMTAB       : constant := 16#B#;
   LC_BUILD_VERSION  : constant := 16#32#;
   PLATFORM_MACOS    : constant := 1;
   MACOS_15          : constant := 16#000F_0000#;
   S_ATTR_CODE       : constant := 16#8000_0400#;
   N_EXT             : constant := 16#01#;
   N_SECT            : constant := 16#0E#;

   Header_Size  : constant := 32;
   Segment_Size : constant := 72;
   Section_Size : constant := 80;
   Build_Size   : constant := 24;
   Symtab_Size  : constant := 24;
   Dysymtab_Size : constant := 80;

   function Reloc_Type (K : Reloc_Kind) return Unsigned_32 is
     (case K is
        when Branch26   => 2,
        when Page21     => 3,
        when Page_Off12 => 4);

   function Align (N, A : Natural) return Natural is ((N + A - 1) / A * A);

   function Write_Object (Obj : Sections.Object; Path : String)
                          return Boolean
   is
      Out_Bytes : Byte_Vectors.Vector;

      procedure U8 (V : Natural) is
      begin
         Out_Bytes.Append (Byte (V));
      end U8;

      procedure U32 (V : Unsigned_32) is
      begin
         for K in 0 .. 3 loop
            Out_Bytes.Append (Byte (Shift_Right (V, 8 * K) and 16#FF#));
         end loop;
      end U32;

      procedure U32 (V : Natural) is
      begin
         U32 (Unsigned_32 (V));
      end U32;

      procedure U64 (V : Natural) is
      begin
         U32 (V);
         U32 (Natural'(0));
      end U64;

      procedure Name16 (S : String) is
      begin
         for K in 1 .. 16 loop
            U8 (if K <= S'Length then Character'Pos (S (S'First + K - 1))
                else 0);
         end loop;
      end Name16;

      procedure Pad_To (N : Natural) is
      begin
         while Natural (Out_Bytes.Length) < N loop
            U8 (0);
         end loop;
      end Pad_To;

      Text_Bytes  : constant Natural := Size (Obj, Text);
      Const_Bytes : constant Natural := Size (Obj, Const);

      --  심볼 순서: 지역, 정의된 외부, 정의되지 않은 외부
      --  (LC_DYSYMTAB이 이 세 묶음을 요구한다)
      type Group is (Local, External, Undefined);
      function Group_Of (S : Sections.Symbol) return Group is
        (if not S.Defined then Undefined
         elsif S.Global then External else Local);

      Order : array (1 .. Natural (Obj.Symbols.Length)) of Positive;
      Index : array (1 .. Natural (Obj.Symbols.Length)) of Natural;
      Count : array (Group) of Natural := [others => 0];
      Next  : Natural := 0;

      Strings : Unbounded_String := To_Unbounded_String ([1 => ASCII.NUL]);

      --  섹션 주소: __text는 0, __const는 그 뒤
      Const_Addr : constant Natural := Align (Text_Bytes, 8);
      Load_Cmds  : constant Natural :=
        Segment_Size + 2 * Section_Size + Build_Size + Symtab_Size
        + Dysymtab_Size;
      Text_Off   : constant Natural := Align (Header_Size + Load_Cmds, 8);
      Const_Off  : constant Natural := Text_Off + Const_Addr;
      Data_End   : constant Natural := Const_Off + Const_Bytes;

      Text_Relocs, Const_Relocs : Natural := 0;
   begin
      for R of Obj.Relocs loop
         if R.Section = Text then
            Text_Relocs := Text_Relocs + 1;
         else
            Const_Relocs := Const_Relocs + 1;
         end if;
      end loop;

      for G in Group loop
         for I in Obj.Symbols.First_Index .. Obj.Symbols.Last_Index loop
            if Group_Of (Obj.Symbols (I)) = G then
               Next := Next + 1;
               Order (Next) := I;
               Index (I) := Next - 1;
               Count (G) := Count (G) + 1;
            end if;
         end loop;
      end loop;

      declare
         Reloc_Off : constant Natural := Align (Data_End, 8);
         Sym_Off   : constant Natural :=
           Reloc_Off + 8 * (Text_Relocs + Const_Relocs);
         Str_Off   : constant Natural := Sym_Off + 16 * Order'Length;
         Str_Index : array (Order'Range) of Natural;
      begin
         for K in Order'Range loop
            Str_Index (K) := Length (Strings);
            Append (Strings, To_String (Obj.Symbols (Order (K)).Name)
                    & ASCII.NUL);
         end loop;
         while Length (Strings) mod 8 /= 0 loop
            Append (Strings, ASCII.NUL);
         end loop;

         --  mach_header_64
         U32 (Unsigned_32'(MH_MAGIC_64));
         U32 (Unsigned_32'(CPU_TYPE_ARM64));
         U32 (Natural'(0));
         U32 (Natural'(MH_OBJECT));
         U32 (Natural'(4));  --  로드 명령 수
         U32 (Load_Cmds);
         U32 (Natural'(0));
         U32 (Natural'(0));

         --  LC_SEGMENT_64: 이름 없는 세그먼트 하나에 섹션 둘
         U32 (Natural'(LC_SEGMENT_64));
         U32 (Natural'(Segment_Size + 2 * Section_Size));
         Name16 ("");
         U64 (0);
         U64 (Const_Addr + Const_Bytes);
         U64 (Text_Off);
         U64 (Const_Addr + Const_Bytes);
         U32 (Natural'(7));
         U32 (Natural'(7));
         U32 (Natural'(2));
         U32 (Natural'(0));

         --  section_64 __text
         Name16 ("__text");
         Name16 ("__TEXT");
         U64 (0);
         U64 (Text_Bytes);
         U32 (Text_Off);
         U32 (Natural'(2));
         U32 ((if Text_Relocs > 0 then Reloc_Off else 0));
         U32 (Text_Relocs);
         U32 (Unsigned_32'(S_ATTR_CODE));
         U32 (Natural'(0));
         U32 (Natural'(0));
         U32 (Natural'(0));

         --  section_64 __const
         Name16 ("__const");
         Name16 ("__TEXT");
         U64 (Const_Addr);
         U64 (Const_Bytes);
         U32 (Const_Off);
         U32 (Natural'(0));
         U32 ((if Const_Relocs > 0 then Reloc_Off + 8 * Text_Relocs
               else 0));
         U32 (Const_Relocs);
         U32 (Natural'(0));
         U32 (Natural'(0));
         U32 (Natural'(0));
         U32 (Natural'(0));

         --  LC_BUILD_VERSION
         U32 (Natural'(LC_BUILD_VERSION));
         U32 (Natural'(Build_Size));
         U32 (Natural'(PLATFORM_MACOS));
         U32 (Natural'(MACOS_15));
         U32 (Natural'(MACOS_15));
         U32 (Natural'(0));

         --  LC_SYMTAB
         U32 (Natural'(LC_SYMTAB));
         U32 (Natural'(Symtab_Size));
         U32 (Sym_Off);
         U32 (Natural'(Order'Length));
         U32 (Str_Off);
         U32 (Length (Strings));

         --  LC_DYSYMTAB
         U32 (Natural'(LC_DYSYMTAB));
         U32 (Natural'(Dysymtab_Size));
         U32 (Natural'(0));
         U32 (Count (Local));
         U32 (Count (Local));
         U32 (Count (External));
         U32 (Count (Local) + Count (External));
         U32 (Count (Undefined));
         for K in 1 .. 12 loop
            U32 (Natural'(0));
         end loop;

         --  섹션 내용
         Pad_To (Text_Off);
         for B of Obj.Contents (Text) loop
            Out_Bytes.Append (B);
         end loop;
         Pad_To (Const_Off);
         for B of Obj.Contents (Const) loop
            Out_Bytes.Append (B);
         end loop;

         --  재배치: r_address, 그리고 symbolnum:24 pcrel:1 length:2
         --  extern:1 type:4
         Pad_To (Reloc_Off);
         for S in Section_Kind loop
            for R of Obj.Relocs loop
               if R.Section = S then
                  U32 (R.Offset);
                  U32 (Unsigned_32 (Index (R.Target))
                       or (if R.Kind = Page_Off12 then 0
                           else Shift_Left (1, 24))
                       or Shift_Left (2, 25)
                       or Shift_Left (1, 27)
                       or Shift_Left (Reloc_Type (R.Kind), 28));
               end if;
            end loop;
         end loop;

         --  nlist_64
         for K in Order'Range loop
            declare
               S : constant Sections.Symbol := Obj.Symbols (Order (K));
            begin
               U32 (Str_Index (K));
               if S.Defined then
                  U8 (N_SECT + (if S.Global then N_EXT else 0));
                  U8 (if S.Section = Text then 1 else 2);
                  U8 (0);
                  U8 (0);
                  U64 (S.Offset + (if S.Section = Const then Const_Addr
                                   else 0));
               else
                  U8 (N_EXT);
                  U8 (0);
                  U8 (0);
                  U8 (0);
                  U64 (0);
               end if;
            end;
         end loop;

         for C of To_String (Strings) loop
            U8 (Character'Pos (C));
         end loop;
      end;

      declare
         use Ada.Streams.Stream_IO;
         F : File_Type;
      begin
         Create (F, Out_File, Path);
         for B of Out_Bytes loop
            Byte'Write (Stream (F), B);
         end loop;
         Close (F);
         return True;
      exception
         when others =>
            return False;
      end;
   end Write_Object;

end MachO;
