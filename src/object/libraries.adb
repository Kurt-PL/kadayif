with Ada.Directories;
with Ada.Exceptions;
with Ada.Environment_Variables;
with Ada.Streams.Stream_IO;
with Ada.Strings.Fixed;
with Diagnostics;

package body Libraries is

   use Ada.Strings.Unbounded;
   use Interfaces;
   use type Ada.Directories.File_Kind;

   CPU_ARM64 : constant := 16#0100_000C#;

   Malformed : exception;

   function Is_File (Path : String) return Boolean is
     (Ada.Directories.Exists (Path)
      and then Ada.Directories.Kind (Path) = Ada.Directories.Ordinary_File);

   function Is_Dir (Path : String) return Boolean is
     (Ada.Directories.Exists (Path)
      and then Ada.Directories.Kind (Path) = Ada.Directories.Directory);

   function Read_File (Path : String) return String is
      use Ada.Streams.Stream_IO;
      F : File_Type;
   begin
      Open (F, In_File, Path);
      declare
         Data : String (1 .. Natural (Size (F)));
      begin
         String'Read (Stream (F), Data);
         Close (F);
         return Data;
      end;
   end Read_File;

   --  "1.2.12" → 0x0001_020C (xxxx.yy.zz)
   function Parse_Version (S : String) return Unsigned_32 is
      Parts : array (1 .. 3) of Unsigned_32 := [others => 0];
      K     : Positive := 1;
   begin
      for C of S loop
         if C = '.' then
            exit when K = 3;
            K := K + 1;
         elsif C in '0' .. '9' then
            Parts (K) := Parts (K) * 10
              + Unsigned_32 (Character'Pos (C) - Character'Pos ('0'));
         end if;
      end loop;
      return Shift_Left (Parts (1), 16) or Shift_Left (Parts (2) and 255, 8)
        or (Parts (3) and 255);
   end Parse_Version;

   ---------------------------------------------------------------------
   --  텍스트 스텁 (.tbd, tbd-version 4까지의 YAML)

   function Unquote (S : String) return String is
      T : constant String := Ada.Strings.Fixed.Trim (S, Ada.Strings.Both);
   begin
      if T'Length >= 2 and then T (T'First) in ''' | '"' then
         return T (T'First + 1 .. T'Last - 1);
      end if;
      return T;
   end Unquote;

   function Load_Tbd (Path : String; Lib : in out Library) return Boolean is
      Data : constant String := Read_File (Path);

      type Section is (None, Exported, Other);
      Doc        : Natural := 0;
      Current    : Section := None;
      Collecting : Boolean := False;  --  내보내는 심볼 목록 안
      Skipping   : Boolean := False;  --  관심 없는 여러 줄 목록 안

      --  "[ a, b," 같은 조각에서 심볼을 모으고, ']'를 만나면 True
      function Take_Symbols (S : String) return Boolean is
         Token : Unbounded_String;
         Done  : Boolean := False;

         procedure Flush is
         begin
            if Length (Token) > 0 then
               Lib.Exports.Include (Unquote (To_String (Token)));
               Token := Null_Unbounded_String;
            end if;
         end Flush;
      begin
         for C of S loop
            case C is
               when '[' | ' ' | ASCII.HT => Flush;
               when ',' => Flush;
               when ']' =>
                  Flush;
                  Done := True;
               when others => Append (Token, C);
            end case;
         end loop;
         Flush;
         return Done;
      end Take_Symbols;

      procedure Line (Raw : String) is
         use Ada.Strings.Fixed;
         T : constant String := Trim (Raw, Ada.Strings.Both);
      begin
         if T'Length = 0 then
            return;
         elsif Collecting then
            Collecting := not Take_Symbols (T);
            return;
         elsif Skipping then
            Skipping := Index (T, "]") = 0;
            return;
         elsif T'Length >= 3 and then T (T'First .. T'First + 2) = "---"
         then
            Doc := Doc + 1;
            Current := None;
            return;
         elsif T'Length >= 1 and then T (T'First) = '{' then
            raise Malformed with "tbd-version 5 (JSON) stubs";
         end if;

         declare
            Body_Text : constant String :=
              (if T'Length >= 2 and then T (T'First .. T'First + 1) = "- "
               then T (T'First + 2 .. T'Last) else T);
            Colon     : constant Natural := Index (Body_Text, ":");
         begin
            if Colon = 0 then
               return;
            end if;
            declare
               Key   : constant String :=
                 Trim (Body_Text (Body_Text'First .. Colon - 1),
                       Ada.Strings.Both);
               Value : constant String :=
                 Body_Text (Colon + 1 .. Body_Text'Last);
               Top   : constant Boolean :=
                 Raw'Length > 0 and then Raw (Raw'First) /= ' ';
            begin
               if Top then
                  Current := (if Key in "exports" | "reexports" then Exported
                              else Other);
                  if Doc = 1 and then Key = "install-name" then
                     Lib.Install_Name := To_Unbounded_String (Unquote (Value));
                  elsif Doc = 1 and then Key = "current-version" then
                     Lib.Current := Parse_Version (Value);
                  elsif Doc = 1 and then Key = "compatibility-version" then
                     Lib.Compat := Parse_Version (Value);
                  end if;
               end if;
               if Current = Exported
                 and then Key in "symbols" | "weak-symbols"
                               | "thread-local-symbols"
               then
                  Collecting := not Take_Symbols (Value);
               elsif Index (Value, "[") > 0 and then Index (Value, "]") = 0
               then
                  Skipping := True;
               end if;
            end;
         end;
      end Line;

      First : Positive := Data'First;
   begin
      for I in Data'Range loop
         if Data (I) = ASCII.LF then
            Line (Data (First .. I - 1));
            First := I + 1;
         end if;
      end loop;
      if First <= Data'Last then
         Line (Data (First .. Data'Last));
      end if;
      return Length (Lib.Install_Name) > 0;
   end Load_Tbd;

   ---------------------------------------------------------------------
   --  Mach-O 동적 라이브러리

   function Load_Dylib (Path : String; Lib : in out Library) return Boolean is
      Data : constant String := Read_File (Path);

      function B (Off : Natural) return Unsigned_32 is
        (Unsigned_32 (Character'Pos (Data (Data'First + Off))));

      function LE32 (Off : Natural) return Natural is
        (Natural (B (Off) or Shift_Left (B (Off + 1), 8)
                  or Shift_Left (B (Off + 2), 16)
                  or Shift_Left (B (Off + 3) and 16#7F#, 24)));

      function BE32 (Off : Natural) return Unsigned_32 is
        (Shift_Left (B (Off), 24) or Shift_Left (B (Off + 1), 16)
         or Shift_Left (B (Off + 2), 8) or B (Off + 3));

      function C_String (Off : Natural) return String is
         Last : Natural := Off;
      begin
         while Data (Data'First + Last) /= ASCII.NUL loop
            Last := Last + 1;
         end loop;
         return Data (Data'First + Off .. Data'First + Last - 1);
      end C_String;

      Slice : Natural := 0;
      Trie, Trie_Size : Natural := 0;

      function ULEB (P : in out Natural) return Natural is
         V     : Natural := 0;
         Shift : Natural := 0;
      begin
         loop
            declare
               Bt : constant Natural := Natural (B (P));
            begin
               P := P + 1;
               V := V + (Bt mod 128) * 2 ** Shift;
               exit when Bt < 128;
               Shift := Shift + 7;
               if Shift > 28 then
                  raise Malformed with "export trie";
               end if;
            end;
         end loop;
         return V;
      end ULEB;

      procedure Walk (Node : Natural; Prefix : String; Depth : Natural) is
         P        : Natural := Trie + Node;
         Terminal : Natural;
         Children : Natural;
      begin
         if Depth > 256 or else Node >= Trie_Size then
            raise Malformed with "export trie";
         end if;
         Terminal := ULEB (P);
         if Terminal > 0 then
            Lib.Exports.Include (Prefix);
         end if;
         P := P + Terminal;
         Children := Natural (B (P));
         P := P + 1;
         for K in 1 .. Children loop
            declare
               Edge : constant String := C_String (P);
            begin
               P := P + Edge'Length + 1;
               Walk (ULEB (P), Prefix & Edge, Depth + 1);
            end;
         end loop;
      end Walk;

   begin
      if BE32 (0) = 16#CAFE_BABE# then
         --  fat: arm64 조각을 고른다
         for K in 0 .. Natural (BE32 (4)) - 1 loop
            if BE32 (8 + 20 * K) = CPU_ARM64 then
               Slice := Natural (BE32 (8 + 20 * K + 8));
            end if;
         end loop;
      end if;
      --  LE32는 최상위 비트를 버린다: MH_MAGIC_64 = 16#FEED_FACF#
      if LE32 (Slice) /= 16#7EED_FACF#
        or else LE32 (Slice + 4) /= CPU_ARM64
      then
         raise Malformed with "no arm64 Mach-O in the library";
      end if;

      declare
         P : Natural := Slice + 32;
      begin
         for K in 1 .. LE32 (Slice + 16) loop
            declare
               Cmd  : constant Natural := LE32 (P);
               Size : constant Natural := LE32 (P + 4);
            begin
               case Cmd is
                  when 16#D# =>                    --  LC_ID_DYLIB
                     Lib.Install_Name := To_Unbounded_String
                       (C_String (P + LE32 (P + 8)));
                     Lib.Current := Unsigned_32 (LE32 (P + 16));
                     Lib.Compat := Unsigned_32 (LE32 (P + 20));
                  when 16#33# =>                   --  LC_DYLD_EXPORTS_TRIE
                     Trie := Slice + LE32 (P + 8);
                     Trie_Size := LE32 (P + 12);
                  when 16#22# =>                   --  LC_DYLD_INFO(_ONLY)
                     if Trie_Size = 0 then
                        Trie := Slice + LE32 (P + 40);
                        Trie_Size := LE32 (P + 44);
                     end if;
                  when 16#1F# =>                   --  LC_REEXPORT_DYLIB
                     Lib.Partial := True;
                  when others =>
                     null;
               end case;
               P := P + Size;
            end;
         end loop;
      end;
      if Trie_Size > 0 then
         Walk (0, "", 0);
      end if;
      return Length (Lib.Install_Name) > 0;
   end Load_Dylib;

   ---------------------------------------------------------------------
   --  찾기

   function Default_Dirs return String_Vectors.Vector is
      Result : String_Vectors.Vector;
      Env    : constant String :=
        (if Ada.Environment_Variables.Exists ("SDKROOT")
         then Ada.Environment_Variables.Value ("SDKROOT") else "");
      CLT    : constant String :=
        "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk";
      Xcode  : constant String :=
        "/Applications/Xcode.app/Contents/Developer/Platforms/"
        & "MacOSX.platform/Developer/SDKs/MacOSX.sdk";
   begin
      if Env'Length > 0 and then Is_Dir (Env) then
         Result.Append (Env & "/usr/lib");
      elsif Is_Dir (CLT) then
         Result.Append (CLT & "/usr/lib");
      elsif Is_Dir (Xcode) then
         Result.Append (Xcode & "/usr/lib");
      end if;
      Result.Append ("/usr/local/lib");
      return Result;
   end Default_Dirs;

   function Find
     (Name : String;
      Dirs : String_Vectors.Vector;
      Mode : Linkage;
      Lib  : out Library) return Boolean
   is
      All_Dirs : String_Vectors.Vector := Dirs;

      procedure Fail (Message : String) is
      begin
         Diagnostics.Report (Diagnostics.Error, Message);
      end Fail;

   begin
      Lib := (others => <>);
      for D of Default_Dirs loop
         All_Dirs.Append (D);
      end loop;
      for D of All_Dirs loop
         for Kind in 1 .. 5 loop
            declare
               File : constant String :=
                 (case Kind is
                    when 1 => Name & ".dl",
                    when 2 => Name & ".sl",
                    when 3 => "lib" & Name & ".dylib",
                    when 4 => "lib" & Name & ".tbd",
                    when others => "lib" & Name & ".a");
               Path : constant String := D & "/" & File;
            begin
               if (Mode = Dynamic or else Kind in 2 | 5)
                 and then Is_File (Path)
               then
                  Lib.Path := To_Unbounded_String (Path);
                  case Kind is
                     when 1 =>
                        Fail ("unimplemented: Kurt dynamic libraries ("
                              & Path & ", KCSS §4.9)");
                        return False;
                     when 2 =>
                        Fail ("unimplemented: Kurt static libraries ("
                              & Path & ", KCSS §4.9)");
                        return False;
                     when 5 =>
                        Fail ("unimplemented: static system libraries ("
                              & Path & ", KCSS §4.9)");
                        return False;
                     when others =>
                        begin
                           if (if Kind = 3 then Load_Dylib (Path, Lib)
                               else Load_Tbd (Path, Lib))
                           then
                              return True;
                           end if;
                           Fail ("cannot read library '" & Path & "'");
                           return False;
                        exception
                           when Err : Malformed =>
                              Fail ("unimplemented: library '" & Path
                                    & "': "
                                    & Ada.Exceptions.Exception_Message (Err));
                              return False;
                           when others =>
                              Fail ("malformed library '" & Path & "'");
                              return False;
                        end;
                  end case;
               end if;
            end;
         end loop;
      end loop;
      Fail ("library not found for -l " & Name);
      return False;
   end Find;

end Libraries;
