with Ada.Containers.Vectors;
with Ada.Directories;
with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded;

package body Source_Map is

   use Ada.Strings.Unbounded;

   type String_Access is access String;

   type Entry_Rec is record
      Path : Unbounded_String;
      Text : String_Access;
   end record;

   package Entry_Vectors is new Ada.Containers.Vectors (Positive, Entry_Rec);
   Entries : Entry_Vectors.Vector;

   function Load (Path : String) return Source_Id is
      use Ada.Directories;
      use Ada.Streams.Stream_IO;
      F : File_Type;
   begin
      if not Exists (Path) or else Kind (Path) /= Ordinary_File then
         return No_Source;
      end if;
      declare
         Buf : constant String_Access :=
           new String (1 .. Natural (Size (Path)));
      begin
         Open (F, In_File, Path);
         String'Read (Stream (F), Buf.all);
         Close (F);
         Entries.Append (Entry_Rec'(To_Unbounded_String (Path), Buf));
         return Source_Id (Entries.Last_Index);
      end;
   exception
      when others =>
         if Is_Open (F) then
            Close (F);
         end if;
         return No_Source;
   end Load;

   function Path (Id : Source_Id) return String is
     (To_String (Entries (Positive (Id)).Path));

   function Text (Id : Source_Id) return Text_Access is
     (Text_Access (Entries (Positive (Id)).Text));

   procedure Line_Col (Pos : Source_Pos; Line, Col : out Positive) is
      T    : constant Text_Access := Text (Pos.Source);
      Stop : constant Natural := Natural'Min (Pos.Offset - 1, T'Last);
   begin
      Line := 1;
      Col := 1;
      for I in T'First .. Stop loop
         if T (I) = ASCII.LF then
            Line := Line + 1;
            Col := 1;
         elsif Character'Pos (T (I)) / 16#40# /= 2 then
            --  UTF-8 연속 바이트(10xxxxxx)가 아닌 것만 센다
            Col := Col + 1;
         end if;
      end loop;
   end Line_Col;

end Source_Map;
