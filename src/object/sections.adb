package body Sections is

   use Ada.Strings.Unbounded;
   use Interfaces;

   function Lookup (Obj : in out Object; Name : String) return Positive is
      S : Symbol;
   begin
      for I in Obj.Symbols.First_Index .. Obj.Symbols.Last_Index loop
         if Obj.Symbols (I).Name = Name then
            return I;
         end if;
      end loop;
      S.Name := To_Unbounded_String (Name);
      Obj.Symbols.Append (S);
      return Obj.Symbols.Last_Index;
   end Lookup;

   procedure Define
     (Obj     : in out Object;
      Name    : String;
      Section : Section_Kind;
      Offset  : Natural;
      Global  : Boolean)
   is
      I : constant Positive := Lookup (Obj, Name);
      S : Symbol := Obj.Symbols (I);
   begin
      S.Defined := True;
      S.Section := Section;
      S.Offset := Offset;
      S.Global := Global;
      Obj.Symbols.Replace_Element (I, S);
   end Define;

   procedure Append (Obj : in out Object; Section : Section_Kind; B : Byte) is
   begin
      Obj.Contents (Section).Append (B);
   end Append;

   procedure Append_Word
     (Obj : in out Object; Section : Section_Kind; W : Unsigned_32) is
   begin
      for K in 0 .. 3 loop
         Append (Obj, Section, Byte (Shift_Right (W, 8 * K) and 16#FF#));
      end loop;
   end Append_Word;

end Sections;
