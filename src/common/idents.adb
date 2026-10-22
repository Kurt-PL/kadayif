with Ada.Containers.Indefinite_Hashed_Maps;
with Ada.Containers.Indefinite_Vectors;
with Ada.Strings.Hash;

package body Idents is

   package Maps is new Ada.Containers.Indefinite_Hashed_Maps
     (String, Ident, Ada.Strings.Hash, "=");
   package Names is new Ada.Containers.Indefinite_Vectors (Positive, String);

   Table : Maps.Map;
   Spellings : Names.Vector;

   function Intern (S : String) return Ident is
      C : constant Maps.Cursor := Table.Find (S);
   begin
      if Maps.Has_Element (C) then
         return Maps.Element (C);
      end if;
      Spellings.Append (S);
      Table.Insert (S, Ident (Spellings.Last_Index));
      return Ident (Spellings.Last_Index);
   end Intern;

   function Image (Id : Ident) return String is
     (if Id = No_Ident then "" else Spellings (Positive (Id)));

end Idents;
