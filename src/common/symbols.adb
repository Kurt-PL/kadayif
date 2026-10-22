package body Symbols is

   function Add (S : Symbol) return Symbol_Id is
   begin
      Table.Append (S);
      return Symbol_Id (Table.Last_Index);
   end Add;

end Symbols;
