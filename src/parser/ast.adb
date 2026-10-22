package body AST is

   --  모든 리스트가 이어 붙는 평면 저장소
   Lists : Id_Vectors.Vector;

   function Add (N : Node) return Node_Id is
   begin
      Nodes.Append (N);
      return Node_Id (Nodes.Last_Index);
   end Add;

   function Make_List (Items : Id_Vectors.Vector) return List_Id is
      First : constant Natural := Natural (Lists.Length) + 1;
   begin
      for N of Items loop
         Lists.Append (N);
      end loop;
      return (First, Natural (Items.Length));
   end Make_List;

   function Item (L : List_Id; Index : Positive) return Node_Id is
     (Lists (L.First + Index - 1));

end AST;
