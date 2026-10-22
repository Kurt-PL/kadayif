--  선언과 타입 파싱 (§4, §5, §10)
with AST;

package Declarations is

   --  item = { item_decoration, ws }, ( global_item | local_item ) ;
   function Parse_Item return AST.Node_Id;

   --  현재 토큰이 항목을 시작하는가 (블록 안의 local item 판별용)
   function Starts_Item return Boolean;

   function Parse_Type return AST.Node_Id;

   --  single_path (§6.2.1). 타입 문맥이면 세그먼트의 generic_args를
   --  타입으로 읽는다.
   function Parse_Path (In_Type : Boolean) return AST.Node_Id;

end Declarations;
