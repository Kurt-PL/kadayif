--  블록, 문, 제어 흐름 파싱 (§7)
with AST;

package Statements is

   --  block = '{', ws, { block_item, ws }, '}' ;  (§7.1)
   function Parse_Block return AST.Node_Id;

   --  제어 식. 식의 앞머리에서 Expressions가 부른다.
   --  Ends_With_Block은 결과가 block_expression으로 끝났는지, 곧
   --  문 위치에서 ';' 없이 문을 끝낼 수 있는지를 알려 준다.
   function Parse_Control (Ends_With_Block : out Boolean)
                           return AST.Node_Id;

   --  현재 토큰이 Parse_Control이 받는 제어 식을 시작하는가
   function Starts_Control return Boolean;

end Statements;
