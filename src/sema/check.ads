--  의미 분석 (§10.2의 3, 4단계)
--
--  Collect가 선언을 모으고, Analyse가 서브루틴 본문을 검사한다.
--  검사하면서 노드마다 Ty와 Sym을 채운다.
with Ada.Numerics.Big_Numbers.Big_Integers;
with AST;

package Check is

   procedure Collect (Unit : AST.Node_Id);
   procedure Analyse (Unit : AST.Node_Id);

   --  의미 분석을 마친 N_Int_Lit·N_Char_Lit의 값
   function Int_Value (N : AST.Node_Id)
     return Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

   --  N이 서브루틴 본문 끝까지 실행이 이어지지 못하게 하는가 (§2.4)
   function Diverges (N : AST.Node_Id) return Boolean;

end Check;
