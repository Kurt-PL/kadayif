--  타깃 독립 c1 구동부: 식 트리 → Instruction_Set 경유 명령열
--
--  c1974의 rcexpr처럼 식을 세 문맥으로 내린다. 값 문맥은 Temp 하나에
--  값을 남기고, 효과 문맥은 값을 버리고, 조건 문맥은 계약의 성패에
--  따라 분기한다. 피연산자는 언제나 앞쪽부터 평가한다 (§2.1.1).
with AST;
with Calling;
with Instruction_Set;

package Emit is

   --  의미 분석을 마친 단위의 어셈블리 텍스트. 번역 한계를 넘으면
   --  진단을 내고, 그때 결과는 쓰지 말아야 한다.
   function Generate
     (Unit       : AST.Node_Id;
      M          : in out Instruction_Set.ISA'Class;
      Convention : Calling.Convention'Class) return String;

end Emit;
