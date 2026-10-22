--  식 파싱 (§6). 우선순위와 결합은 §6.14를 따른다.
with AST;

package Expressions is

   function Parse_Expression return AST.Node_Id;

end Expressions;
