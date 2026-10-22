--  파서 진입점과 공용 상태
--
--  Declarations, Statements, Expressions가 이 커서를 함께 쓴다.
--  구문 오류는 진단을 낸 뒤 Syntax_Error로 항목 단위까지 되감는다.
with AST;
with Idents;
with Source_Map;
with Strip;
with Tokens;

package Parser is

   --  source_unit = ws, { item, ws } ;  (§10.1)
   function Parse (S : Strip.Stripped) return AST.Node_Id;

   Syntax_Error : exception;

   function Peek (Ahead : Natural := 0) return Tokens.Token_Kind;
   function Current return Tokens.Token;
   procedure Advance;

   --  현재 토큰이 K면 넘기고 True
   function Skip (K : Tokens.Token_Kind) return Boolean;
   procedure Expect (K : Tokens.Token_Kind);

   function Here return Source_Map.Source_Pos;
   function Current_Text return String;

   --  식별자를 기대하고 넘긴다
   function Take_Ident return Idents.Ident;

   --  현재 위치에서 오류를 보고하고 Syntax_Error를 던진다
   procedure Fail (Message : String) with No_Return;
   procedure Unimplemented (What : String) with No_Return;

   function Source return Strip.Stripped;

   --  위치만 채운 노드
   function Fresh (Kind : AST.Node_Kind) return AST.Node;

end Parser;
