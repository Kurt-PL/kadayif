--  토큰 종류와 토큰 레코드 (§3.3–§3.7)
package Tokens is

   type Token_Kind is
     (T_EOF,
      T_Ident, T_Int, T_Float, T_Char, T_String, T_Raw_String,
      T_Annotation,

      --  키워드 (§3.4)
      K_Airside, K_And, K_Arbit, K_As, K_Atomic,
      K_Break, K_Cellbits, K_Const, K_Continue, K_Contract,
      K_Copyable, K_Dyn, K_Else, K_Enum, K_Express,
      K_Extern, K_Fn, K_Guard, K_If, K_Impl,
      K_Instruct, K_Integer, K_Let, K_Loop, K_Match,
      K_Module, K_Mut, K_Numeric, K_Or, K_Primitive,
      K_Protocol, K_Pub, K_Return, K_Routes, K_Self,
      K_Selftype, K_Srcroot, K_Static, K_Struct, K_Super,
      K_Then, K_Transact, K_Trap, K_Type, K_Uninit,
      K_Use, K_Variadic, K_Volatile, K_While, K_Wild,
      K_With, K_Xlat, K_Xor,

      --  지시어 (§3.3). flag 지시어는 strip 단계에서 처리된다.
      D_Add, D_Dyn, D_Path, D_Symbol, D_Inline, D_No_Inline,

      --  구두점과 연산자 (§3.7)
      P_Bang, P_Dollar, P_Percent, P_Amp, P_Apos, P_LParen, P_RParen,
      P_Star, P_Plus, P_Comma, P_Minus, P_Dot, P_Slash, P_Colon, P_Semi,
      P_Lt, P_Eq, P_Gt, P_Question, P_At, P_LBracket, P_RBracket,
      P_Caret, P_LBrace, P_Pipe, P_RBrace, P_Tilde,

      P_Ne, P_Percent_Eq, P_Amp_Eq, P_Star_Eq, P_Star_At, P_Star_Pipe,
      P_Plus_Eq, P_Plus_At, P_Plus_Pipe, P_Minus_Eq, P_Arrow,
      P_Minus_Pipe, P_Dot_Dot, P_Slash_Eq, P_Slash_Pipe, P_Colon_Colon,
      P_Shl, P_Le, P_Eq_Eq, P_Ge, P_Shr, P_Caret_Eq, P_Pipe_Eq,

      P_Star_Pipe_Eq, P_Plus_Pipe_Eq, P_Minus_Pipe_Eq, P_Ellipsis,
      P_Dot_Dot_Eq, P_Slash_Pipe_Eq, P_Shl_Eq, P_Shr_Eq, P_Cas);

   subtype Keyword_Kind is Token_Kind range K_Airside .. K_Xor;
   subtype Directive_Kind is Token_Kind range D_Add .. D_No_Inline;
   subtype Punct_Kind is Token_Kind range P_Bang .. P_Cas;

   --  First .. Last는 strip된 텍스트에서의 철자 범위
   type Token is record
      Kind  : Token_Kind := T_EOF;
      First : Positive   := 1;
      Last  : Natural    := 0;
      Raw   : Boolean    := False;  --  i#로 시작하는 raw identifier
   end record;

   --  키워드가 아니면 T_Ident
   function Keyword (S : String) return Token_Kind;

   --  지시어 이름('#' 제외)에 해당하는 종류, 없으면 T_EOF
   function Directive (S : String) return Token_Kind;

   --  구두점의 철자, 그 밖에는 설명
   function Spelling (K : Token_Kind) return String;

end Tokens;
