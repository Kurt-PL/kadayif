--  토큰화 (§3.2 4단계): strip된 문자열 → 토큰열
with Ada.Containers.Vectors;
with Source_Map;
with Strip;
with Tokens;

package Scanner is

   package Token_Vectors is new Ada.Containers.Vectors
     (Positive, Tokens.Token, Tokens."=");

   --  마지막 토큰은 언제나 T_EOF
   function Run (S : Strip.Stripped) return Token_Vectors.Vector;

   function Spelling (S : Strip.Stripped; T : Tokens.Token) return String is
     (S.Text (T.First .. T.Last));

   function Position
     (S : Strip.Stripped; T : Tokens.Token) return Source_Map.Source_Pos is
     (Strip.Position (S, T.First));

   --  문자열·raw 문자열·문자 리터럴의 내용을 이스케이프를 풀어 셀
   --  값의 열(바이트열)로 돌려준다 (§3.5.4–§3.5.6). 리터럴 인코딩은
   --  UTF-8, 셀 폭은 8비트다. 잘못된 이스케이프는 진단한다.
   function Literal_Content (S : Strip.Stripped; T : Tokens.Token)
                             return String;

end Scanner;
