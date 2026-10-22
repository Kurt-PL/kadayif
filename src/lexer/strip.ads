--  lexical strip scanner (§3.2.1): 주석과 비활성 flag 영역을 걷어 내고,
--  남은 문자 각각이 원본 소스의 어디서 왔는지 기록한다.
with Source_Map;

package Strip is

   type Origin_Array is array (Positive range <>) of Positive;
   type Origin_Access is access constant Origin_Array;
   type Text_Access is access constant String;

   type Stripped is record
      Source : Source_Map.Source_Id;
      Text   : Text_Access;    --  살아남은 문자열 (Text'First = 1)
      Origin : Origin_Access;  --  Origin (I) = Text (I)의 원본 오프셋
   end record;

   function Run (Id : Source_Map.Source_Id) return Stripped;

   --  Text (Index)의 원본 위치
   function Position
     (S : Stripped; Index : Positive) return Source_Map.Source_Pos;

   function Is_Ident_Start (C : Character) return Boolean is
     (C in 'A' .. 'Z' | 'a' .. 'z' | '_');
   function Is_Ident_Char (C : Character) return Boolean is
     (Is_Ident_Start (C) or else C in '0' .. '9');
   function Is_Hex (C : Character) return Boolean is
     (C in '0' .. '9' | 'a' .. 'f' | 'A' .. 'F');

   --  UTF-8 선행 바이트로 문자 하나의 바이트 수
   function Char_Length (C : Character) return Positive;

   --  S (I)가 아포스트로피일 때 문자 리터럴(§3.5.3)이 성립하면
   --  닫는 아포스트로피의 인덱스, 아니면 0
   function Char_Literal_End (S : String; I : Positive) return Natural;

   --  \xH 이스케이프의 자릿수: ⌈B_a / 4⌉ (§3.5.6). 셀 폭 8비트 가정.
   Hex_Escape_Digits : constant := 2;

end Strip;
