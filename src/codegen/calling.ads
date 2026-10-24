--  ABI가 구현할 추상 인터페이스: 인자 배치
package Calling is

   type Location_Kind is (In_Register, On_Stack);

   type Location is record
      Kind   : Location_Kind := In_Register;
      Index  : Natural := 0;  --  첫 인자 레지스터 번호
      Count  : Natural := 1;  --  쓰는 레지스터 수 (집합체)
      Offset : Natural := 0;  --  스택 인자 영역 안의 오프셋
      --  집합체의 복사본 주소를 넘긴다
      By_Reference : Boolean := False;
   end record;

   type Arg_Info is record
      Size      : Natural := 8;       --  셀 수
      Variadic  : Boolean := False;   --  가변 인자 부분
      Aggregate : Boolean := False;   --  레지스터 하나에 담기지 않는 값
   end record;

   type Arg_Array is array (Positive range <>) of Arg_Info;
   type Location_Array is array (Positive range <>) of Location;

   type Convention is abstract tagged null record;

   --  Stack_Size는 스택 인자 영역의 크기(스택 정렬까지 올림)
   procedure Lay_Out
     (C          : Convention;
      Args       : Arg_Array;
      Locs       : out Location_Array;
      Stack_Size : out Natural) is abstract;

   --  반환값: Registers개 레지스터(x0부터)로, 또는 Indirect면 호출자가
   --  준 자리(AArch64: x8)에 쓴다
   procedure Return_Location
     (C         : Convention;
      Size      : Natural;
      Aggregate : Boolean;
      Registers : out Natural;
      Indirect  : out Boolean) is abstract;

end Calling;
