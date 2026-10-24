--  Apple arm64 호출 규약 (AAPCS64 변형)
--
--  고정 인자는 x0–x7, 넘치면 스택에 자연 정렬로 채운다. 가변 인자는
--  언제나 스택에 8바이트 칸 하나씩 놓는다.
with Calling;

package Apple_Arm64 is

   type Convention is new Calling.Convention with null record;

   overriding procedure Lay_Out
     (C          : Convention;
      Args       : Calling.Arg_Array;
      Locs       : out Calling.Location_Array;
      Stack_Size : out Natural);

   overriding procedure Return_Location
     (C         : Convention;
      Size      : Natural;
      Aggregate : Boolean;
      Registers : out Natural;
      Indirect  : out Boolean);

end Apple_Arm64;
