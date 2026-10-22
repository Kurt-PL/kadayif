--  System V AMD64 호출 규약
--
--  INTEGER 분류 인자만 다룬다: rdi, rsi, rdx, rcx, r8, r9, 넘치면 스택에
--  8바이트 칸 하나씩. 가변 인자도 같은 규칙을 따른다.
with Calling;

package SysV_AMD64 is

   type Convention is new Calling.Convention with null record;

   overriding procedure Lay_Out
     (C          : Convention;
      Args       : Calling.Arg_Array;
      Locs       : out Calling.Location_Array;
      Stack_Size : out Natural);

end SysV_AMD64;
