package body SysV_AMD64 is

   use Calling;

   overriding procedure Lay_Out
     (C          : Convention;
      Args       : Calling.Arg_Array;
      Locs       : out Calling.Location_Array;
      Stack_Size : out Natural)
   is
      pragma Unreferenced (C);
      Next_Reg : Natural := 0;
      Offset   : Natural := 0;
   begin
      for I in Args'Range loop
         if Next_Reg < 6 then
            Locs (I) := (In_Register, Next_Reg, 1, 0, False);
            Next_Reg := Next_Reg + 1;
         else
            Locs (I) := (On_Stack, 0, 1, Offset, False);
            Offset := Offset + 8;
         end if;
      end loop;
      Stack_Size := (Offset + 15) / 16 * 16;
   end Lay_Out;

   --  INTEGER 분류만: 16바이트 이하는 rax(와 rdx), 넘으면 메모리
   overriding procedure Return_Location
     (C         : Convention;
      Size      : Natural;
      Aggregate : Boolean;
      Registers : out Natural;
      Indirect  : out Boolean)
   is
      pragma Unreferenced (C);
   begin
      Indirect := Size > 16;
      Registers := (if Indirect then 0
                    elsif Aggregate then (Size + 7) / 8
                    elsif Size = 0 then 0 else 1);
   end Return_Location;

end SysV_AMD64;
