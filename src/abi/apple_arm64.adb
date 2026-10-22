package body Apple_Arm64 is

   use Calling;

   function Round_Up (N, A : Natural) return Natural is
     ((N + A - 1) / A * A);

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
         if Args (I).Variadic then
            Offset := Round_Up (Offset, 8);
            Locs (I) := (On_Stack, 0, Offset);
            Offset := Offset + 8;
         elsif Next_Reg < 8 then
            Locs (I) := (In_Register, Next_Reg, 0);
            Next_Reg := Next_Reg + 1;
         else
            Offset := Round_Up (Offset, Args (I).Size);
            Locs (I) := (On_Stack, 0, Offset);
            Offset := Offset + Args (I).Size;
         end if;
      end loop;
      Stack_Size := Round_Up (Offset, 16);
   end Lay_Out;

end Apple_Arm64;
