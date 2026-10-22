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
            Locs (I) := (In_Register, Next_Reg, 0);
            Next_Reg := Next_Reg + 1;
         else
            Locs (I) := (On_Stack, 0, Offset);
            Offset := Offset + 8;
         end if;
      end loop;
      Stack_Size := (Offset + 15) / 16 * 16;
   end Lay_Out;

end SysV_AMD64;
