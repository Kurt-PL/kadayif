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
         declare
            A : Arg_Info := Args (I);
            L : Location;
         begin
            --  16바이트를 넘는 집합체는 복사본의 주소로 넘긴다
            if A.Aggregate and then A.Size > 16 then
               L.By_Reference := True;
               A := (Size => 8, Variadic => A.Variadic, Aggregate => False);
            end if;

            if A.Variadic then
               Offset := Round_Up (Offset, 8);
               L.Kind := On_Stack;
               L.Offset := Offset;
               Offset := Offset + Round_Up (Natural'Max (A.Size, 1), 8);
            elsif A.Aggregate then
               --  레지스터 n개, 모자라면 전부 스택으로 (AAPCS64 C.12–C.13)
               L.Count := (A.Size + 7) / 8;
               if Next_Reg + L.Count <= 8 then
                  L.Kind := In_Register;
                  L.Index := Next_Reg;
                  Next_Reg := Next_Reg + L.Count;
               else
                  Next_Reg := 8;
                  Offset := Round_Up (Offset, 8);
                  L.Kind := On_Stack;
                  L.Offset := Offset;
                  Offset := Offset + 8 * L.Count;
               end if;
            elsif Next_Reg < 8 then
               L.Kind := In_Register;
               L.Index := Next_Reg;
               Next_Reg := Next_Reg + 1;
            else
               Offset := Round_Up (Offset, Natural'Max (A.Size, 1));
               L.Kind := On_Stack;
               L.Offset := Offset;
               Offset := Offset + A.Size;
            end if;
            Locs (I) := L;
         end;
      end loop;
      Stack_Size := Round_Up (Offset, 16);
   end Lay_Out;

   overriding procedure Return_Location
     (C         : Convention;
      Size      : Natural;
      Aggregate : Boolean;
      Registers : out Natural;
      Indirect  : out Boolean)
   is
      pragma Unreferenced (C);
   begin
      Indirect := Aggregate and then Size > 16;
      Registers := (if Indirect then 0
                    elsif Aggregate then (Size + 7) / 8
                    elsif Size = 0 then 0 else 1);
   end Return_Location;

end Apple_Arm64;
