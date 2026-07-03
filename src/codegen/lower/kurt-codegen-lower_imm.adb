separate (Kurt.Codegen)
   procedure Lower_Imm
     (F : IO.File_Type; Reg : Natural; V : Long_Long_Integer; Wide : Boolean)
   is
      R     : constant String := (if Wide then "x" else "w") & Img (Reg);
      Lanes : constant Natural := (if Wide then 4 else 2);
      Done  : Boolean := False;
   begin
      if V < 0 then
         raise Program_Error with
           "codegen: negative integer literals not yet supported";
      end if;
      if V = 0 then
         IO.Put_Line (F, "    mov     " & R & ", #0");
         return;
      end if;
      for I in 0 .. Lanes - 1 loop
         declare
            Lane  : constant Long_Long_Integer :=
              (V / (2 ** (16 * I))) mod 16#1_0000#;
            Shift : constant Natural := 16 * I;
         begin
            if Lane /= 0 then
               if not Done then
                  IO.Put_Line (F, "    movz    " & R & ", #" & Img (Lane)
                                  & (if Shift = 0 then ""
                                     else ", lsl #" & Img (Shift)));
                  Done := True;
               else
                  IO.Put_Line (F, "    movk    " & R & ", #" & Img (Lane)
                                  & ", lsl #" & Img (Shift));
               end if;
            end if;
         end;
      end loop;
   end Lower_Imm;
