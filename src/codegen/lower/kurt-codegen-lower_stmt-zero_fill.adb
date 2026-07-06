separate (Kurt.Codegen.Lower_Stmt)
   procedure Zero_Fill (Off : Cell_Count; Sz : Cell_Count) is
      Curr : Cell_Count := Off;
      Rem_Sz : Cell_Count := Sz;
   begin
      while Rem_Sz >= 8 loop
         IO.Put_Line (F, "    str     xzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 8;
         Rem_Sz := Rem_Sz - 8;
      end loop;
      if Rem_Sz >= 4 then
         IO.Put_Line (F, "    str     wzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 4;
         Rem_Sz := Rem_Sz - 4;
      end if;
      if Rem_Sz >= 2 then
         IO.Put_Line (F, "    strh    wzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 2;
         Rem_Sz := Rem_Sz - 2;
      end if;
      if Rem_Sz >= 1 then
         IO.Put_Line (F, "    strb    wzr, [x29, #" & Img (Curr) & "]");
      end if;
   end Zero_Fill;
