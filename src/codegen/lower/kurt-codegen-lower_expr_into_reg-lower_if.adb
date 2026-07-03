separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_If (E : Expr_Access) is
      FN     : constant String  := SU.To_String (ST.Fn_Name);
      Idx    : constant Natural := ST.If_Idx;
      L_Else : constant String  := "Lelse_" & FN & "_" & Img (Idx);
      L_End  : constant String  := "Lendif_" & FN & "_" & Img (Idx);
      Wt     : constant String  := "w" & Img (Target_Reg);
   begin
      ST.If_Idx := ST.If_Idx + 1;
      Lower_Expr_Into_Reg (F, E.I_Cond, Target_Reg, ST);
      IO.Put_Line (F, "    cbz     " & Wt & ", " & L_Else);
      Lower_Expr_Into_Reg (F, E.I_Then, Target_Reg, ST);
      IO.Put_Line (F, "    b       " & L_End);
      IO.Put_Line (F, L_Else & ":");
      Lower_Expr_Into_Reg (F, E.I_Else, Target_Reg, ST);
      IO.Put_Line (F, L_End & ":");
   end Lower_If;
