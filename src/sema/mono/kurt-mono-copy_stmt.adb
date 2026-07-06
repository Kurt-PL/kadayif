separate (Kurt.Mono)
   function Copy_Stmt
     (S      : Stmt_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Access
   is
      function C (X : Expr_Access) return Expr_Access is
        (Copy_Expr (X, Params, Args));
      R : Stmt_Access;
   begin
      if S = null then
         return null;
      end if;
      R := new Stmt_Node (Kind => S.Kind);
      case S.Kind is
         when S_Return =>
            R.R_Val := C (S.R_Val);
         when S_Expr =>
            R.E_Val := C (S.E_Val);
         when S_Airside_Block =>
            R.A_Stmts := Copy_Block (S.A_Stmts, Params, Args);
         when S_Let | S_Mut =>
            R.L_Name        := S.L_Name;
            R.L_Ty          := Subst (S.L_Ty, Params, Args);
            R.L_Init        := C (S.L_Init);
            R.L_Tuple_Names := S.L_Tuple_Names;
            R.L_Is_Refut    := S.L_Is_Refut;
            R.L_Refut_Pat   := S.L_Refut_Pat;
            R.L_Else        := Copy_Block (S.L_Else, Params, Args);
            R.L_Is_Const    := S.L_Is_Const;
         when S_Assign =>
            R.Asn_Lhs := C (S.Asn_Lhs);
            R.Asn_Rhs := C (S.Asn_Rhs);
         when S_While =>
            R.W_Cond  := C (S.W_Cond);
            R.W_Body  := Copy_Block (S.W_Body, Params, Args);
            R.W_Then  := Copy_Block (S.W_Then, Params, Args);
            R.W_Label := S.W_Label;
            R.W_Is_Let  := S.W_Is_Let;
            R.W_Let_Pat := S.W_Let_Pat;
            R.W_Is_Contract := S.W_Is_Contract;
            R.W_Succ_Bind   := S.W_Succ_Bind;
         when S_If =>
            R.SI_Cond        := C (S.SI_Cond);
            R.SI_Then        := Copy_Block (S.SI_Then, Params, Args);
            R.SI_Else        := Copy_Block (S.SI_Else, Params, Args);
            R.SI_Is_Contract := S.SI_Is_Contract;
            R.SI_Succ_Bind   := S.SI_Succ_Bind;
            R.SI_Fail_Bind   := S.SI_Fail_Bind;
            R.SI_Is_Let      := S.SI_Is_Let;
            R.SI_Let_Pat     := S.SI_Let_Pat;
         when S_Break =>
            R.Brk_Val   := C (S.Brk_Val);
            R.Brk_Label := S.Brk_Label;
         when S_Continue =>
            R.Cont_Label := S.Cont_Label;
         when S_Express =>
            R.Xp_Val   := C (S.Xp_Val);
            R.Xp_Label := S.Xp_Label;
         when S_Fence =>
            R.Fn_Guard := S.Fn_Guard;
            R.Fn_Form  := S.Fn_Form;
         when S_Trap =>
            null;   --  §7.10: no fields to copy
         when S_Asm =>
            R.Asm_Body      := S.Asm_Body;   --  §6.11 raw body
            R.Asm_In_Regs   := S.Asm_In_Regs;
            R.Asm_Out_Regs  := S.Asm_Out_Regs;
            R.Asm_Out_Names := S.Asm_Out_Names;
            R.Asm_Clobbers  := S.Asm_Clobbers;
            for I in S.Asm_In_Exprs.First_Index ..
                     S.Asm_In_Exprs.Last_Index loop
               R.Asm_In_Exprs.Append (C (S.Asm_In_Exprs.Element (I)));
            end loop;
      end case;
      return R;
   end Copy_Stmt;
