separate (Kurt.Mono.Monomorphize)
   procedure Visit_Stmt (S : Stmt_Access) is
   begin
      case S.Kind is
         when S_Let | S_Mut =>
            Visit_Type (S.L_Ty);
            Visit_Expr (S.L_Init);
         when S_Return =>
            Visit_Expr (S.R_Val);
         when S_Expr =>
            Visit_Expr (S.E_Val);
         when S_Assign =>
            Visit_Expr (S.Asn_Lhs);
            Visit_Expr (S.Asn_Rhs);
         when S_While =>
            Visit_Expr (S.W_Cond);
            Visit_Block (S.W_Body);
            Visit_Block (S.W_Then);
         when S_If =>
            Visit_Expr (S.SI_Cond);
            Visit_Block (S.SI_Then);
            Visit_Block (S.SI_Else);
         when S_Extract =>
            Visit_Expr (S.X_Expr);
            Visit_Block (S.X_Else);
         when S_Airside_Block =>
            Visit_Block (S.A_Stmts);
         when S_Break =>
            Visit_Expr (S.Brk_Val);
         when S_Express =>
            Visit_Expr (S.Xp_Val);
         when S_Continue | S_Fence | S_Trap | S_Asm =>
            null;
      end case;
   end Visit_Stmt;
