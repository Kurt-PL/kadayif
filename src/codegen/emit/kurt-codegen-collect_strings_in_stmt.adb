separate (Kurt.Codegen)
   procedure Collect_Strings_In_Stmt
     (S : Stmt_Access; Pool : in out String_Pool)
   is
   begin
      case S.Kind is
         when S_Return =>
            Collect_Strings_In_Expr (S.R_Val, Pool);
         when S_Expr =>
            Collect_Strings_In_Expr (S.E_Val, Pool);
         when S_Airside_Block =>
            for I in S.A_Stmts.First_Index .. S.A_Stmts.Last_Index loop
               Collect_Strings_In_Stmt (S.A_Stmts.Element (I), Pool);
            end loop;
         when S_Let | S_Mut =>
            Collect_Strings_In_Expr (S.L_Init, Pool);
            if S.L_Is_Refut then
               for I in S.L_Else.First_Index .. S.L_Else.Last_Index loop
                  Collect_Strings_In_Stmt (S.L_Else.Element (I), Pool);
               end loop;
            end if;
         when S_Assign =>
            Collect_Strings_In_Expr (S.Asn_Lhs, Pool);
            Collect_Strings_In_Expr (S.Asn_Rhs, Pool);
         when S_While =>
            Collect_Strings_In_Expr (S.W_Cond, Pool);
            for I in S.W_Body.First_Index .. S.W_Body.Last_Index loop
               Collect_Strings_In_Stmt (S.W_Body.Element (I), Pool);
            end loop;
            for I in S.W_Then.First_Index .. S.W_Then.Last_Index loop
               Collect_Strings_In_Stmt (S.W_Then.Element (I), Pool);
            end loop;
         when S_If =>
            Collect_Strings_In_Expr (S.SI_Cond, Pool);
            for I in S.SI_Then.First_Index .. S.SI_Then.Last_Index loop
               Collect_Strings_In_Stmt (S.SI_Then.Element (I), Pool);
            end loop;
            for I in S.SI_Else.First_Index .. S.SI_Else.Last_Index loop
               Collect_Strings_In_Stmt (S.SI_Else.Element (I), Pool);
            end loop;
         when S_Extract =>
            Collect_Strings_In_Expr (S.X_Expr, Pool);
            for I in S.X_Else.First_Index .. S.X_Else.Last_Index loop
               Collect_Strings_In_Stmt (S.X_Else.Element (I), Pool);
            end loop;
         when S_Break =>
            Collect_Strings_In_Expr (S.Brk_Val, Pool);
         when S_Continue | S_Fence | S_Trap | S_Asm =>
            null;
         when S_Express =>
            Collect_Strings_In_Expr (S.Xp_Val, Pool);
      end case;
   end Collect_Strings_In_Stmt;
