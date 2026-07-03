separate (Kurt.Sema.Check)
   function Stmt_Diverges (S : Stmt_Access) return Boolean is
   begin
      if S = null then
         return False;
      end if;
      case S.Kind is
         when S_Trap | S_Return | S_Break | S_Continue | S_Express =>
            return True;
         when S_Expr =>
            --  §7.11: a `-> never` call (its value type is `never`).
            return Is_Never_Ty (S.E_Val.Sem_Ty);
         when S_Airside_Block =>
            return Stmts_Diverge (S.A_Stmts);
         when S_If =>
            return (not S.SI_Else.Is_Empty)
              and then Stmts_Diverge (S.SI_Then)
              and then Stmts_Diverge (S.SI_Else);
         when S_While =>
            --  `loop { ... }` desugars to `while true`; with no escaping
            --  break/express it never transfers control onward.
            return Cond_Is_True (S.W_Cond)
              and then not Has_Escape (S.W_Body);
         when S_Let | S_Mut | S_Assign | S_Fence | S_Extract
            | S_Asm =>
            return False;
      end case;
   end Stmt_Diverges;
