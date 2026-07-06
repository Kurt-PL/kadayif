separate (Kurt.Sema.Check)
   procedure Check_No_Destruct_Load (E : Expr_Access) is
   begin
      if E /= null and then E.Kind = E_Deref
        and then E.D_Inner /= null and then E.D_Inner.Sem_Ty /= null
        and then E.D_Inner.Sem_Ty.Kind = T_Ref
        and then E.D_Inner.Sem_Ty.Sigil /= R_Raw
        and then Satisfies_Destruct (E.Sem_Ty)
      then
         Error ("loading '" & Image (E.Sem_Ty) & "' through a tracked "
                & "reference copies a value satisfying `destruct`; only "
                & "a `&raw` load is permitted (spec 8.9)");
      end if;
   end Check_No_Destruct_Load;
