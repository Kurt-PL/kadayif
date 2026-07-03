separate (Kurt.Sema.Check)
   function Subst_Self_T (T, Conc : Type_Access) return Type_Access is
   begin
      if T = null then
         return null;
      end if;
      case T.Kind is
         when T_Named =>
            if SU.To_String (T.Name) = "selftype" then
               return Conc;
            end if;
            return T;
         when T_Ref =>
            return Mk_Ref (T.Sigil, T.R_Volatile, T.R_Store,
                           Subst_Self_T (T.Target, Conc));
         when others =>
            return T;
      end case;
   end Subst_Self_T;
