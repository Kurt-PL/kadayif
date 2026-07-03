separate (Kurt.Codegen)
   function Type_Of_Expr (E : Expr_Access; ST : Lower_State) return Type_Access
   is
      Idx : Natural;
   begin
      if E = null then
         return null;
      end if;
      if E.Sem_Ty /= null then
         return E.Sem_Ty;
      end if;
      if E.Kind = E_Path and then Natural (E.Segments.Length) = 1 then
         Idx := Find_Binding (ST, SU.To_String (E.Segments.Last_Element));
         if Idx /= 0 then
            return ST.Bindings.Element (Idx).Ty;
         end if;
      end if;
      return null;
   end Type_Of_Expr;
