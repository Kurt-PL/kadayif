separate (Kurt.Sema.Check)
   function Cond_Is_True (E : Expr_Access) return Boolean is
   begin
      if E = null then
         return False;
      end if;
      if E.Kind = E_Bool_Lit then
         return E.Bool_V;
      end if;
      if E.Kind = E_Path and then Natural (E.Segments.Length) = 1 then
         declare
            Nm : constant String :=
              SU.To_String (E.Segments.Last_Element);
         begin
            for I in U.Consts.First_Index .. U.Consts.Last_Index loop
               declare
                  C : Const_Decl renames U.Consts.Element (I);
               begin
                  if SU.To_String (C.Name) = Nm and then C.Ty /= null
                    and then C.Ty.Kind = T_Named
                    and then SU.To_String (C.Ty.Name) = "bool"
                    and then C.Init /= null
                    and then C.Init.Kind = E_Bool_Lit
                  then
                     return C.Init.Bool_V;
                  end if;
               end;
            end loop;
         end;
      end if;
      return False;
   end Cond_Is_True;
