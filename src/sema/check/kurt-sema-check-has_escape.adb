separate (Kurt.Sema.Check)
   function Has_Escape (V : Stmt_Vectors.Vector) return Boolean is
   begin
      for I in V.First_Index .. V.Last_Index loop
         declare
            S : constant Stmt_Access := V.Element (I);
         begin
            case S.Kind is
               when S_Break | S_Express => return True;
               when S_Airside_Block =>
                  if Has_Escape (S.A_Stmts) then return True; end if;
               when S_If =>
                  if Has_Escape (S.SI_Then)
                    or else Has_Escape (S.SI_Else)
                  then return True; end if;
               when S_While =>
                  if Has_Escape (S.W_Body)
                    or else Has_Escape (S.W_Then)
                  then return True; end if;
               when S_Extract =>
                  if Has_Escape (S.X_Else) then return True; end if;
               when others => null;
            end case;
         end;
      end loop;
      return False;
   end Has_Escape;
