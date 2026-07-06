separate (Kurt.Sema.Check)
   function Has_Escape (V : Stmt_Vectors.Vector) return Boolean is
      --  §7.2.3: a `contract e else fallback` expression whose fallback is
      --  a brace block (`{ ... }`, parsed as a non-airside E_Airside_Blk)
      --  may itself contain a `break`/`express` -- e.g. `let v = contract
      --  e() else { break; };` directly inside a loop body. Only that
      --  block-shaped fallback is looked into; a bare-value or call
      --  fallback cannot syntactically contain a statement at all.
      function Expr_Has_Escape (E : Expr_Access) return Boolean is
        (E /= null and then E.Kind = E_Extract
         and then E.Ex_Fallback /= null
         and then E.Ex_Fallback.Kind = E_Airside_Blk
         and then Has_Escape (E.Ex_Fallback.AB_Stmts));
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
                  --  §7.11: a translation-time-false/-true condition makes
                  --  one arm statically unreachable -- an escape syntactically
                  --  present only in the unreachable arm is not a real
                  --  escape (spec's own canonical `while true { if false
                  --  { break; } ... }` example).
                  if Cond_Is_False (S.SI_Cond) then
                     if Has_Escape (S.SI_Else) then return True; end if;
                  elsif Cond_Is_True (S.SI_Cond) then
                     if Has_Escape (S.SI_Then) then return True; end if;
                  elsif Has_Escape (S.SI_Then)
                    or else Has_Escape (S.SI_Else)
                  then return True; end if;
               when S_While =>
                  if Has_Escape (S.W_Body)
                    or else Has_Escape (S.W_Then)
                  then return True; end if;
               when S_Let | S_Mut =>
                  if Expr_Has_Escape (S.L_Init) then return True; end if;
               when S_Assign =>
                  if Expr_Has_Escape (S.Asn_Rhs) then return True; end if;
               when S_Expr =>
                  if Expr_Has_Escape (S.E_Val) then return True; end if;
               when others => null;
            end case;
         end;
      end loop;
      return False;
   end Has_Escape;
