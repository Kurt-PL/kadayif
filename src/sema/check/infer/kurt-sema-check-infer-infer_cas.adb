separate (Kurt.Sema.Check.Infer)
   function Infer_CAS return Type_Access is
   begin
            --  §8.7: the target shall be `&atomic T` or `&guard T`;
            --  expected/new are T. The result is verdict.<T, T>.
            declare
               TT : constant Type_Access := Infer (E.CAS_Tgt, null);
               RT : Type_Access := null;   --  referent T
            begin
               if not Is_Ref (TT)
                 or else TT.R_Store not in RS_Atomic | RS_Guard
               then
                  Error ("compare-and-swap target shall be '&atomic T' "
                         & "or '&guard T', got '" & Image (TT)
                         & "' (spec 8.7)");
               elsif not Is_Unsigned_Int_Type (TT.Target) then
                  --  §8.5.2 via §8.7: the referent shall be an unsigned
                  --  integer type.
                  Error ("compare-and-swap referent shall be an "
                         & "unsigned integer type, got '"
                         & Image (TT.Target) & "' (spec 8.7, 8.5.2)");
               else
                  RT := TT.Target;
               end if;

               declare
                  ET : constant Type_Access := Infer (E.CAS_Exp, RT);
                  NT : constant Type_Access := Infer (E.CAS_New, RT);
               begin
                  if RT /= null then
                     if not Assignable (RT, ET) then
                        Error ("CAS expected operand: expected '"
                               & Image (RT) & "' but got '"
                               & Image (ET) & "'");
                     end if;
                     if not Assignable (RT, NT) then
                        Error ("CAS new operand: expected '"
                               & Image (RT) & "' but got '"
                               & Image (NT) & "'");
                     end if;
                  end if;
               end;

               --  §4.5/§8.7 result type is the intrinsic verdict.<T, T>
               --  (T the referent type) — built directly, no instantiation.
               if RT /= null then
                  declare
                     V : constant Type_Access :=
                       new AST_Type (Kind => T_Named);
                  begin
                     V.Name := SU.To_Unbounded_String ("verdict");
                     V.Args.Append (RT);
                     V.Args.Append (RT);
                     E.Sem_Ty := V;
                  end;
               else
                  E.Sem_Ty := null;
               end if;
               return E.Sem_Ty;
            end;

   end Infer_CAS;
