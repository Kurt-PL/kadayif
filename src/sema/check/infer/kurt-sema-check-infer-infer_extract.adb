separate (Kurt.Sema.Check.Infer)
   function Infer_Extract return Type_Access is
   begin
            --  §7.2.3: `contract e else [.id] fallback`. e shall satisfy
            --  `contract`; the expression's type is e's success payload
            --  type regardless of `fallback` (fallback only ever supplies
            --  a value on the path where e fails).
            declare
               IT : constant Type_Access := Infer (E.Ex_Inner, null);
               EN : constant String :=
                 (if IT /= null and then IT.Kind = T_Named
                  then SU.To_String (IT.Name) else "");
            begin
               if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN) then
                  Error ("`contract` operand must satisfy `contract`, got '"
                         & Image (IT) & "' (spec 7.2.3)");
                  E.Sem_Ty := IT;
                  return E.Sem_Ty;
               end if;
               declare
                  Succ_Ty : constant Type_Access :=
                    Kurt.Layout.Variant_Field_Type
                      (IT, Kurt.Layout.Contract_Success_Variant (EN), 1);
                  Fail_Ty : constant Type_Access :=
                    Kurt.Layout.Variant_Field_Type
                      (IT, Kurt.Layout.Contract_Fail_Variant (EN), 1);
                  Saved : constant Natural := Natural (Scope.Length);
               begin
                  --  §7.2.3: `.id` binds the failure payload, in scope only
                  --  within `fallback`.
                  if SU.Length (E.Ex_Err) > 0 then
                     Scope.Append
                       ((Name => E.Ex_Err, Ty => Fail_Ty, others => <>));
                  end if;
                  declare
                     FT : constant Type_Access :=
                       Infer (E.Ex_Fallback, Succ_Ty);
                  begin
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                     --  §7.2.3: `fallback` shall diverge, or its type shall
                     --  be assignment-compatible with the success payload.
                     if not Is_Never_Ty (FT)
                       and then not Assignable (Succ_Ty, FT)
                     then
                        Error ("the fallback of `contract ... else` must "
                               & "diverge or yield a value assignable to "
                               & "the success payload type '"
                               & Image (Succ_Ty) & "'; got '" & Image (FT)
                               & "' (spec 7.2.3)");
                     end if;
                  end;
               end;
               E.Sem_Ty := Kurt.Layout.Variant_Field_Type
                 (IT, Kurt.Layout.Contract_Success_Variant (EN), 1);
               return E.Sem_Ty;
            end;

   end Infer_Extract;
