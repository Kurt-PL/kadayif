separate (Kurt.Sema.Check.Check_Stmt)
   procedure Check_If is
   begin
            if S.SI_Is_Let then
               --  §7.3.3 `if let Enum::Variant { binds } = e { } else { }`.
               declare
                  CT : constant Type_Access := Infer (S.SI_Cond, null);
                  EN : constant String :=
                    (if CT /= null and then CT.Kind = T_Named
                     then SU.To_String (CT.Name) else "");
                  VN : constant String :=
                    SU.To_String (S.SI_Let_Pat.Path.Last_Element);
                  Saved : Natural;
               begin
                  if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                     Error ("`if let` requires an enum value; got '"
                            & Image (CT) & "' (spec 7.3.3)");
                     Check_Block (S.SI_Then);
                     Check_Block (S.SI_Else);
                  elsif not Kurt.Layout.Has_Variant (EN, VN) then
                     Error ("enum '" & EN & "' has no variant '" & VN
                            & "' (spec 7.3.3)");
                     Check_Block (S.SI_Then);
                     Check_Block (S.SI_Else);
                  else
                     --  then-block sees the positional payload bindings.
                     Saved := Natural (Scope.Length);
                     for K in 1 .. Natural (S.SI_Let_Pat.Bindings.Length)
                     loop
                        Scope.Append
                          ((Name => S.SI_Let_Pat.Bindings.Element (K),
                            Ty   => Pat_Field_Ty (S.SI_Let_Pat, CT, VN, K), others => <>));
                     end loop;
                     Check_Block (S.SI_Then);
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                     --  else-block binds nothing (§7.3.3).
                     Check_Block (S.SI_Else);
                  end if;
               end;
            elsif S.SI_Is_Contract then
               --  §7 contract-binding `if e -> v | err`.
               declare
                  CT : constant Type_Access := Infer (S.SI_Cond, null);
                  EN : constant String :=
                    (if CT /= null and then CT.Kind = T_Named
                     then SU.To_String (CT.Name) else "");
                  Saved : Natural;
               begin
                  if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
                  then
                     Error ("the `->` form requires a contract value; "
                            & "got '" & Image (CT) & "'");
                     Check_Block (S.SI_Then);
                     Check_Block (S.SI_Else);
                  elsif S.SI_Cond.Kind /= E_Path
                    or else Natural (S.SI_Cond.Segments.Length) /= 1
                  then
                     --  §7.3 bootstrap: the `->` scrutinee must be a
                     --  binding (a place) so the payload can be aliased
                     --  in place. A call/temporary is not yet materialised.
                     Error ("the `if ... -> v` scrutinee must currently be a "
                            & "binding; bind the value first (bootstrap)");
                     Check_Block (S.SI_Then);
                     Check_Block (S.SI_Else);
                  else
                     --  then-block sees the success payload.
                     Saved := Natural (Scope.Length);
                     Scope.Append
                       ((Name => S.SI_Succ_Bind,
                         Ty   => Kurt.Layout.Variant_Field_Type
                                   (CT,
                                    Kurt.Layout.Contract_Success_Variant
                                      (EN), 1), others => <>));
                     Check_Block (S.SI_Then);
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                     --  else-block sees the failure payload (if bound).
                     Saved := Natural (Scope.Length);
                     if SU.Length (S.SI_Fail_Bind) > 0 then
                        Scope.Append
                          ((Name => S.SI_Fail_Bind,
                            Ty   => Kurt.Layout.Variant_Field_Type
                                      (CT,
                                       Kurt.Layout.Contract_Fail_Variant
                                         (EN), 1), others => <>));
                     end if;
                     Check_Block (S.SI_Else);
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                  end if;
               end;
            else
               declare
                  CT : constant Type_Access :=
                    Infer (S.SI_Cond, Mk_Named ("bool"));
                  pragma Unreferenced (CT);
               begin
                  Check_Block (S.SI_Then);
                  Check_Block (S.SI_Else);
               end;
            end if;

   end Check_If;
