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
                     Reject_Sub_Patterns (S.SI_Let_Pat, "`if let`");
                     --  §5.10.2 field coverage.
                     Check_Payload_Coverage (S.SI_Let_Pat, EN, VN);
                     --  then-block sees the positional payload bindings.
                     Saved := Natural (Scope.Length);
                     for K in 1 .. Natural (S.SI_Let_Pat.Bindings.Length)
                     loop
                        Scope.Append
                          ((Name => S.SI_Let_Pat.Bindings.Element (K),
                            Ty   => Pat_Field_Ty (S.SI_Let_Pat, CT, VN, K),
                            Is_Mut => Pat_Bind_Is_Mut (S.SI_Let_Pat, K)));
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
               begin
                  --  §7.3: the condition of a plain `if` shall satisfy
                  --  `contract` (bool, verdict, or an enum `with
                  --  contract`); a truthy C-style condition is a TF.
                  if not Is_Contract_Ty (CT) then
                     Error ("`if` condition must satisfy `contract` "
                            & "(bool, verdict, or an enum `with "
                            & "contract`); got '" & Image (CT)
                            & "' (spec 7.3)");
                  end if;
                  --  §8.8.2/§5.2: branch-aware join. Each arm is checked
                  --  from the SAME pre-if snapshot of Moved/Init_States (an
                  --  arm shall not see the other arm's moves/assignments);
                  --  a diverging arm's ending state drops out of the join
                  --  entirely (control never falls through it).
                  declare
                     Init_Pre   : constant Init_Vec.Vector := Init_States;
                     Moved_Pre  : constant Moved_Vec.Vector := Moved;
                     Init_Then  : Init_Vec.Vector;
                     Moved_Then : Moved_Vec.Vector;
                     Then_Diverges : Boolean;
                     Else_Diverges : Boolean;
                  begin
                     Check_Block (S.SI_Then);
                     Init_Then     := Init_States;
                     Moved_Then    := Moved;
                     --  §5.2's own "constant propagation" example: a
                     --  translation-time-false/-true condition makes the
                     --  other arm unreachable, exactly like a diverging
                     --  arm -- it drops out of the join the same way.
                     Then_Diverges := Stmts_Diverge (S.SI_Then)
                       or else Cond_Is_False (S.SI_Cond);
                     Init_States   := Init_Pre;
                     Moved         := Moved_Pre;
                     Check_Block (S.SI_Else);
                     Else_Diverges := Stmts_Diverge (S.SI_Else)
                       or else Cond_Is_True (S.SI_Cond);
                     --  Init_States/Moved currently hold the else-arm's
                     --  result (or the pre-if snapshot, if S.SI_Else is
                     --  empty and never touches either).
                     if Then_Diverges and then Else_Diverges then
                        null;  --  unreachable after; state is moot
                     elsif Then_Diverges then
                        null;  --  post = else-arm's result (already current)
                     elsif Else_Diverges then
                        Init_States := Init_Then;
                        Moved       := Moved_Then;
                     else
                        --  §8.8.2 union: moved in either live arm => moved
                        --  after (the runtime drop flag, already armed
                        --  per-binding, settles the actual conditional
                        --  destruction).
                        for M of Moved_Then loop
                           if not Is_Moved (SU.To_String (M.Name)) then
                              Moved.Append (M);
                           end if;
                        end loop;
                        --  §5.2 join: a name the if pre-dates keeps Init
                        --  only when BOTH arms leave it Init; when both
                        --  arms leave it untouched (still whatever it was
                        --  before the if) it is unchanged; any other
                        --  disagreement is Maybe-init (spec 5.2).
                        for K in Init_Pre.First_Index .. Init_Pre.Last_Index
                        loop
                           declare
                              Nm : constant String :=
                                SU.To_String (Init_Pre.Element (K).Name);
                              Then_St : Init_State :=
                                Init_Pre.Element (K).State;
                              Else_St : Init_State :=
                                Init_Pre.Element (K).State;
                           begin
                              for J of Init_Then loop
                                 if SU.To_String (J.Name) = Nm then
                                    Then_St := J.State;
                                 end if;
                              end loop;
                              for J of Init_States loop
                                 if SU.To_String (J.Name) = Nm then
                                    Else_St := J.State;
                                 end if;
                              end loop;
                              if Then_St /= Else_St then
                                 for J in Init_States.First_Index ..
                                          Init_States.Last_Index
                                 loop
                                    if SU.To_String (Init_States.Element (J).Name)
                                         = Nm
                                    then
                                       declare
                                          IB : Init_Bind :=
                                            Init_States.Element (J);
                                       begin
                                          IB.State := St_Maybe;
                                          Init_States.Replace_Element (J, IB);
                                       end;
                                    end if;
                                 end loop;
                              end if;
                           end;
                        end loop;
                     end if;
                  end;
               end;
            end if;

   end Check_If;
