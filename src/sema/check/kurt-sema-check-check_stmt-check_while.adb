separate (Kurt.Sema.Check.Check_Stmt)
   procedure Check_While is
   begin
            declare
               Has_Label : constant Boolean := SU.Length (S.W_Label) > 0;
               Saved     : Natural := 0;
               Bound_Let : Boolean := False;
            begin
               if S.W_Is_Let then
                  --  §7.5.1 `while let Enum::Variant { binds } = e { }`:
                  --  the body sees the positional payload bindings.
                  declare
                     CT : constant Type_Access := Infer (S.W_Cond, null);
                     EN : constant String :=
                       (if CT /= null and then CT.Kind = T_Named
                        then SU.To_String (CT.Name) else "");
                     VN : constant String :=
                       SU.To_String (S.W_Let_Pat.Path.Last_Element);
                  begin
                     if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                        Error ("`while let` requires an enum value; got '"
                               & Image (CT) & "' (spec 7.5.1)");
                     elsif not Kurt.Layout.Has_Variant (EN, VN) then
                        Error ("enum '" & EN & "' has no variant '" & VN
                               & "' (spec 7.5.1)");
                     else
                        --  §5.10.2 field coverage.
                        Reject_Sub_Patterns (S.W_Let_Pat, "`while let`");
                        Check_Payload_Coverage (S.W_Let_Pat, EN, VN);
                        Saved := Natural (Scope.Length);
                        Bound_Let := True;
                        for K in 1 .. Natural (S.W_Let_Pat.Bindings.Length)
                        loop
                           Scope.Append
                             ((Name => S.W_Let_Pat.Bindings.Element (K),
                               Ty   => Pat_Field_Ty (S.W_Let_Pat, CT, VN, K), others => <>));
                        end loop;
                     end if;
                  end;
               elsif S.W_Is_Contract then
                  --  §7.5.1 `while cond -> v { }`: cond is a contract
                  --  value; v binds the success payload in the body.
                  declare
                     CT : constant Type_Access := Infer (S.W_Cond, null);
                     EN : constant String :=
                       (if CT /= null and then CT.Kind = T_Named
                        then SU.To_String (CT.Name) else "");
                  begin
                     if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
                     then
                        Error ("`while ->` requires a contract value; got '"
                               & Image (CT) & "' (spec 7.5.1)");
                     elsif S.W_Cond.Kind /= E_Path
                       or else Natural (S.W_Cond.Segments.Length) /= 1
                     then
                        --  §7.5.1 bootstrap: the `->` scrutinee must be a
                        --  binding re-read each iteration; a call/temporary
                        --  is not yet materialised.
                        Error ("the `while ... -> v` scrutinee must currently "
                               & "be a binding reassigned in the body "
                               & "(bootstrap)");
                     else
                        Saved := Natural (Scope.Length);
                        Bound_Let := True;
                        Scope.Append
                          ((Name => S.W_Succ_Bind,
                            Ty   => Kurt.Layout.Variant_Field_Type
                                      (CT,
                                       Kurt.Layout.Contract_Success_Variant
                                         (EN), 1), others => <>));
                     end if;
                  end;
               else
                  declare
                     CT : constant Type_Access :=
                       Infer (S.W_Cond, Mk_Named ("bool"));
                  begin
                     --  §7.5.1: the condition of a plain `while` shall
                     --  satisfy `contract` (bool, verdict, or an enum
                     --  `with contract`); a truthy C-style condition is
                     --  a TF.
                     if not Is_Contract_Ty (CT) then
                        Error ("`while` condition must satisfy `contract` "
                               & "(bool, verdict, or an enum `with "
                               & "contract`); got '" & Image (CT)
                               & "' (spec 7.5.1)");
                     end if;
                  end;
               end if;
               In_Loop := In_Loop + 1;
               if Has_Label then
                  --  §7.9 loop label in scope for the body.
                  Label_Stack.Append ((Name => S.W_Label, Is_Block => False));
               end if;
               declare
                  --  §5.2: the body (+ step block) may run zero times, so
                  --  a deferred binding declared OUTSIDE the loop that the
                  --  body assigns can only leave the loop Maybe-init, never
                  --  Init -- reads inside the body still see the body's
                  --  own straight-line flow (Check_Block below runs
                  --  normally, from the current, pre-loop state).
                  Init_Pre : constant Init_Vec.Vector := Init_States;
               begin
                  Check_Block (S.W_Body);
                  Check_Block (S.W_Then);   --  §7.5.3 step block
                  for P of Init_Pre loop
                     if P.State /= St_Init then
                        for J in Init_States.First_Index ..
                                 Init_States.Last_Index
                        loop
                           if SU.To_String (Init_States.Element (J).Name)
                                = SU.To_String (P.Name)
                             and then Init_States.Element (J).State
                                        = St_Init
                           then
                              declare
                                 IB : Init_Bind := Init_States.Element (J);
                              begin
                                 IB.State := St_Maybe;
                                 Init_States.Replace_Element (J, IB);
                              end;
                           end if;
                        end loop;
                     end if;
                  end loop;
               end;
               if Has_Label then
                  Label_Stack.Delete_Last;
               end if;
               In_Loop := In_Loop - 1;
               if Bound_Let then
                  while Natural (Scope.Length) > Saved loop
                     Scope.Delete_Last;
                  end loop;
               end if;
            end;

   end Check_While;
