separate (Kurt.Sema.Check)
   procedure Check_Return_Escape (E : Expr_Access) is
   begin
      if E = null then
         return;
      end if;
      case E.Kind is
         when E_Ref =>
            if E.Rf_Sigil /= R_Raw
              and then E.Rf_Place /= null
              and then E.Rf_Place.Kind = E_Path
              and then Natural (E.Rf_Place.Segments.Length) >= 1
            then
               declare
                  Root : constant String :=
                    SU.To_String (E.Rf_Place.Segments.First_Element);
               begin
                  if not Outlives_Call (Root) then
                     Error ("returns a reference to '" & Root
                            & "', which does not outlive the call; its "
                            & "referent escapes its scope (spec 8.4.3)");
                  end if;
               end;
            end if;
         when E_Path =>
            if Natural (E.Segments.Length) = 1 then
               declare
                  Name : constant String :=
                    SU.To_String (E.Segments.Last_Element);
                  N    : constant Kurt.Borrow.Node_Id :=
                    Kurt.Borrow.Of_Binding (Borrows, Name);
               begin
                  --  A tracked local reference: check what it points to.
                  --  No node ⇒ a reference parameter (its referent is the
                  --  caller's, which outlives the call) or an untracked
                  --  chain — conservatively permitted.
                  if N /= Kurt.Borrow.No_Node then
                     declare
                        Ref : constant String :=
                          Kurt.Borrow.Referent_Of (Borrows, N);
                     begin
                        if not Outlives_Call (Ref) then
                           Error ("returns reference '" & Name
                                  & "' pointing to '" & Ref
                                  & "', which does not outlive the call "
                                  & "(spec 8.4.3)");
                        end if;
                     end;
                  end if;
               end;
            end if;
         when E_Cast =>
            --  A reference cast preserves the referent (§6.8.8).
            Check_Return_Escape (E.Cast_Inner);
         when others =>
            null;  --  call results etc.: the callee's signature is
                   --  verified at its own definition.
      end case;
   end Check_Return_Escape;
