separate (Kurt.Sema.Check.Check_Stmt)
   procedure Check_Assign is
   begin
            --  §6.7.1/§6.7.2 the left side of an assignment (plain or
            --  compound) shall be a place expression: a binding, a field
            --  access, or a dereference. A value expression here would
            --  otherwise reach an unsupported lvalue path in codegen.
            if S.Asn_Lhs.Kind not in E_Path | E_Field | E_Deref then
               Error ("the left side of an assignment shall be a place "
                      & "expression (a binding, field access, or "
                      & "dereference) (spec 6.7.1)");
            end if;
            if S.Asn_Rhs.Kind = E_Uninit then
               --  §6.1.8: `place = uninit;` — establishes the contained
               --  state without storing a value.
               declare
                  LT : constant Type_Access := Infer (S.Asn_Lhs, null);
               begin
                  Check_Uninit (LT);
                  S.Asn_Rhs.Sem_Ty := LT;
               end;
               return;
            end if;
            declare
               LT : constant Type_Access := Infer (S.Asn_Lhs, null);
               RT : constant Type_Access := Infer (S.Asn_Rhs, LT);
            begin
               --  §8.3: a store through an exclusive reference asserts
               --  exclusivity; flag a provable alias.
               Register_Store (S.Asn_Lhs);
               --  §8.8.2: assigning a `destruct`-typed binding transfers it.
               Maybe_Move (S.Asn_Rhs);
               if not Assignable (LT, RT) then
                  Error ("assignment type mismatch: place is '"
                         & Image (LT) & "' but value is '"
                         & Image (RT) & "'");
               end if;
               --  §5.4: a plain `static` is immutable; stores require
               --  `static mut`.
               if S.Asn_Lhs.Kind = E_Path
                 and then Natural (S.Asn_Lhs.Segments.Length) = 1
               then
                  declare
                     Name : constant String := SU.To_String
                       (S.Asn_Lhs.Segments.Last_Element);
                     M       : Boolean;
                     Mutable : Boolean;
                     Is_Local : Boolean;
                  begin
                     Mutable := Lookup_Scope_Mut (Name, Is_Local);
                     if Is_Local then
                        --  §2.2.1/§5.1: a `let` binding (and an immutable
                        --  parameter) is single-assignment.
                        if not Mutable then
                           Error ("assignment to immutable binding '"
                                  & Name & "' -- declare it `mut` "
                                  & "(spec 2.2.1)");
                        end if;
                     elsif Find_Static_Decl (Name, M) and then not M then
                        Error ("assignment to immutable static '"
                               & Name & "' -- declare it `static "
                               & "mut` (spec 5.4)");
                     else
                        --  §5.3: a `const` is a translation-time value and
                        --  cannot be assigned to.
                        for CI in U.Consts.First_Index ..
                                  U.Consts.Last_Index loop
                           if SU.To_String (U.Consts.Element (CI).Name)
                                = Name
                           then
                              Error ("assignment to `const` '" & Name
                                     & "' (spec 5.3)");
                           end if;
                        end loop;
                     end if;
                  end;
               end if;
               --  §8.1.2: a store through a reference requires store
               --  permission — `$T`, or a `mut`/`atomic`/`guard`
               --  modifier. `&T` and `&raw T` are load-only.
               if S.Asn_Lhs.Kind = E_Deref then
                  declare
                     IT : constant Type_Access :=
                       S.Asn_Lhs.D_Inner.Sem_Ty;
                  begin
                     if Is_Ref (IT)
                       and then IT.Sigil /= R_Excl
                       and then IT.R_Store = RS_None
                     then
                        Error ("store through load-only reference '"
                               & Image (IT) & "' -- a store requires "
                               & "'$', 'mut', 'atomic' or 'guard' "
                               & "(spec 8.1.2)");
                     end if;
                  end;
                  --  §8.5.2 `mut` field requirement for atomic stores: a
                  --  store (including RMW) through an `&atomic`/`&guard`/
                  --  `&mut`/`$` reference derived from a `.field` access
                  --  in a non-exclusive context shall not appear unless
                  --  the field carries the `mut` field modifier (§5.5.1).
                  --  Loads through such a reference are unrestricted, so
                  --  this is enforced at the store, not at reference
                  --  creation. Waived when the containing value is reached
                  --  through an exclusive (`$`) or `&mut` path, or a `mut`
                  --  binding of the containing value.
                  declare
                     Ref : constant Expr_Access := S.Asn_Lhs.D_Inner;
                  begin
                     if Ref.Kind = E_Ref
                       and then Ref.Rf_Sigil /= R_Raw
                       and then Ref.Rf_Place.Kind = E_Field
                       and then (Ref.Rf_Store in RS_Atomic | RS_Guard
                                                | RS_Mut
                                 or else Ref.Rf_Sigil = R_Excl)
                     then
                        declare
                           Recv : constant Expr_Access :=
                             Ref.Rf_Place.F_Recv;
                           RT   : constant Type_Access :=
                             Infer (Recv, null);
                           RTD  : constant Type_Access :=
                             (if Is_Ref (RT) then RT.Target else RT);
                           FN   : constant String :=
                             SU.To_String (Ref.Rf_Place.F_Name);
                           Exclusive_Ctx : Boolean := False;
                        begin
                           if Is_Ref (RT)
                             and then (RT.Sigil = R_Excl
                                       or else RT.R_Store = RS_Mut)
                           then
                              Exclusive_Ctx := True;
                           elsif not Is_Ref (RT)
                             and then Recv.Kind = E_Path
                             and then Natural (Recv.Segments.Length) = 1
                           then
                              declare
                                 Found : Boolean;
                                 Mut   : constant Boolean :=
                                   Lookup_Scope_Mut
                                     (SU.To_String
                                        (Recv.Segments.Last_Element),
                                      Found);
                              begin
                                 Exclusive_Ctx := Found and then Mut;
                              end;
                           end if;
                           if not Exclusive_Ctx
                             and then RTD /= null
                             and then RTD.Kind = T_Named
                             and then Kurt.Layout.Is_Struct
                                        (SU.To_String (RTD.Name))
                             and then not Kurt.Layout.Field_Is_Mut
                                        (SU.To_String (RTD.Name), FN)
                           then
                              Error ("atomic/exclusive store to non-`mut` "
                                     & "field '" & FN & "' requires the "
                                     & "field be declared `mut` "
                                     & "(spec 8.5.2)");
                           end if;
                        end;
                     end if;
                  end;
               end if;
            end;

   end Check_Assign;
