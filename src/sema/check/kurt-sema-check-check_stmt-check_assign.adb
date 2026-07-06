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
            --  §8.1.4 `.ptr`/`.len` storability. An array VALUE's fat-
            --  reference view is a projection -- computed from the value's
            --  own storage/extent, not a stored field -- so it is never a
            --  modifiable place, in any region. A reference to an array
            --  (`&[T]` or `&[T; N]`, which materialize the same stored
            --  representation, spec 8.1.4) is different: `.ptr`/`.len` are
            --  then fields of that stored fat reference, storable subject
            --  to the enclosing binding's own mutability -- landside only
            --  through a `mut`-bound reference; `airside` additionally
            --  permits it through a `let`-bound one (the storability
            --  matrix). A receiver reached through anything other than a
            --  simple local/parameter binding is conservatively treated
            --  like a `let` (airside-only) -- no reborrow-tree tracking.
            if S.Asn_Lhs.Kind = E_Field
              and then (SU.To_String (S.Asn_Lhs.F_Name) = "ptr"
                        or else SU.To_String (S.Asn_Lhs.F_Name) = "len")
            then
               declare
                  RT : constant Type_Access :=
                    Infer (S.Asn_Lhs.F_Recv, null);
               begin
                  if RT /= null and then RT.Kind = T_Array then
                     Error ("'." & SU.To_String (S.Asn_Lhs.F_Name)
                            & "' of an array value is a projection, not "
                            & "a modifiable place expression -- storing "
                            & "to it is always a translation failure "
                            & "(spec 8.1.4)");
                  elsif Is_Ref (RT) and then RT.Target /= null
                    and then RT.Target.Kind = T_Array
                  then
                     declare
                        Recv_Found : Boolean := False;
                        Recv_Mut   : Boolean := False;
                     begin
                        if S.Asn_Lhs.F_Recv.Kind = E_Path
                          and then Natural
                                     (S.Asn_Lhs.F_Recv.Segments.Length) = 1
                        then
                           Recv_Mut := Lookup_Scope_Mut
                             (SU.To_String
                                (S.Asn_Lhs.F_Recv.Segments.Last_Element),
                              Recv_Found);
                        end if;
                        if not (Recv_Found and then Recv_Mut)
                          and then In_Airside = 0
                        then
                           Error ("store to '."
                                  & SU.To_String (S.Asn_Lhs.F_Name)
                                  & "' of a `let`-bound array reference "
                                  & "requires an `airside` region (or "
                                  & "declare the binding `mut`) "
                                  & "(spec 8.1.4)");
                        end if;
                     end;
                  end if;
               end;
            end if;
            if S.Asn_Rhs.Kind = E_Uninit then
               --  §6.1.8: `place = uninit;` — establishes the contained
               --  state without storing a value.
               Suppress_Init_Read := True;
               declare
                  LT : constant Type_Access := Infer (S.Asn_Lhs, null);
               begin
                  Suppress_Init_Read := False;
                  Check_Uninit (LT);
                  S.Asn_Rhs.Sem_Ty := LT;
               end;
               --  §5.2/§6.1.8: the assignment (even of `uninit`) establishes
               --  the initialization determination for a deferred binding.
               if S.Asn_Lhs.Kind = E_Path
                 and then Natural (S.Asn_Lhs.Segments.Length) = 1
               then
                  declare
                     Idx : Natural;
                  begin
                     if Init_Lookup
                       (SU.To_String (S.Asn_Lhs.Segments.Last_Element), Idx)
                     then
                        declare
                           IB : Init_Bind := Init_States.Element (Idx);
                        begin
                           IB.State := St_Init;
                           Init_States.Replace_Element (Idx, IB);
                        end;
                     end if;
                  end;
               end if;
               return;
            end if;
            declare
               LT : Type_Access;
               RT : Type_Access;
            begin
               Suppress_Init_Read := True;
               LT := Infer (S.Asn_Lhs, null);
               Suppress_Init_Read := False;
               RT := Infer (S.Asn_Rhs, LT);
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
                     Idx      : Natural;
                     Deferred : Boolean;
                  begin
                     Mutable  := Lookup_Scope_Mut (Name, Is_Local);
                     Deferred := Init_Lookup (Name, Idx);
                     if Is_Local then
                        --  §2.2.1/§5.1: a `let` binding (and an immutable
                        --  parameter) is single-assignment. §5.2: a
                        --  deferred `let x: T;` gets exactly one legal
                        --  assignment -- its (only) initialization -- once
                        --  Init_Lookup shows it still Uninit; any further
                        --  assignment (Maybe or Init already) is the same
                        --  single-assignment violation, just diagnosed
                        --  precisely.
                        if not Mutable then
                           if Deferred
                             and then Init_States.Element (Idx).State
                                        = St_Uninit
                           then
                              null;
                           elsif Deferred then
                              Error ("assignment to '" & Name
                                     & "': a `let` binding may be assigned "
                                     & "at most once over its lifetime "
                                     & "(spec 5.2)");
                           else
                              Error ("assignment to immutable binding '"
                                     & Name & "' -- declare it `mut` "
                                     & "(spec 2.2.1)");
                           end if;
                        end if;
                        --  §5.2: this assignment establishes the whole
                        --  object's initialization determination.
                        if Deferred then
                           declare
                              IB : Init_Bind := Init_States.Element (Idx);
                           begin
                              IB.State := St_Init;
                              Init_States.Replace_Element (Idx, IB);
                           end;
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
               --  §5.3: a field write whose place chain roots in a `const`
               --  (a unit-level or associated const — either way sema
               --  resolved the path to its translation-time value, so
               --  there is no assignable object). Walk the E_Field chain
               --  to its root and reject a const root.
               if S.Asn_Lhs.Kind = E_Field then
                  declare
                     Root : Expr_Access := S.Asn_Lhs;
                  begin
                     while Root /= null and then Root.Kind = E_Field loop
                        Root := Root.F_Recv;
                     end loop;
                     if Root /= null and then Root.Kind = E_Path
                       and then Root.P_Assoc_Val /= null
                     then
                        Error ("assignment to a field of `const` '"
                               & SU.To_String (Root.Segments.Last_Element)
                               & "' (spec 5.3)");
                     end if;
                     --  §5.5.1: a field store through a simple local
                     --  binding of the struct VALUE itself (not through a
                     --  reference — `self`/`&mut`/`$` places are governed
                     --  by the reference's own store permission, checked
                     --  separately below) follows the binding's
                     --  mutability; a `mut` field additionally always
                     --  permits the store in `airside`.
                     if Root /= null and then Root.Kind = E_Path
                       and then Natural (Root.Segments.Length) = 1
                       and then Root.P_Assoc_Val = null
                     then
                        declare
                           RName : constant String :=
                             SU.To_String (Root.Segments.Last_Element);
                           RTy   : constant Type_Access :=
                             Lookup_Scope (RName);
                        begin
                           if RTy /= null and then not Is_Ref (RTy) then
                              declare
                                 Recv   : constant Expr_Access :=
                                   S.Asn_Lhs.F_Recv;
                                 RcvTy  : constant Type_Access :=
                                   Infer (Recv, null);
                                 RcvTyD : constant Type_Access :=
                                   (if Is_Ref (RcvTy) then RcvTy.Target
                                    else RcvTy);
                                 FN     : constant String :=
                                   SU.To_String (S.Asn_Lhs.F_Name);
                                 Found     : Boolean;
                                 Bind_Mut  : constant Boolean :=
                                   Lookup_Scope_Mut (RName, Found);
                              begin
                                 if Found and then not Bind_Mut
                                   and then RcvTyD /= null
                                   and then RcvTyD.Kind = T_Named
                                   and then Kurt.Layout.Is_Struct
                                     (SU.To_String (RcvTyD.Name))
                                 then
                                    if Kurt.Layout.Field_Is_Mut
                                      (SU.To_String (RcvTyD.Name), FN)
                                    then
                                       if In_Airside = 0 then
                                          Error ("store to `mut` field '"
                                            & FN & "' through immutable "
                                            & "binding '" & RName
                                            & "' requires an `airside` "
                                            & "region (spec 5.5.1)");
                                       end if;
                                    else
                                       Error ("assignment to field '" & FN
                                         & "' through immutable binding '"
                                         & RName & "' -- declare it `mut` "
                                         & "(spec 5.5.1)");
                                    end if;
                                 end if;
                              end;
                           end if;
                        end;
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
