separate (Kurt.Sema.Check)
   procedure Check_Stmt (S : Stmt_Access) is
   begin
      case S.Kind is
         when S_Return =>
            if S.R_Val = null then
               --  §5.1 bare `return;` is well-formed only in a subroutine
               --  whose return type is `void`.
               if Cur_Ret /= null and then not Is_Void_Type (Cur_Ret) then
                  Error ("bare `return;` in a subroutine returning '"
                         & Image (Cur_Ret) & "'; a value is required "
                         & "(spec 5.1)");
               end if;
               return;
            end if;
            declare
               RT : constant Type_Access := Infer (S.R_Val, Cur_Ret);
            begin
               if not Assignable (Cur_Ret, RT) then
                  Error ("return type mismatch: subroutine returns '"
                         & Image (Cur_Ret) & "' but expression is '"
                         & Image (RT) & "'");
               end if;
               --  §8.4.3: a returned landside reference shall not outlive
               --  its referent (no reference to a local / value parameter).
               if Cur_Ret /= null and then Cur_Ret.Kind = T_Ref
                 and then Cur_Ret.Sigil /= R_Raw
               then
                  Check_Return_Escape (S.R_Val);
               end if;
               --  §8.8.2: returning a `destruct`-typed binding transfers it.
               Maybe_Move (S.R_Val);
            end;

         when S_Expr =>
            declare
               ET : constant Type_Access := Infer (S.E_Val, null);
               pragma Unreferenced (ET);
            begin
               null;
            end;

         when S_Let | S_Mut =>
            if S.L_Is_Refut then
               --  §5.2.1 refutable let-else: `let Enum::V { binds } = e
               --  else { diverge };`. On a match the payload binds for the
               --  rest of the enclosing scope; the else block (which sees no
               --  payload binding) runs on mismatch.
               declare
                  CT : constant Type_Access := Infer (S.L_Init, null);
                  EN : constant String :=
                    (if CT /= null and then CT.Kind = T_Named
                     then SU.To_String (CT.Name) else "");
                  VN : constant String :=
                    SU.To_String (S.L_Refut_Pat.Path.Last_Element);
               begin
                  if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                     Error ("refutable `let` requires an enum value; got '"
                            & Image (CT) & "' (spec 5.2.1)");
                  elsif not Kurt.Layout.Has_Variant (EN, VN) then
                     Error ("enum '" & EN & "' has no variant '" & VN
                            & "' (spec 5.2.1)");
                  end if;
                  --  else first (no payload in scope here), then the
                  --  payload bindings persist into the enclosing scope.
                  Check_Block (S.L_Else);
                  if EN /= "" and then Kurt.Layout.Is_Enum (EN)
                    and then Kurt.Layout.Has_Variant (EN, VN)
                  then
                     for K in 1 .. Natural (S.L_Refut_Pat.Bindings.Length)
                     loop
                        Check_Dup_In_Scope
                          (S.L_Refut_Pat.Bindings.Element (K));
                        Scope.Append
                          ((Name => S.L_Refut_Pat.Bindings.Element (K),
                            Ty   => Pat_Field_Ty (S.L_Refut_Pat, CT, VN, K), others => <>));
                     end loop;
                  end if;
               end;
               return;
            end if;
            declare
               Ty : Type_Access := S.L_Ty;
            begin
               --  §4.6: `[T]` cannot be a binding type (use `&[T]`).
               if Is_Unsized_Value (S.L_Ty) then
                  Error ("`[T]`/`dyn Trait` cannot be a binding type "
                         & "(use a reference) (spec 4.6/9.5)");
               end if;
               if S.L_Init /= null and then S.L_Init.Kind = E_Uninit then
                  --  §6.1.8: `let/mut x: T = uninit;` — no value to infer
                  --  from, so the type annotation is required.
                  Check_Uninit (Ty);
                  S.L_Init.Sem_Ty := Ty;
               elsif S.L_Init /= null then
                  declare
                     IT : constant Type_Access := Infer (S.L_Init, Ty);
                  begin
                     if Ty = null then
                        Ty := IT;
                     --  §4.6 `let r: &[T] = &arr;` slice coercion.
                     elsif Is_Slice_Ref (Ty) and then Is_Ref (IT)
                       and then IT.Target /= null
                       and then IT.Target.Kind = T_Array
                       and then IT.Target.Len > 0
                       and then Same_Type (Ty.Target.Elem,
                                           IT.Target.Elem)
                     then
                        declare
                           SC : constant Expr_Access :=
                             new Expr_Node (Kind => E_Slice_Cast);
                        begin
                           SC.SC_Inner := S.L_Init;
                           SC.SC_Len   := IT.Target.Len;
                           SC.Sem_Ty   := Ty;
                           S.L_Init    := SC;
                        end;
                     --  §2.9.1 the initialiser's type must be assignable to
                     --  the declared type. `&T → &dyn Trait` coercion is
                     --  resolved downstream, so it is exempted here.
                     elsif IT /= null
                       and then not Assignable (Ty, IT)
                       and then not (Is_Dyn_Ref (Ty) and then Is_Ref (IT))
                       and then not Is_Generic_Param_Ty (IT)
                       and then not Is_Generic_Param_Ty (Ty)
                     then
                        --  In a generic template, associated-item types are
                        --  not yet concrete; the assignability is re-checked
                        --  at each monomorphised instance.
                        Error ("initialiser of type '" & Image (IT)
                               & "' is not assignable to declared type '"
                               & Image (Ty) & "' (spec 2.9.1)");
                     end if;
                  end;
               end if;
               if not S.L_Tuple_Names.Is_Empty then
                  --  §4.7 destructuring: each name binds a tuple field.
                  if Ty = null or else Ty.Kind /= T_Tuple then
                     Error ("destructuring let requires a tuple value, "
                            & "got '" & Image (Ty) & "'");
                  elsif Natural (S.L_Tuple_Names.Length)
                          /= Natural (Ty.Elems.Length)
                  then
                     Error ("destructuring pattern has"
                            & S.L_Tuple_Names.Length'Image
                            & " names but tuple '" & Image (Ty) & "' has"
                            & Ty.Elems.Length'Image & " fields");
                  else
                     for I in S.L_Tuple_Names.First_Index ..
                              S.L_Tuple_Names.Last_Index
                     loop
                        Check_Dup_In_Scope (S.L_Tuple_Names.Element (I));
                        Scope.Append
                          ((Name => S.L_Tuple_Names.Element (I),
                            Ty   => Kurt.Layout.Tuple_Field_Type
                                      (Ty, I - S.L_Tuple_Names.First_Index),
                            Is_Mut => S.Kind = S_Mut));
                     end loop;
                  end if;
               else
                  if Ty = null then
                     Error ("binding '" & SU.To_String (S.L_Name)
                            & "' needs a type annotation or initialiser");
                  end if;
                  Check_Dup_In_Scope (S.L_Name);
                  --  §2.2.1: `let` is single-assignment (immutable); `mut`
                  --  is mutable.
                  Scope.Append
                    ((Name => S.L_Name, Ty => Ty,
                      Is_Mut => S.Kind = S_Mut));
                  Register_Borrow (SU.To_String (S.L_Name), S.L_Init);
                  --  §8.8.2: initialising from a `destruct`-typed binding
                  --  transfers it (the source is invalidated).
                  Maybe_Move (S.L_Init);
               end if;
            end;

         when S_Assign =>
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

         when S_Fence =>
            null;   --  §8.5.3: fences carry no static obligations here

         when S_While =>
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
                     pragma Unreferenced (CT);
                  begin
                     null;
                  end;
               end if;
               In_Loop := In_Loop + 1;
               if Has_Label then
                  Label_Stack.Append (S.W_Label);   --  §7.9 in scope
               end if;
               Check_Block (S.W_Body);
               Check_Block (S.W_Then);   --  §7.5.3 step block
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

         when S_If =>
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

         when S_Airside_Block =>
            In_Airside := In_Airside + 1;
            Check_Block (S.A_Stmts);
            In_Airside := In_Airside - 1;

         when S_Extract =>
            --  §7: `let v <- e else err { ... }`. e is a contract value;
            --  v binds the success payload for the rest of the block,
            --  err binds the failure payload inside the else block.
            declare
               ET : constant Type_Access := Infer (S.X_Expr, null);
               EN : constant String :=
                 (if ET /= null and then ET.Kind = T_Named
                  then SU.To_String (ET.Name) else "");
               Saved : Natural;
            begin
               if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
               then
                  Error ("`<-` requires a contract value; got '"
                         & Image (ET) & "'");
                  Check_Block (S.X_Else);
               else
                  Saved := Natural (Scope.Length);
                  if SU.Length (S.X_Err) > 0 then
                     Scope.Append
                       ((Name => S.X_Err,
                         Ty   => Kurt.Layout.Variant_Field_Type
                                   (ET,
                                    Kurt.Layout.Contract_Fail_Variant (EN),
                                    1), others => <>));
                  end if;
                  Check_Block (S.X_Else);
                  while Natural (Scope.Length) > Saved loop
                     Scope.Delete_Last;
                  end loop;
                  --  §7.2.3: the `else` block shall either diverge or
                  --  yield a fallback value via `express`; otherwise
                  --  the extracted binding would continue uninitialized
                  --  on the failure path.
                  if not Stmts_Diverge (S.X_Else) then
                     Error ("the `else` of `<-` must diverge (return/"
                            & "break/continue/@trap) or yield a value "
                            & "via `express` (spec 7.2.3)");
                  end if;
                  declare
                     Succ_Ty : constant Type_Access :=
                       Kurt.Layout.Variant_Field_Type
                         (ET, Kurt.Layout.Contract_Success_Variant (EN), 1);
                  begin
                     if S.X_Is_Place then
                        --  §7.2.3 copy the success payload into the place,
                        --  which shall be an existing `mut` binding.
                        declare
                           PN : constant String := SU.To_String (S.X_Bind);
                           PT : constant Type_Access := Lookup_Scope (PN);
                           Is_Local : Boolean;
                           Mutable  : constant Boolean :=
                             Lookup_Scope_Mut (PN, Is_Local);
                        begin
                           if PT = null then
                              Error ("extract-assignment target '" & PN
                                     & "' is not a binding");
                           elsif not Mutable then
                              Error ("extract-assignment target '" & PN
                                     & "' must be `mut` (spec 7.2.3)");
                           elsif not Assignable (PT, Succ_Ty) then
                              Error ("extract-assignment type mismatch: "
                                     & "place is '" & Image (PT)
                                     & "' but success payload is '"
                                     & Image (Succ_Ty) & "'");
                           end if;
                        end;
                     else
                        --  Success binding stays in scope for the rest.
                        Scope.Append
                          ((Name => S.X_Bind, Ty => Succ_Ty, others => <>));
                     end if;
                  end;
               end if;
            end;

         when S_Break =>
            --  §7.7/§7.9: break may carry a value and/or a target label.
            if In_Loop = 0 then
               Error ("`break` shall appear only within a loop (spec 7.7)");
            end if;
            Check_Loop_Label (S.Brk_Label);
            if S.Brk_Val /= null then
               declare
                  T : constant Type_Access := Infer (S.Brk_Val, null);
                  pragma Unreferenced (T);
               begin null; end;
            end if;
         when S_Continue =>
            --  §7.9: optional target label.
            if In_Loop = 0 then
               Error ("`continue` shall appear only within a loop "
                      & "(spec 7.7)");
            end if;
            Check_Loop_Label (S.Cont_Label);
         when S_Express =>
            --  §7.8: the expressed value is typed against the innermost
            --  enclosing block expression's expected type (steering
            --  literals like a `let` annotation); outside a block
            --  expression it is inferred freely.
            declare
               T : constant Type_Access :=
                 Infer (S.Xp_Val, Express_Expected);
               pragma Unreferenced (T);
            begin null; end;

         when S_Trap =>
            --  §7.10/§7.11: `@trap;` is a diverging expression; it
            --  produces no value and imposes no type obligation.
            null;
         when S_Asm =>
            --  §6.11 inline assembly is opaque to the type system, but its
            --  `in`/`io` operand expressions are ordinary Kurt expressions
            --  (inferred so codegen has their types) and each `out`/`io`
            --  target shall be an existing binding (a place).
            --  §6.11: `asm` is permitted only inside an airside region.
            if In_Airside = 0 then
               Error ("inline `asm` is permitted only inside an `airside` "
                      & "block or `airside fn` body (spec 6.11)");
            end if;
            for I in S.Asm_In_Exprs.First_Index ..
                     S.Asm_In_Exprs.Last_Index loop
               declare
                  T : constant Type_Access :=
                    Infer (S.Asm_In_Exprs.Element (I), null);
                  pragma Unreferenced (T);
               begin null; end;
            end loop;
            for I in S.Asm_Out_Names.First_Index ..
                     S.Asm_Out_Names.Last_Index loop
               if Lookup_Scope
                    (SU.To_String (S.Asm_Out_Names.Element (I))) = null
               then
                  Error ("asm `out` target '"
                         & SU.To_String (S.Asm_Out_Names.Element (I))
                         & "' is not a binding");
               end if;
            end loop;
            --  §6.11: overlap between a (resource-mode) operand target and
            --  a `clobber` entry, and duplicate resource targets, shall not
            --  appear. Logical/positional targets (`'…`) get impl-chosen
            --  registers and cannot textually overlap a named clobber.
            declare
               function In_Clobbers (R : String) return Boolean is
               begin
                  for K in S.Asm_Clobbers.First_Index ..
                           S.Asm_Clobbers.Last_Index loop
                     if SU.To_String (S.Asm_Clobbers.Element (K)) = R then
                        return True;
                     end if;
                  end loop;
                  return False;
               end In_Clobbers;

               procedure Check_Target (R : String) is
               begin
                  if R'Length > 0 and then R (R'First) /= '''
                    and then In_Clobbers (R)
                  then
                     Error ("asm operand target '" & R & "' overlaps a "
                            & "`clobber` entry (spec 6.11)");
                  end if;
               end Check_Target;
            begin
               for I in S.Asm_In_Regs.First_Index ..
                        S.Asm_In_Regs.Last_Index loop
                  Check_Target (SU.To_String (S.Asm_In_Regs.Element (I)));
               end loop;
               for I in S.Asm_Out_Regs.First_Index ..
                        S.Asm_Out_Regs.Last_Index loop
                  Check_Target (SU.To_String (S.Asm_Out_Regs.Element (I)));
               end loop;
            end;
      end case;
   end Check_Stmt;
