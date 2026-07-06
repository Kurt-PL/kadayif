separate (Kurt.Sema.Check.Check_Stmt)
   procedure Check_Let is
   begin
            if S.L_Is_Refut then
               --  §5.2.1/§5.10.4: `let Enum::V { binds } = e [else { ... }];`.
               --  Refutability is a static-semantic property of the
               --  matched enum, computed here (not by the parser, which
               --  only records the pattern's syntactic *shape* --
               --  Kurt.Parser.Parse_Stmt.Stmt_Let): a variant pattern is
               --  irrefutable when the enum has exactly one variant, and
               --  refutable otherwise. The biconditional then governs
               --  `else`: a refutable pattern requires one, an
               --  irrefutable one forbids it (its body would be
               --  unreachable).
               declare
                  CT : constant Type_Access := Infer (S.L_Init, null);
                  EN : constant String :=
                    (if CT /= null and then CT.Kind = T_Named
                     then SU.To_String (CT.Name) else "");
                  VN : constant String :=
                    SU.To_String (S.L_Refut_Pat.Path.Last_Element);
                  Is_Enum   : constant Boolean :=
                    EN /= "" and then Kurt.Layout.Is_Enum (EN);
                  --  §5.10.4: irrefutable iff the enum has exactly one
                  --  variant. An unresolved/non-enum scrutinee (already
                  --  flagged below) is conservatively treated as
                  --  refutable, matching the pre-existing "else required"
                  --  shape most such malformed programs were written in.
                  Refutable : constant Boolean :=
                    not Is_Enum
                    or else Kurt.Layout.Variant_Count (EN) > 1;
               begin
                  if EN = "" or else not Is_Enum then
                     Error ("refutable `let` requires an enum value; got '"
                            & Image (CT) & "' (spec 5.2.1)");
                  elsif not Kurt.Layout.Has_Variant (EN, VN) then
                     Error ("enum '" & EN & "' has no variant '" & VN
                            & "' (spec 5.2.1)");
                  end if;
                  if Refutable and then S.L_Else.Is_Empty then
                     Error ("refutable `let` pattern (enum '" & EN
                            & "' has more than one variant) shall carry "
                            & "an `else` clause (spec 5.2.1/5.10.4)");
                  elsif not Refutable and then not S.L_Else.Is_Empty then
                     Error ("irrefutable `let` pattern (enum '" & EN
                            & "' has exactly one variant) shall not "
                            & "carry an `else` clause -- it is "
                            & "unreachable (spec 5.2.1/5.10.4)");
                  end if;
                  --  else first (no payload in scope here), then the
                  --  payload bindings persist into the enclosing scope.
                  Check_Block (S.L_Else);
                  --  §5.2.1: the `else` block shall diverge (return/
                  --  break/continue/@trap/express etc.) -- otherwise
                  --  control would fall through into the rest of the
                  --  scope with the pattern's names left unbound. Only
                  --  meaningful when an `else` is actually present.
                  if not S.L_Else.Is_Empty
                    and then not Stmts_Diverge (S.L_Else)
                  then
                     Error ("the `else` of a refutable `let` must "
                            & "diverge (return/break/continue/@trap/"
                            & "express); a value would otherwise fall "
                            & "through unbound (spec 5.2.1)");
                  end if;
                  if EN /= "" and then Is_Enum
                    and then Kurt.Layout.Has_Variant (EN, VN)
                  then
                     --  §5.10.2 field coverage.
                     Check_Payload_Coverage (S.L_Refut_Pat, EN, VN);
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
               if S.L_Is_Const and then S.L_Init /= null
                 and then S.L_Init.Kind = E_Uninit
               then
                  --  §5.3/§6.1.8: `uninit` has no translation-time value,
                  --  so it cannot initialise a `const`.
                  Error ("const '" & SU.To_String (S.L_Name)
                         & "': initializer shall not be `uninit` -- a "
                         & "`const` initializer is evaluated at "
                         & "translation time (spec 5.3)");
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
                     --  §8.9: `let v = *r;` copies out through the
                     --  dereference -- rejected when the referent
                     --  satisfies `destruct` and the reference is tracked.
                     Check_No_Destruct_Load (S.L_Init);
                     --  §5.3: a statement-position `const` (Fix 4, spec
                     --  5.3 -- previously top-level only) is bound by the
                     --  same translation-time-evaluable requirement as a
                     --  top-level `const`: reuse Is_Xlatime_Foldable
                     --  (§6.10.2) rather than a parallel predicate. The
                     --  bootstrap does not plumb the folded value into the
                     --  top-level const table, so (documented limitation)
                     --  a local const is usable as an ordinary immutable
                     --  binding but NOT in an array-length position
                     --  `[T; N]` -- only a top-level `const` is (spec 4.7).
                     if S.L_Is_Const
                       and then not Is_Xlatime_Foldable (S.L_Init)
                     then
                        Error ("const '" & SU.To_String (S.L_Name)
                               & "': initializer is not evaluable at "
                               & "translation time (spec 5.3, bootstrap "
                               & "subset: literals, type intrinsics, "
                               & "consts, aggregate literals over those, "
                               & "and pure operators)");
                     end if;
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
                  --  §5.2 deferred initialization: the initializer is
                  --  genuinely omitted (an explicit `= uninit` establishes
                  --  the determination immediately, spec 6.1.8, so it is
                  --  not tracked here). Uninit until some assignment
                  --  reaches this binding's whole object.
                  if S.L_Init = null then
                     Init_States.Append
                       ((Name   => S.L_Name,
                         State  => St_Uninit,
                         Depth  => Natural (Scope.Length),
                         Ty     => Ty,
                         Is_Let => S.Kind = S_Let));
                  end if;
               end if;
            end;

   end Check_Let;
