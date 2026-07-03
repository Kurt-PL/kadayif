separate (Kurt.Sema.Check)
   function Infer (E : Expr_Access; Expected : Type_Access)
      return Type_Access
   is
      function Infer_Closure return Type_Access is separate;
      function Infer_Cast return Type_Access is separate;
      function Infer_Match return Type_Access is separate;
      function Infer_Struct_Lit return Type_Access is separate;
      function Infer_Binary return Type_Access is separate;
      function Infer_Call return Type_Access is separate;
      function Infer_Path return Type_Access is separate;
   begin
      case E.Kind is
         when E_Int_Lit =>
            --  §3.4.1: a type suffix fixes the type; otherwise take
            --  the expected integer type, else default to saddr.
            --  §3.4.1 also permits an integer literal in a float
            --  context (e.g. `let x: fe8m23 = 42;` => 42.0).
            if SU.Length (E.Int_Suffix) > 0 then
               E.Sem_Ty := Mk_Named (SU.To_String (E.Int_Suffix));
            elsif Is_Integer_Type (Expected)
              or else Is_Float_Type (Expected)
            then
               E.Sem_Ty := Expected;
            else
               E.Sem_Ty := Mk_Named ("saddr");
            end if;
            return E.Sem_Ty;

         when E_Float_Lit =>
            --  §3.4.2: a suffix fixes the type; else an expected float
            --  type; else default fe11m52.
            if SU.Length (E.Float_Suffix) > 0 then
               E.Sem_Ty := Mk_Named (Canon_Float
                 (SU.To_String (E.Float_Suffix)));
            elsif Is_Float_Type (Expected) then
               E.Sem_Ty := Expected;
            else
               E.Sem_Ty := Mk_Named ("fe11m52");
            end if;
            return E.Sem_Ty;

         when E_Bool_Lit =>
            --  §3.4.3 bool literal: type is the built-in alias `bool`.
            E.Sem_Ty := Mk_Named ("bool");
            return E.Sem_Ty;

         when E_String_Lit =>
            --  Slice &[ui1] fat reference. NB §3.5.5 specifies the type
            --  as `&[ui1; N]` (a thin reference to a sized array), but the
            --  bootstrap represents a string literal as a fat slice
            --  (ptr+len, the `Len => 0` sentinel). Carrying the true N in
            --  the type would require switching the whole string-literal
            --  representation to a thin sized-array reference — deferred.
            E.Sem_Ty := Mk_Ref (R_Shared, False, RS_None,
                                new AST_Type'(Kind => T_Array,
                                              Elem => Mk_Named ("ui1"),
                                              Len  => 0));
            return E.Sem_Ty;

         when E_Path =>
            return Infer_Path;
         when E_Field =>
            declare
               RT  : constant Type_Access := Infer (E.F_Recv, null);
               --  §6.2.5 reference transparency: field access through
               --  a reference reaches the referent's fields.
               RTD : constant Type_Access :=
                 (if Is_Ref (RT) then RT.Target else RT);
               FN  : constant String := SU.To_String (E.F_Name);
            begin
               if FN = "?" then
                  Error ("access to padding field '?' is prohibited (spec 5.5.2)");
               end if;
               if FN = "ptr" then
                  --  Fat-pointer view (§4.6.1): `.ptr` is &raw elem.
                  if E.F_Recv.Kind = E_String_Lit then
                     E.Sem_Ty := Mk_Raw_Ref (Mk_Named ("ui1"));
                  elsif RT /= null and then RT.Kind = T_Array then
                     E.Sem_Ty := Mk_Raw_Ref (RT.Elem);
                  elsif RTD /= null and then RTD.Kind = T_Array then
                     --  through a reference, e.g. a `&[T]` slice
                     E.Sem_Ty := Mk_Raw_Ref (RTD.Elem);
                  elsif Is_Ref (RT) then
                     E.Sem_Ty := Mk_Raw_Ref (RT.Target);
                  else
                     E.Sem_Ty := Mk_Raw_Ref (Mk_Named ("ui1"));
                  end if;
               elsif FN = "len" then
                  E.Sem_Ty := Mk_Named ("uaddr");
               elsif RTD /= null and then RTD.Kind = T_Named
                 and then Kurt.Layout.Is_Struct (SU.To_String (RTD.Name))
               then
                  declare
                     FT : constant Type_Access :=
                       Kurt.Layout.Field_Type
                         (SU.To_String (RTD.Name), FN);
                  begin
                     if FT = null then
                        Error ("struct '" & SU.To_String (RTD.Name)
                               & "' has no field '" & FN & "'");
                     end if;
                     E.Sem_Ty := FT;
                  end;
               elsif RT /= null and then RT.Kind = T_Tuple then
                  --  §6.2.2 tuple field by index `.0`, `.1`, ...
                  declare
                     Idx : constant Integer := Integer'Value (FN);
                  begin
                     if Idx < 0 or else Idx >= Natural (RT.Elems.Length)
                     then
                        Error ("tuple index" & Idx'Image
                               & " out of range for '" & Image (RT) & "'");
                        E.Sem_Ty := null;
                     else
                        E.Sem_Ty :=
                          Kurt.Layout.Tuple_Field_Type (RT, Idx);
                     end if;
                  exception
                     when Constraint_Error =>
                        Error ("tuple field must be an integer index, "
                               & "got '." & FN & "'");
                        E.Sem_Ty := null;
                  end;
               else
                  Error ("unsupported field '." & FN & "'");
                  E.Sem_Ty := null;
               end if;
               return E.Sem_Ty;
            end;

         when E_Call =>
            return Infer_Call;
         when E_Binary =>
            return Infer_Binary;
         when E_If =>
            declare
               CT : constant Type_Access :=
                 Infer (E.I_Cond, Mk_Named ("bool"));
               TT : constant Type_Access := Infer (E.I_Then, Expected);
               --  §7.11: a diverging `then` contributes no type; steer the
               --  `else` by the surviving expected type, not by `never`.
               ET : constant Type_Access :=
                 Infer (E.I_Else,
                        (if Is_Never_Ty (TT) then Expected else TT));
               pragma Unreferenced (CT);
            begin
               --  §7.11 unification: drop the diverging branch; the
               --  result type comes from the non-diverging one (or is
               --  itself `never` when both diverge).
               if Is_Never_Ty (TT) then
                  E.Sem_Ty := ET;
               elsif Is_Never_Ty (ET) then
                  E.Sem_Ty := TT;
               else
                  if not Same_Type (TT, ET) then
                     Error ("if branches have differing types: '"
                            & Image (TT) & "' vs '" & Image (ET)
                            & "' (§7.1)");
                  end if;
                  E.Sem_Ty := TT;
               end if;
               return E.Sem_Ty;
            end;

         when E_Deref =>
            declare
               IT : constant Type_Access := Infer (E.D_Inner, null);
            begin
               if Is_Ref (IT) then
                  --  §2.6: dereferencing a `&raw` reference is an
                  --  airside-only operation. `&`/`$` derefs are landside.
                  if IT.Sigil = R_Raw and then In_Airside = 0 then
                     Error ("dereference of a `&raw` reference is "
                            & "permitted only in an `airside` region "
                            & "(spec 2.6)");
                  end if;
                  --  §2.6: `&mut T` access (load and store) is an
                  --  airside-only operation. This E_Deref case is
                  --  reached both for an rvalue load (`*m`) and for a
                  --  store target (the S_Assign LHS is inferred here),
                  --  so a single gate covers both directions. `$`
                  --  (R_Excl) and plain `&`/atomic/guard are not in the
                  --  §2.6 list and are not gated here.
                  if IT.Sigil = R_Shared and then IT.R_Store = RS_Mut
                    and then In_Airside = 0
                  then
                     Error ("load/store through a `&mut T` reference is "
                            & "permitted only in an `airside` region "
                            & "(spec 2.6)");
                  end if;
                  E.Sem_Ty := IT.Target;
               else
                  Error ("dereference of non-reference type '"
                         & Image (IT) & "'");
                  E.Sem_Ty := null;
               end if;
               return E.Sem_Ty;
            end;

         when E_Struct_Lit =>
            return Infer_Struct_Lit;
         when E_Variant_New =>
            declare
               --  Concrete enum type from the expected type when the
               --  written name is a generic template / intrinsic verdict;
               --  keep its arguments (verdict payload types come from them).
               Conc : constant Type_Access :=
                 (if Expected /= null and then Expected.Kind = T_Named
                     and then Kurt.Layout.Is_Enum
                                (SU.To_String (Expected.Name))
                  then Expected
                  else Mk_Named (SU.To_String (E.VN_Enum)));
               EN : constant String := SU.To_String (Conc.Name);
               VN : constant String := SU.To_String (E.VN_Variant);
            begin
               if VN = "#wild#" then
                  --  §6.1.5 wild construction. Permitted only on an enum
                  --  that does not declare its own `#wild#` variant.
                  if not Kurt.Layout.Is_Enum (EN) then
                     Error ("unknown enum type '" & EN & "'");
                  elsif Kurt.Layout.Has_Wild_Variant (EN) then
                     Error ("`" & EN & "::#wild#` construction is not "
                            & "permitted: '" & EN & "' declares a #wild# "
                            & "variant (spec 6.1.5)");
                  end if;
                  E.Sem_Ty := Conc;
               elsif not Kurt.Layout.Is_Enum (EN) then
                  Error ("unknown enum type '" & EN & "'");
               elsif not Kurt.Layout.Has_Variant (EN, VN) then
                  Error ("enum '" & EN & "' has no variant '" & VN & "'");
               else
                  for I in E.VN_Fields.First_Index ..
                           E.VN_Fields.Last_Index
                  loop
                     declare
                        FI : constant Field_Init :=
                          E.VN_Fields.Element (I);
                        FT : constant Type_Access :=
                          Kurt.Layout.Variant_Field_Type_By_Name
                            (Conc, VN, SU.To_String (FI.Name));
                        VT : Type_Access;
                     begin
                        if FT = null then
                           Error ("variant '" & EN & "::" & VN
                                  & "' has no payload field '"
                                  & SU.To_String (FI.Name) & "'");
                        end if;
                        VT := Infer (FI.Val, FT);
                        if FT /= null and then not Assignable (FT, VT) then
                           Error ("payload field '"
                                  & SU.To_String (FI.Name) & "': expected '"
                                  & Image (FT) & "' but got '"
                                  & Image (VT) & "'");
                        end if;
                        --  §8.8.2 payload init from a binding is a transfer
                        --  when the payload type satisfies destruct.
                        Maybe_Move (FI.Val);
                     end;
                  end loop;
               end if;
               E.Sem_Ty := Conc;
               return E.Sem_Ty;
            end;

         when E_Match =>
            return Infer_Match;
         when E_Cast =>
            return Infer_Cast;
         when E_Unary =>
            --  §6.3.1 negation (numeric: int or float) / §6.5.3 bitwise
            --  NOT (integer) / §7.2.1 contract polarity inversion.
            declare
               OT : constant Type_Access := Infer (E.U_Operand, Expected);
            begin
               if OT /= null then
                  if E.U_Op = U_Neg
                    and then not (Is_Integer_Type (OT)
                                  or else Is_Float_Type (OT)
                                  or else Generic_Arith_OK (OT))
                  then
                     Error ("unary '-' requires a numeric operand, got '"
                            & Image (OT) & "'");
                  elsif E.U_Op = U_Not
                    and then not Is_Integer_Type (OT)
                  then
                     --  §7.2.1: `!` on a contract value exchanges the
                     --  success and failure variants. The bootstrap
                     --  supports the self-inverse cases: bool, and any
                     --  contract enum whose two payloads are identical
                     --  (a declared `-> inv_type` pair is otherwise
                     --  required and not yet implemented).
                     if not Is_Contract_Ty (OT) then
                        Error ("unary '!' requires an integer or a "
                               & "`contract` operand, got '"
                               & Image (OT) & "'");
                     elsif SU.To_String (OT.Name) /= "bool" then
                        declare
                           EN : constant String :=
                             SU.To_String (OT.Name);
                           SV : constant String :=
                             Kurt.Layout.Contract_Success_Variant (EN);
                           FV : constant String :=
                             Kurt.Layout.Contract_Fail_Variant (EN);
                           SC : constant Natural :=
                             Kurt.Layout.Variant_Field_Count (EN, SV);
                           FC : constant Natural :=
                             Kurt.Layout.Variant_Field_Count (EN, FV);
                        begin
                           if SC /= FC
                             or else (SC > 0 and then not Same_Type
                               (Kurt.Layout.Variant_Field_Type
                                  (OT, SV, 1),
                                Kurt.Layout.Variant_Field_Type
                                  (OT, FV, 1)))
                           then
                              Error ("'!' on '" & Image (OT)
                                     & "' needs a declared inverted "
                                     & "pair -- asymmetric payloads "
                                     & "(spec 7.2.1; bootstrap supports "
                                     & "the self-inverse case only)");
                           end if;
                        end;
                     end if;
                  end if;
               end if;
               E.Sem_Ty := OT;
               return OT;
            end;

         when E_Question =>
            --  §6.2.4: `e?` requires e and the enclosing fn return to
            --  both satisfy `contract`. Failure payload types shall
            --  match. The expression's type is e's success payload.
            declare
               IT : constant Type_Access := Infer (E.Q_Inner, null);
               EN : constant String :=
                 (if IT /= null and then IT.Kind = T_Named
                  then SU.To_String (IT.Name) else "");
               Ret_EN : constant String :=
                 (if Cur_Ret /= null and then Cur_Ret.Kind = T_Named
                  then SU.To_String (Cur_Ret.Name) else "");
            begin
               if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN) then
                  Error ("`?` operand must satisfy `contract`, got '"
                         & Image (IT) & "'");
                  E.Sem_Ty := IT;
                  return E.Sem_Ty;
               end if;
               if Ret_EN = ""
                 or else not Kurt.Layout.Is_Contract_Enum (Ret_EN)
               then
                  Error ("`?` requires the enclosing subroutine to "
                         & "return a `contract` type; got '"
                         & Image (Cur_Ret) & "'");
               elsif not Same_Type (Kurt.Layout.Variant_Field_Type
                       (IT, Kurt.Layout.Contract_Fail_Variant (EN), 1),
                     Kurt.Layout.Variant_Field_Type
                       (Cur_Ret,
                        Kurt.Layout.Contract_Fail_Variant (Ret_EN), 1))
               then
                  Error ("`?` failure payload type of '" & Image (IT)
                         & "' does not match the enclosing return "
                         & "type '" & Image (Cur_Ret) & "' (spec 7.2.4)");
               end if;
               E.Sem_Ty := Kurt.Layout.Variant_Field_Type
                 (IT, Kurt.Layout.Contract_Success_Variant (EN), 1);
               return E.Sem_Ty;
            end;

         when E_Tuple_Lit =>
            --  §6.1.7: type is .{T1, ..., TN} from element types. When an
            --  expected tuple type is in context, steer each element.
            declare
               Tup : constant Type_Access :=
                 new AST_Type (Kind => T_Tuple);
            begin
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index
               loop
                  declare
                     Exp : Type_Access := null;
                     Eit : constant Expr_Access := E.TL_Elems.Element (I);
                  begin
                     if Expected /= null and then Expected.Kind = T_Tuple
                       and then I - E.TL_Elems.First_Index
                         < Natural (Expected.Elems.Length)
                     then
                        Exp := Expected.Elems.Element
                          (Expected.Elems.First_Index
                             + (I - E.TL_Elems.First_Index));
                     end if;
                     Tup.Elems.Append (Infer (Eit, Exp));
                  end;
               end loop;
               E.Sem_Ty := Tup;
               return Tup;
            end;

         when E_Ref =>
            --  §8.1 reference creation. The place is a binding or field
            --  access; the result type is `sigil [mods] T`.
            declare
               PT : constant Type_Access := Infer (E.Rf_Place, null);
            begin
               if E.Rf_Place.Kind /= E_Path
                 and then E.Rf_Place.Kind /= E_Field
                 and then E.Rf_Place.Kind /= E_Deref
               then
                  Error ("reference creation requires a place "
                         & "expression (binding, field, or deref)");
               end if;
               --  §8.5.2: atomic/guard references are restricted to
               --  unsigned integer referents.
               if E.Rf_Store in RS_Atomic | RS_Guard
                 and then not Is_Unsigned_Int_Type (PT)
               then
                  Error ("'&" & (if E.Rf_Store = RS_Atomic
                                 then "atomic" else "guard")
                         & "' requires an unsigned integer referent, "
                         & "got '" & Image (PT) & "' (spec 8.5.2)");
               end if;
               --  §5.4: only shared references may be created from an
               --  immutable `static` in landside code.
               if E.Rf_Place.Kind = E_Path
                 and then Natural (E.Rf_Place.Segments.Length) = 1
               then
                  declare
                     Name : constant String := SU.To_String
                       (E.Rf_Place.Segments.Last_Element);
                     M    : Boolean;
                  begin
                     if Lookup_Scope (Name) = null
                       and then Find_Static_Decl (Name, M)
                       and then not M
                       and then (E.Rf_Sigil = R_Excl
                                 or else E.Rf_Store = RS_Mut)
                     then
                        Error ("only shared references ('&', "
                               & "'&volatile', '&atomic', '&guard') "
                               & "may be created from immutable "
                               & "static '" & Name & "' (spec 5.4)");
                     end if;
                     --  §2.2.1: an exclusive ('$') or '&mut' reference may
                     --  be created only from a mutable binding.
                     declare
                        Bmut, Found : Boolean;
                     begin
                        Bmut := Lookup_Scope_Mut (Name, Found);
                        if Found and then not Bmut
                          and then (E.Rf_Sigil = R_Excl
                                    or else E.Rf_Store = RS_Mut)
                        then
                           Error ("an exclusive ('$') or '&mut' reference "
                                  & "requires a mutable binding; '" & Name
                                  & "' is an immutable `let` (spec 2.2.1)");
                        end if;
                     end;
                  end;
               end if;
               E.Sem_Ty :=
                 Mk_Ref (E.Rf_Sigil, E.Rf_Volatile, E.Rf_Store, PT);
               return E.Sem_Ty;
            end;

         when E_CAS =>
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

         when E_Array_Lit =>
            --  §6.1.6: element list or repeat form. The element type is
            --  steered by the expected array type when present.
            declare
               Exp_Elem : constant Type_Access :=
                 (if Expected /= null and then Expected.Kind = T_Array
                  then Expected.Elem else null);
               ET  : Type_Access := null;
               Arr : constant Type_Access :=
                 new AST_Type (Kind => T_Array);
            begin
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index
               loop
                  declare
                     T : constant Type_Access :=
                       Infer (E.AL_Elems.Element (I),
                              (if ET = null then Exp_Elem else ET));
                  begin
                     --  §9.5: a `[&dyn Trait; N]` literal coerces each
                     --  `&U` element (U implements Trait) to `&dyn Trait`.
                     if Is_Dyn_Ref (Exp_Elem) and then Is_Ref (T)
                       and then T.Target /= null
                       and then T.Target.Kind = T_Named
                       and then Type_Implements
                         (SU.To_String (T.Target.Name),
                          SU.To_String (Exp_Elem.Target.Trait_Name))
                     then
                        declare
                           DC : constant Expr_Access :=
                             new Expr_Node (Kind => E_Dyn_Cast);
                        begin
                           DC.DC_Inner := E.AL_Elems.Element (I);
                           DC.DC_Conc  := T.Target.Name;
                           DC.DC_Trait := Exp_Elem.Target.Trait_Name;
                           DC.Sem_Ty   := Exp_Elem;
                           E.AL_Elems.Replace_Element (I, DC);
                        end;
                        ET := Exp_Elem;
                     elsif ET = null then
                        ET := T;
                     elsif not Same_Type (ET, T) then
                        Error ("array literal elements have differing "
                               & "types: '" & Image (ET) & "' vs '"
                               & Image (T) & "'");
                     end if;
                     --  §8.8.2 an element supplied by a `destruct`-typed
                     --  binding is transferred into the array (its
                     --  scope-exit drop is suppressed). Only the element-
                     --  list form transfers; the repeat form `[e; N]`
                     --  would copy `e` N times.
                     if E.AL_Repeat = 0 then
                        Maybe_Move (E.AL_Elems.Element (I));
                     end if;
                  end;
               end loop;
               Arr.Elem := ET;
               Arr.Len  :=
                 (if E.AL_Repeat > 0 then E.AL_Repeat
                  else Natural (E.AL_Elems.Length));
               if Expected /= null and then Expected.Kind = T_Array
                 and then Expected.Len /= Arr.Len
               then
                  Error ("array literal has" & Arr.Len'Image
                         & " elements but the expected type '"
                         & Image (Expected) & "' has"
                         & Expected.Len'Image);
               end if;
               E.Sem_Ty := Arr;
               return Arr;
            end;

         when E_Dyn_Cast =>
            --  Synthesised by the coercion logic below; its type is
            --  the `&dyn Trait` it was annotated with at creation.
            return E.Sem_Ty;

         when E_Slice_Cast =>
            --  Synthesised by the coercion logic below; type is the
            --  `&[T]` it was annotated with at creation.
            return E.Sem_Ty;

         when E_Type_Intrinsic =>
            --  §6.12.1 layout intrinsics: translation-time `uaddr`
            --  constants. The operand shall be a known sized type;
            --  `@offset` additionally requires a struct field.
            declare
               Known : Boolean := False;
            begin
               if E.TI_Ty.Kind in T_Ref | T_Tuple | T_Array then
                  Known := True;
               elsif E.TI_Ty.Kind = T_Named then
                  declare
                     TN : constant String := SU.To_String (E.TI_Ty.Name);
                  begin
                     --  §4: `void` is a complete type — size 0, align 0.
                     Known :=
                       Is_Integer_Type (E.TI_Ty)
                       or else Is_Float_Type (E.TI_Ty)
                       or else TN = "bool"
                       or else TN = "void"
                       or else Kurt.Layout.Is_Struct (TN)
                       or else Kurt.Layout.Is_Enum (TN);
                  end;
               end if;

               if E.TI_Ty.Kind = T_Array and then E.TI_Ty.Len = 0
                 and then E.TI_Op in TI_Size | TI_Align
               then
                  --  §8.1.4: `[T]` is not a type — it exists only inside
                  --  a slice-reference production, so it has no size of
                  --  its own to query.
                  Error ("`@size`/`@align` cannot be applied to `[T]`: "
                         & "a slice exists only behind a reference "
                         & "(spec 8.1.4)");
               elsif not Known then
                  declare
                     TypeNameStr : constant String :=
                       (if E.TI_Ty.Kind = T_Named then SU.To_String (E.TI_Ty.Name)
                        else "anonymous type");
                  begin
                     Error ("type intrinsic on unknown type '" & TypeNameStr
                            & "' (spec 6.12)");
                  end;
               elsif E.TI_Op = TI_Offset then
                  if E.TI_Ty.Kind /= T_Named or else not Kurt.Layout.Is_Struct (SU.To_String (E.TI_Ty.Name)) then
                     Error ("`@offset` requires a struct type, got '"
                            & (if E.TI_Ty.Kind = T_Named then SU.To_String (E.TI_Ty.Name) else "anonymous type")
                            & "' (spec 6.12.1)");
                  elsif Kurt.Layout.Field_Type
                          (SU.To_String (E.TI_Ty.Name), SU.To_String (E.TI_Field)) = null
                  then
                     Error ("struct '" & SU.To_String (E.TI_Ty.Name) & "' has no field '"
                            & SU.To_String (E.TI_Field)
                            & "' (spec 6.12.1)");
                  end if;
               end if;
               E.Sem_Ty := Mk_Named ("uaddr");
               return E.Sem_Ty;
            end;

         when E_Uninit =>
            --  §6.1.8: `uninit` is valid only as the value of an
            --  assignment to a binding's object (handled in S_Let/S_Mut/
            --  S_Assign). Reaching it through ordinary inference means it
            --  appeared in some other position, which is ill-formed.
            Error ("`uninit` shall appear only as the value of an "
                   & "assignment to a binding (spec 6.1.8)");
            E.Sem_Ty := Expected;
            return Expected;

         when E_Closure =>
            return Infer_Closure;
         when E_Destruct =>
            --  §8.4/§8.11: `destruct(e)` runs e's destructor now;
            --  `undestruct(e)` reclaims e's storage without running it
            --  (airside only). Both consume the operand binding — a
            --  later use is a use-after-transfer failure. The result is
            --  `void`.
            declare
               IT      : constant Type_Access := Infer (E.DT_Inner, null);
               Is_Bind : constant Boolean :=
                 E.DT_Inner /= null and then E.DT_Inner.Kind = E_Path
                 and then Natural (E.DT_Inner.Segments.Length) = 1;
               Word    : constant String :=
                 (if E.DT_Undo then "`undestruct`" else "`destruct`");
            begin
               if not Is_Bind then
                  Error (Word & " operand shall be a binding (bootstrap)");
               elsif not Satisfies_Destruct (IT) then
                  Error (Word & " requires an operand whose type satisfies "
                         & "`destruct` (spec 8.11)");
               end if;
               if E.DT_Undo and then In_Airside = 0 then
                  Error ("`undestruct` shall appear only inside an "
                         & "`airside` block or `airside fn` body "
                         & "(spec 8.4)");
               end if;
               Maybe_Move (E.DT_Inner);
               E.Sem_Ty := Mk_Named ("void");
               return E.Sem_Ty;
            end;

         when E_Airside_Blk =>
            --  §6.9 `airside { ... }` block expression. The body is
            --  checked as an airside lexical scope; the block's type is
            --  the type of the trailing `express` value, or `void` when
            --  no `express` targets the block. (Bootstrap: only a
            --  trailing `express` yields the value.)
            declare
               Saved : constant Type_Access := Express_Expected;
            begin
               Express_Expected := Expected;
               if E.AB_Airside then
                  In_Airside := In_Airside + 1;
               end if;
               Check_Block (E.AB_Stmts);
               if E.AB_Airside then
                  In_Airside := In_Airside - 1;
               end if;
               Express_Expected := Saved;
            end;
            if not E.AB_Stmts.Is_Empty
              and then E.AB_Stmts.Last_Element.Kind = S_Express
              and then E.AB_Stmts.Last_Element.Xp_Val /= null
            then
               E.Sem_Ty := E.AB_Stmts.Last_Element.Xp_Val.Sem_Ty;
            else
               E.Sem_Ty := Mk_Named ("void");
            end if;
            return E.Sem_Ty;

         when E_Loop =>
            --  §7.7 `loop { … }` as an expression. The body is checked in
            --  a loop context; its type is the annotated (expected) type
            --  when known, otherwise the type of the first `break expr`
            --  targeting this loop, or `never` when no break carries a
            --  value (a diverging loop).
            declare
               Found : Type_Access := null;

               --  Scan for a `break`-with-value that targets this loop:
               --  descend into `if`/`airside` bodies but not into a nested
               --  loop (whose breaks target the inner loop).
               procedure Scan (V : Stmt_Vectors.Vector) is
               begin
                  for I in V.First_Index .. V.Last_Index loop
                     declare
                        BS : constant Stmt_Access := V.Element (I);
                     begin
                        case BS.Kind is
                           when S_Break =>
                              if Found = null
                                and then BS.Brk_Val /= null
                              then
                                 Found := BS.Brk_Val.Sem_Ty;
                              end if;
                           when S_If =>
                              Scan (BS.SI_Then);
                              Scan (BS.SI_Else);
                           when S_Airside_Block =>
                              Scan (BS.A_Stmts);
                           when others =>
                              null;   --  skip S_While (nested loop)
                        end case;
                     end;
                  end loop;
               end Scan;
            begin
               In_Loop := In_Loop + 1;
               Check_Block (E.Loop_Body);
               In_Loop := In_Loop - 1;
               if Expected /= null and then not Is_Void_Type (Expected) then
                  E.Sem_Ty := Expected;
               else
                  Scan (E.Loop_Body);
                  E.Sem_Ty :=
                    (if Found /= null then Found else Mk_Named ("never"));
               end if;
            end;
            return E.Sem_Ty;
      end case;
   end Infer;
