separate (Kurt.Sema.Check.Infer)
   function Infer_Match return Type_Access is
   begin
            declare
               Scrut_Ty : constant Type_Access := Infer (E.M_Scrut, null);
               Result   : Type_Access := Expected;
               Has_Wild : Boolean := False;
               Any_Live : Boolean := False;  --  §7.11 saw a non-diverging arm
               Is_Enum_Scrut : constant Boolean :=
                 Scrut_Ty /= null and then Scrut_Ty.Kind = T_Named
                 and then Kurt.Layout.Is_Enum
                            (SU.To_String (Scrut_Ty.Name));
               --  §5.10.1: the parser desugars an or-pattern `p | q` into
               --  consecutive arms sharing one Arm_Body access value, so
               --  alternatives are recognised here by body identity. All
               --  alternatives shall bind the same names at the same
               --  types; the previous alternative's bindings are kept for
               --  the comparison.
               Prev_Body  : Expr_Access := null;
               Prev_Names : Path_Segments.Vector;
               Prev_Tys   : Type_Vectors.Vector;
               --  §8.8.2/§5.2: arms are mutually exclusive alternatives,
               --  not sequential code -- each is checked from the SAME
               --  pre-match Moved/Init_States snapshot (one arm shall not
               --  see another's moves/assignments); a diverging arm's
               --  ending state drops out of the join (control never falls
               --  through it). Combined_Init/Union_Moved fold in each live
               --  arm's result as it is seen (associative: once any two
               --  live arms disagree on a name the running state becomes
               --  Maybe and further agreement cannot undo that).
               Init_Pre      : constant Init_Vec.Vector := Init_States;
               Moved_Pre     : constant Moved_Vec.Vector := Moved;
               Combined_Init : Init_Vec.Vector := Init_Pre;
               Union_Moved   : Moved_Vec.Vector := Moved_Pre;
               Any_Live_Arm  : Boolean := False;

               --  §7.4 item(a): recursively type-check and bind a nested
               --  payload sub-pattern P against a value of type Ty (the raw
               --  field's own type -- an enum, a struct, or, at the leaf, a
               --  plain bind/`#wild#`). Reuses the same field-coverage/
               --  airside checks as the top-level enum/struct branches
               --  below; exhaustiveness of the nested pattern itself is not
               --  proven (out of scope for this bootstrap subset) -- a
               --  mismatch simply falls through to the arm's own L_Next,
               --  exactly like any other failing sub-test within one arm.
               procedure Bind_Nested (P : Kurt.Parser.Pattern; Ty : Type_Access)
               is
               begin
                  case P.Kind is
                     when Pat_Wild =>
                        if SU.Length (P.Bind_Name) > 0 then
                           Scope.Append
                             ((Name => P.Bind_Name, Ty => Ty, others => <>));
                        end if;
                     when Pat_Variant =>
                        if Natural (P.Path.Length) = 1
                          and then (not P.Bindings.Is_Empty
                                    or else P.Has_Rest)
                        then
                           --  Nested struct pattern.
                           declare
                              SN : constant String :=
                                SU.To_String (P.Path.First_Element);
                           begin
                              if Ty = null or else Ty.Kind /= T_Named
                                or else not Kurt.Layout.Is_Struct
                                              (SU.To_String (Ty.Name))
                                or else SN /= SU.To_String (Ty.Name)
                              then
                                 Error ("nested struct pattern '" & SN
                                    & "' does not match field type '"
                                    & Image (Ty) & "' (spec 7.4)");
                              else
                                 if not P.Has_Rest
                                   and then Natural (P.Bindings.Length)
                                        /= Kurt.Layout.Struct_Field_Count (SN)
                                 then
                                    Error ("pattern for struct '" & SN
                                       & "' shall mention every field or "
                                       & "end with `...` (spec 5.10.2)");
                                 end if;
                                 for K in 1 .. Natural (P.Bindings.Length)
                                 loop
                                    declare
                                       FName : constant String :=
                                         (if K <= Natural
                                              (P.Bind_Fields.Length)
                                            and then SU.Length
                                              (P.Bind_Fields.Element (K)) > 0
                                          then SU.To_String
                                            (P.Bind_Fields.Element (K))
                                          elsif SU.Length
                                            (P.Bindings.Element (K)) > 0
                                          then SU.To_String
                                            (P.Bindings.Element (K))
                                          else Kurt.Layout.Struct_Field_Name
                                            (SN, K));
                                       FT : constant Type_Access :=
                                         Kurt.Layout.Field_Type (SN, FName);
                                    begin
                                       if FT = null then
                                          Error ("struct '" & SN
                                             & "' has no field '" & FName
                                             & "' (spec 5.10.2)");
                                       end if;
                                       if K <= Natural (P.Sub_Pats.Length)
                                         and then P.Sub_Pats.Element (K)
                                                    /= null
                                       then
                                          Bind_Nested
                                            (P.Sub_Pats.Element (K).all, FT);
                                       else
                                          Scope.Append
                                            ((Name => P.Bindings.Element (K),
                                              Ty => FT, others => <>));
                                       end if;
                                    end;
                                 end loop;
                              end if;
                           end;
                        elsif Natural (P.Path.Length) = 1 then
                           Scope.Append
                             ((Name => P.Path.First_Element, Ty => Ty,
                               others => <>));
                        elsif Natural (P.Path.Length) = 2
                          and then Ty /= null and then Ty.Kind = T_Named
                          and then Kurt.Layout.Is_Enum
                                     (SU.To_String (Ty.Name))
                        then
                           declare
                              EN : constant String := SU.To_String (Ty.Name);
                              VN : constant String :=
                                SU.To_String (P.Path.Last_Element);
                           begin
                              if not Kurt.Layout.Has_Variant (EN, VN) then
                                 Error ("enum '" & EN & "' has no variant '"
                                        & VN & "' (spec 7.4)");
                              else
                                 Check_Payload_Coverage (P, EN, VN);
                                 for K in 1 .. Natural (P.Bindings.Length)
                                 loop
                                    declare
                                       FT : constant Type_Access :=
                                         Pat_Field_Ty (P, Ty, VN, K);
                                    begin
                                       if Kurt.Layout.Variant_Field_Is_Airside
                                            (EN, VN, K)
                                         and then In_Airside = 0
                                       then
                                          Error ("payload field '"
                                            & Kurt.Layout.Variant_Field_Name
                                                (EN, VN, K)
                                            & "' of '" & EN & "::" & VN
                                            & "' is `airside` -- binding it "
                                            & "requires an `airside` region "
                                            & "(spec 5.5.1/6.2.2)");
                                       end if;
                                       if K <= Natural (P.Sub_Pats.Length)
                                         and then P.Sub_Pats.Element (K)
                                                    /= null
                                       then
                                          Bind_Nested
                                            (P.Sub_Pats.Element (K).all, FT);
                                       else
                                          Scope.Append
                                            ((Name => P.Bindings.Element (K),
                                              Ty => FT, others => <>));
                                       end if;
                                    end;
                                 end loop;
                              end if;
                           end;
                        else
                           Error ("nested variant pattern requires an enum "
                                  & "scrutinee (spec 7.4)");
                        end if;
                     when others =>
                        null;   --  item(b) sub-patterns on a payload field
                                --  (range/int/slice) are not yet shipped.
                  end case;
               end Bind_Nested;
            begin
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  declare
                     Arm   : constant Match_Arm := E.M_Arms.Element (I);
                     BT    : Type_Access;
                     Saved : constant Natural := Natural (Scope.Length);
                  begin
                     case Arm.Pat.Kind is
                        when Pat_Wild =>
                           --  §7.4: a guarded arm may fail at runtime, so a
                           --  guarded `#wild#` does not make the match
                           --  exhaustive — only an unguarded one does.
                           if Arm.Guard = null then
                              Has_Wild := True;
                           end if;
                        when Pat_Int =>
                           if not Is_Integer_Type (Scrut_Ty) then
                              Error ("integer pattern matched against "
                                     & "non-integer scrutinee '"
                                     & Image (Scrut_Ty) & "'");
                           end if;
                        when Pat_Range =>
                           --  §5.10 range pattern: numeric scrutinee, and
                           --  a non-empty bound order.
                           if not Is_Integer_Type (Scrut_Ty) then
                              Error ("range pattern matched against "
                                     & "non-integer scrutinee '"
                                     & Image (Scrut_Ty) & "'");
                           elsif Arm.Pat.Int_V > Arm.Pat.Range_Hi
                             or else (not Arm.Pat.Range_Incl
                                      and then Arm.Pat.Int_V
                                                 = Arm.Pat.Range_Hi)
                           then
                              Error ("range pattern lower bound exceeds "
                                     & "upper bound (empty range)");
                           end if;
                        when Pat_Variant =>
                           if Natural (Arm.Pat.Path.Length) = 1
                             and then (not Arm.Pat.Bindings.Is_Empty
                                       or else Arm.Pat.Has_Rest)
                           then
                              --  §5.10.2/item(e) plain struct pattern:
                              --  `point { x, y }` against a struct-typed
                              --  scrutinee -- a `{ ... }` clause was given
                              --  (distinguished from the bare-identifier
                              --  catch-all below by carrying bindings or
                              --  `...`), so destructure named fields
                              --  instead of binding the whole value to the
                              --  type name. Recursive `#` sub-patterns
                              --  within the clause are a separate,
                              --  unshipped feature (spec 7.4 item b).
                              declare
                                 SN : constant String :=
                                   SU.To_String (Arm.Pat.Path.First_Element);
                              begin
                                 if Scrut_Ty = null
                                   or else Scrut_Ty.Kind /= T_Named
                                   or else not Kurt.Layout.Is_Struct
                                                 (SU.To_String
                                                    (Scrut_Ty.Name))
                                 then
                                    Error ("struct pattern '" & SN
                                       & "' matched against a non-struct "
                                       & "scrutinee '" & Image (Scrut_Ty)
                                       & "' (spec 5.10.2)");
                                 elsif SN /= SU.To_String (Scrut_Ty.Name) then
                                    Error ("struct pattern names '" & SN
                                       & "' but the scrutinee has type '"
                                       & SU.To_String (Scrut_Ty.Name)
                                       & "' (spec 5.10.2)");
                                 else
                                    if not Arm.Pat.Has_Rest
                                      and then Natural
                                                 (Arm.Pat.Bindings.Length)
                                           /= Kurt.Layout.Struct_Field_Count
                                                (SN)
                                    then
                                       Error ("pattern for struct '" & SN
                                          & "' shall mention every field "
                                          & "or end with `...` "
                                          & "(spec 5.10.2)");
                                    end if;
                                    for K in 1 .. Natural
                                      (Arm.Pat.Bindings.Length)
                                    loop
                                       declare
                                          --  Named-field lookup (rename or
                                          --  shorthand); a nested-pattern
                                          --  slot (both empty) falls back to
                                          --  declaration-order position K.
                                          FName : constant String :=
                                            (if K <= Natural
                                                 (Arm.Pat.Bind_Fields.Length)
                                               and then SU.Length
                                                 (Arm.Pat.Bind_Fields.Element
                                                    (K)) > 0
                                             then SU.To_String
                                               (Arm.Pat.Bind_Fields.Element
                                                  (K))
                                             elsif SU.Length
                                               (Arm.Pat.Bindings.Element (K))
                                               > 0
                                             then SU.To_String
                                               (Arm.Pat.Bindings.Element (K))
                                             else Kurt.Layout.Struct_Field_Name
                                               (SN, K));
                                          FT : constant Type_Access :=
                                            Kurt.Layout.Field_Type
                                              (SN, FName);
                                       begin
                                          if FT = null then
                                             Error ("struct '" & SN
                                                & "' has no field '"
                                                & FName & "' "
                                                & "(spec 5.10.2)");
                                          elsif Kurt.Layout.Field_Is_Airside
                                                  (SN, FName)
                                            and then In_Airside = 0
                                          then
                                             Error ("field '" & FName
                                                & "' of '" & SN
                                                & "' is `airside` -- "
                                                & "binding it requires an "
                                                & "`airside` region "
                                                & "(spec 5.5.1/6.2.2)");
                                          end if;
                                          if K <= Natural
                                               (Arm.Pat.Sub_Pats.Length)
                                            and then Arm.Pat.Sub_Pats.Element
                                                       (K) /= null
                                          then
                                             Bind_Nested
                                               (Arm.Pat.Sub_Pats.Element
                                                  (K).all, FT);
                                          else
                                             Scope.Append
                                               ((Name => Arm.Pat.Bindings
                                                           .Element (K),
                                                 Ty   => FT, others => <>));
                                          end if;
                                       end;
                                    end loop;
                                 end if;
                              end;
                              --  §5.10.4: a struct pattern mentioning every
                              --  field, with the only sub-pattern kind this
                              --  bootstrap subset parses in this position
                              --  (plain bind/rename, always irrefutable),
                              --  is itself irrefutable -- it covers the
                              --  match like a bare identifier.
                              if Arm.Guard = null then
                                 Has_Wild := True;
                              end if;
                           elsif Natural (Arm.Pat.Path.Length) = 1 then
                              --  §5.10.1 a bare identifier is an irrefutable
                              --  binding (catch-all): bind the scrutinee
                              --  value to the name. Per §7.4.1 it makes the
                              --  match exhaustive EXCEPT over an enum with
                              --  no declared `#wild#` (which requires an
                              --  explicit `#wild#` arm).
                              Scope.Append
                                ((Name => Arm.Pat.Path.First_Element,
                                  Ty   => Scrut_Ty, others => <>));
                              if Arm.Guard = null
                                and then
                                  (not Is_Enum_Scrut
                                   or else Kurt.Layout.Has_Wild_Variant
                                             (SU.To_String (Scrut_Ty.Name)))
                              then
                                 Has_Wild := True;
                              end if;
                           elsif Is_Enum_Scrut
                             and then Natural (Arm.Pat.Path.Length) = 2
                           then
                              declare
                                 EN : constant String :=
                                   SU.To_String (Scrut_Ty.Name);
                                 VN : constant String := SU.To_String
                                   (Arm.Pat.Path.Last_Element);
                              begin
                                 if not Kurt.Layout.Has_Variant (EN, VN)
                                 then
                                    Error ("enum '" & EN
                                      & "' has no variant '" & VN & "'");
                                 else
                                    --  §5.10.2 field coverage.
                                    Check_Payload_Coverage
                                      (Arm.Pat, EN, VN);
                                    --  Bind payload fields positionally
                                    --  for the arm body's scope.
                                    for K in 1 .. Natural
                                      (Arm.Pat.Bindings.Length)
                                    loop
                                       --  §5.5.1/§5.7: a payload field
                                       --  carrying `airside` is readable
                                       --  only inside an `airside` region
                                       --  — binding it out of one is
                                       --  already the access.
                                       if Kurt.Layout.Variant_Field_Is_Airside
                                            (EN, VN, K)
                                         and then In_Airside = 0
                                       then
                                          Error ("payload field '"
                                            & Kurt.Layout.Variant_Field_Name
                                                (EN, VN, K)
                                            & "' of '" & EN & "::" & VN
                                            & "' is `airside` -- binding it "
                                            & "requires an `airside` region "
                                            & "(spec 5.5.1/6.2.2)");
                                       end if;
                                       --  §7.4 item(a): a slot written as a
                                       --  nested pattern recurses instead of
                                       --  binding a plain name at this level.
                                       if K <= Natural
                                            (Arm.Pat.Sub_Pats.Length)
                                         and then Arm.Pat.Sub_Pats.Element (K)
                                                    /= null
                                       then
                                          Bind_Nested
                                            (Arm.Pat.Sub_Pats.Element (K).all,
                                             Pat_Field_Ty
                                               (Arm.Pat, Scrut_Ty, VN, K));
                                       else
                                          Scope.Append
                                            ((Name => Arm.Pat.Bindings.Element
                                                        (K),
                                              Ty   => Pat_Field_Ty
                                                (Arm.Pat, Scrut_Ty, VN, K),
                                              others => <>));
                                       end if;
                                    end loop;
                                 end if;
                              end;
                           else
                              Error ("variant pattern requires an enum "
                                     & "scrutinee");
                           end if;
                        when Pat_Slice =>
                           --  §7.4.2 slice pattern: the scrutinee shall be
                           --  an array; each bind names an element.
                           if Scrut_Ty = null
                             or else Scrut_Ty.Kind /= T_Array
                           then
                              Error ("slice pattern requires an array "
                                     & "scrutinee, got '"
                                     & Image (Scrut_Ty) & "'");
                           elsif Arm.Pat.From_String
                             and then
                               (Scrut_Ty.Elem = null
                                or else Scrut_Ty.Elem.Kind /= T_Named
                                or else SU.To_String (Scrut_Ty.Elem.Name)
                                          /= "ui1")
                           then
                              --  §7.4.2: a string-literal pattern denotes a
                              --  sequence of `ui1` cells; it is legal only
                              --  against a `ui1`-element scrutinee
                              --  (`[ui1; N]` family).
                              Error ("a string-literal pattern requires a "
                                     & "`ui1`-element scrutinee, got '"
                                     & Image (Scrut_Ty) & "' (spec 7.4.2)");
                           else
                              declare
                                 Rests    : Natural := 0;
                                 Has_Lit  : Boolean := False;  --  item(f)
                              begin
                                 for K in Arm.Pat.Slice_Elems.First_Index ..
                                          Arm.Pat.Slice_Elems.Last_Index
                                 loop
                                    declare
                                       SE : constant Slice_Elem :=
                                         Arm.Pat.Slice_Elems.Element (K);
                                    begin
                                       if SE.Kind = SE_Rest then
                                          Rests := Rests + 1;
                                       elsif SE.Kind = SE_Bind then
                                          Scope.Append
                                            ((Name => SE.Name,
                                              Ty   => Scrut_Ty.Elem,
                                              others => <>));
                                       elsif SE.Kind = SE_Int then
                                          Has_Lit := True;
                                       end if;
                                    end;
                                 end loop;
                                 if Rests > 1 then
                                    Error ("a slice pattern may contain at "
                                       & "most one `...` (spec 7.4.2)");
                                 end if;
                                 --  §5.10.4/§7.4.2 item(f): `[...]` alone is
                                 --  irrefutable for any slice/array. A
                                 --  fixed-length pattern (no `...`) is
                                 --  irrefutable when the scrutinee is a
                                 --  fixed-size array whose length equals the
                                 --  pattern length -- conservatively (for
                                 --  runtime soundness) only when every
                                 --  element is a plain bind/`#wild#`, since
                                 --  an embedded literal can still fail to
                                 --  match at execution time.
                                 if Arm.Guard = null and then Scrut_Ty.Len > 0
                                 then
                                    if Rests = 1
                                      and then Natural
                                                 (Arm.Pat.Slice_Elems.Length)
                                           = 1
                                    then
                                       Has_Wild := True;
                                    elsif Rests = 0 and then not Has_Lit
                                      and then Cell_Count
                                                 (Arm.Pat.Slice_Elems.Length)
                                           = Scrut_Ty.Len
                                    then
                                       Has_Wild := True;
                                    end if;
                                 end if;
                              end;
                           end if;
                     end case;

                     --  §5.10 binding pattern `name # sub`: bind the
                     --  scrutinee value to `name` for the arm (and guard).
                     if SU.Length (Arm.Pat.Bind_Name) > 0 then
                        Scope.Append
                          ((Name => Arm.Pat.Bind_Name,
                            Ty   => Scrut_Ty, others => <>));
                     end if;

                     --  §5.10.1: all alternatives of an or-pattern shall
                     --  bind the same names at the same types. Compare
                     --  this alternative's bindings (the Scope slice it
                     --  appended) against the previous alternative of the
                     --  same arm; then record them for the next one.
                     declare
                        N : constant Natural := Natural (Scope.Length);
                     begin
                        if Arm.Arm_Body = Prev_Body then
                           if N - Saved /= Natural (Prev_Names.Length) then
                              Error ("the alternatives of an or-pattern "
                                     & "bind differing sets of names "
                                     & "(spec 5.10.1)");
                           else
                              for K in Saved + 1 .. N loop
                                 declare
                                    Nm    : constant String := SU.To_String
                                      (Scope.Element (K).Name);
                                    Found : Boolean := False;
                                 begin
                                    for J in Prev_Names.First_Index ..
                                             Prev_Names.Last_Index
                                    loop
                                       if SU.To_String
                                            (Prev_Names.Element (J)) = Nm
                                       then
                                          Found := True;
                                          if not Same_Type
                                            (Prev_Tys.Element (J),
                                             Scope.Element (K).Ty)
                                          then
                                             Error ("or-pattern binding '"
                                               & Nm & "' has differing "
                                               & "types across "
                                               & "alternatives: '"
                                               & Image
                                                   (Prev_Tys.Element (J))
                                               & "' vs '"
                                               & Image
                                                   (Scope.Element (K).Ty)
                                               & "' (spec 5.10.1)");
                                          end if;
                                       end if;
                                    end loop;
                                    if not Found then
                                       Error ("or-pattern binding '" & Nm
                                         & "' is not bound by every "
                                         & "alternative (spec 5.10.1)");
                                    end if;
                                 end;
                              end loop;
                           end if;
                        else
                           Prev_Body := Arm.Arm_Body;
                           Prev_Names.Clear;
                           Prev_Tys.Clear;
                           for K in Saved + 1 .. N loop
                              Prev_Names.Append (Scope.Element (K).Name);
                              Prev_Tys.Append (Scope.Element (K).Ty);
                           end loop;
                        end if;
                     end;

                     --  §7.4: a guard clause is type-checked in the arm's
                     --  pattern-binding scope and shall satisfy `contract`.
                     if Arm.Guard /= null then
                        declare
                           GT : constant Type_Access :=
                             Infer (Arm.Guard, Mk_Named ("bool"));
                        begin
                           if not Is_Contract_Ty (GT) then
                              Error ("match guard must satisfy `contract`, "
                                     & "got '" & Image (GT) & "'");
                           end if;
                        end;
                     end if;

                     BT := Infer (Arm.Arm_Body, Result);

                     --  Pop payload bindings introduced by this arm.
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;

                     --  §7.11: a diverging arm contributes no type to the
                     --  unification; the result comes from the live arms.
                     if not Is_Never_Ty (BT) then
                        Any_Live := True;
                        if Result = null or else Is_Never_Ty (Result) then
                           Result := BT;
                        elsif not Same_Type (Result, BT) then
                           Error ("match arms have differing types: '"
                                  & Image (Result) & "' vs '"
                                  & Image (BT) & "'");
                        end if;
                        --  §8.8.2/§5.2: fold this live arm's post-body
                        --  Moved/Init_States into the running join.
                        if not Any_Live_Arm then
                           Combined_Init := Init_States;
                           Union_Moved   := Moved;
                           Any_Live_Arm  := True;
                        else
                           for M of Moved loop
                              declare
                                 Found : Boolean := False;
                              begin
                                 for N of Union_Moved loop
                                    if SU.To_String (N.Name)
                                         = SU.To_String (M.Name)
                                    then
                                       Found := True;
                                    end if;
                                 end loop;
                                 if not Found then
                                    Union_Moved.Append (M);
                                 end if;
                              end;
                           end loop;
                           for K in Combined_Init.First_Index ..
                                    Combined_Init.Last_Index
                           loop
                              declare
                                 Nm : constant String := SU.To_String
                                   (Combined_Init.Element (K).Name);
                                 Cur_St : constant Init_State :=
                                   Combined_Init.Element (K).State;
                                 Arm_St : Init_State := Cur_St;
                              begin
                                 for J of Init_States loop
                                    if SU.To_String (J.Name) = Nm then
                                       Arm_St := J.State;
                                    end if;
                                 end loop;
                                 if Arm_St /= Cur_St then
                                    declare
                                       IB : Init_Bind :=
                                         Combined_Init.Element (K);
                                    begin
                                       IB.State := St_Maybe;
                                       Combined_Init.Replace_Element (K, IB);
                                    end;
                                 end if;
                              end;
                           end loop;
                        end if;
                     end if;
                     --  Each arm starts fresh from the pre-match state.
                     Init_States := Init_Pre;
                     Moved       := Moved_Pre;
                  end;
               end loop;
               --  §5.2/§8.8.2: install the join across every live arm (or
               --  the pre-match snapshot, if none is live -- the match
               --  itself diverges, so the state is moot either way).
               if Any_Live_Arm then
                  Init_States := Combined_Init;
                  Moved       := Union_Moved;
               end if;

               --  Exhaustiveness (§7): a #wild# arm covers everything;
               --  otherwise an enum must list every variant.
               if not Has_Wild then
                  if Is_Enum_Scrut then
                     declare
                        EN : constant String :=
                          SU.To_String (Scrut_Ty.Name);
                     begin
                        --  §4.5 / §7: an enum without a declared
                        --  `#wild#` variant has discriminant patterns
                        --  beyond its named variants, so a `#wild#`
                        --  arm is mandatory even when every variant is
                        --  listed. Only an enum that declares its own
                        --  `#wild#` variant is exhaustible by listing.
                        if not Kurt.Layout.Has_Wild_Variant (EN) then
                           Error ("non-exhaustive match: enum '" & EN
                                  & "' declares no #wild# variant, so a "
                                  & "#wild# arm is required");
                        else
                           for K in 1 .. Kurt.Layout.Variant_Count (EN)
                           loop
                              declare
                                 VN : constant String :=
                                   Kurt.Layout.Variant_Name (EN, K);
                                 Found : Boolean := False;
                              begin
                                 for I in E.M_Arms.First_Index ..
                                          E.M_Arms.Last_Index
                                 loop
                                    if E.M_Arms.Element (I).Pat.Kind
                                         = Pat_Variant
                                      and then E.M_Arms.Element (I).Guard
                                                 = null
                                      and then SU.To_String
                                        (E.M_Arms.Element (I).Pat.Path
                                           .Last_Element) = VN
                                    then
                                       Found := True;
                                    end if;
                                 end loop;
                                 if not Found then
                                    Error ("non-exhaustive match: enum '"
                                           & EN & "' variant '" & VN
                                           & "' is not covered");
                                 end if;
                              end;
                           end loop;
                        end if;
                     end;
                  else
                     Error ("non-exhaustive match (a #wild# arm is "
                            & "required for this scrutinee)");
                  end if;
               end if;

               --  §7.11: when every arm diverges, the match itself is a
               --  diverging expression of type `never`.
               if not Any_Live then
                  E.Sem_Ty := Mk_Named ("never");
               else
                  E.Sem_Ty := Result;
               end if;
               return E.Sem_Ty;
            end;

   end Infer_Match;
