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
                           if Natural (Arm.Pat.Path.Length) = 1 then
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
                                    --  Bind payload fields positionally
                                    --  for the arm body's scope.
                                    for K in 1 .. Natural
                                      (Arm.Pat.Bindings.Length)
                                    loop
                                       Scope.Append
                                         ((Name => Arm.Pat.Bindings.Element
                                                     (K),
                                           Ty   => Pat_Field_Ty
                                             (Arm.Pat, Scrut_Ty, VN, K),
                                           others => <>));
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
                           else
                              declare
                                 Rests : Natural := 0;
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
                                       end if;
                                    end;
                                 end loop;
                                 if Rests > 1 then
                                    Error ("a slice pattern may contain at "
                                       & "most one `...` (spec 7.4.2)");
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
                     end if;
                  end;
               end loop;

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
