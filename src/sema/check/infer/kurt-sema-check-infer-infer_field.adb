separate (Kurt.Sema.Check.Infer)
   function Infer_Field return Type_Access is
   begin
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
                  --  Fat-pointer view (§8.1.4): `.ptr` is %elem.
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
                     --  §5.5.1/§6.2.2: an `airside` field (load OR store) is
                     --  permitted only inside an `airside` region.
                     elsif Kurt.Layout.Field_Is_Airside
                             (SU.To_String (RTD.Name), FN)
                       and then In_Airside = 0
                     then
                        Error ("field '" & FN & "' of '"
                               & SU.To_String (RTD.Name)
                               & "' is `airside` -- access requires an "
                               & "`airside` region (spec 5.5.1/6.2.2)");
                     --  §6.2.2: a non-`pub` field is accessible only from
                     --  the source unit that declares its struct.
                     elsif not Kurt.Layout.Field_Is_Pub
                             (SU.To_String (RTD.Name), FN)
                       and then not Kurt.Layout.Same_Source_Unit
                             (SU.To_String (RTD.Name),
                              SU.To_String (Cur_Fn_Name))
                     then
                        Error ("field '" & FN & "' of '"
                               & SU.To_String (RTD.Name)
                               & "' is not `pub` -- accessible only within "
                               & "the source unit that declares it "
                               & "(spec 6.2.2)");
                     end if;
                     E.Sem_Ty := FT;
                  end;
               elsif RTD /= null and then RTD.Kind = T_Named
                 and then (for some GS of U.Gen_Structs =>
                             SU.To_String (GS.Name)
                               = SU.To_String (RTD.Name))
               then
                  --  §5.9.2/§9.1: `self`'s type inside a never-
                  --  instantiated impl(...) method template still names
                  --  the bare (still-generic) owner struct -- Kurt.Mono
                  --  lifted it out of U.Structs before Kurt.Layout ever
                  --  registered it, so Kurt.Layout.Is_Struct above always
                  --  answers False for it. Resolve the field directly
                  --  against the preserved template in U.Gen_Structs; a
                  --  field typed by one of the impl's own generic
                  --  parameters (e.g. `a: T`) is returned as-is -- it is
                  --  already in Cur_Generics from Check_Fn.
                  declare
                     Field_Ty : Type_Access := null;
                  begin
                     for GS of U.Gen_Structs loop
                        if SU.To_String (GS.Name) = SU.To_String (RTD.Name)
                        then
                           for FI in GS.Fields.First_Index ..
                                     GS.Fields.Last_Index
                           loop
                              if SU.To_String (GS.Fields.Element (FI).Name)
                                   = FN
                              then
                                 Field_Ty := GS.Fields.Element (FI).Ty;
                              end if;
                           end loop;
                        end if;
                     end loop;
                     if Field_Ty = null then
                        Error ("struct '" & SU.To_String (RTD.Name)
                               & "' has no field '" & FN & "'");
                     end if;
                     E.Sem_Ty := Field_Ty;
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

   end Infer_Field;
