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

   end Infer_Field;
