separate (Kurt.Sema.Check.Infer)
   function Infer_Struct_Lit return Type_Access is
   begin
            declare
               --  The literal's `Name {` may be a generic template
               --  name (`Box`); the actual concrete struct comes from
               --  the expected type (`Box$si4`) after monomorphisation.
               SN : constant String :=
                 (if Expected /= null and then Expected.Kind = T_Named
                     and then Kurt.Layout.Is_Struct
                                (SU.To_String (Expected.Name))
                  then SU.To_String (Expected.Name)
                  else SU.To_String (E.SL_Name));
            begin
               if not Kurt.Layout.Is_Struct (SN) then
                  Error ("unknown struct type '" & SN & "'");
               else
                  for I in E.SL_Fields.First_Index ..
                           E.SL_Fields.Last_Index
                  loop
                     declare
                        FI : constant Field_Init :=
                          E.SL_Fields.Element (I);
                        FT : constant Type_Access :=
                          Kurt.Layout.Field_Type
                            (SN, SU.To_String (FI.Name));
                        VT : Type_Access;
                     begin
                        --  §6.1.4 a field shall not be initialised twice.
                        for J in E.SL_Fields.First_Index .. I - 1 loop
                           if SU.To_String (E.SL_Fields.Element (J).Name)
                                = SU.To_String (FI.Name)
                           then
                              Error ("field '" & SU.To_String (FI.Name)
                                     & "' of '" & SN & "' is initialised "
                                     & "more than once (spec 6.1.4)");
                           end if;
                        end loop;
                        if FT = null then
                           Error ("struct '" & SN & "' has no field '"
                                  & SU.To_String (FI.Name) & "'");
                        end if;
                        VT := Infer (FI.Val, FT);
                        if FT /= null and then not Assignable (FT, VT) then
                           Error ("field '" & SU.To_String (FI.Name)
                                  & "' of '" & SN & "': expected '"
                                  & Image (FT) & "' but got '"
                                  & Image (VT) & "'");
                        end if;
                        --  §8.8.2 aggregate field init from a binding is a
                        --  transfer when the field type satisfies destruct.
                        Maybe_Move (FI.Val);
                     end;
                  end loop;

                  --  §5.5.3: every declared field shall be either supplied
                  --  by the literal or carry a default-value expression.
                  for K in 1 .. Kurt.Layout.Struct_Field_Count (SN) loop
                     declare
                        FN : constant String :=
                          Kurt.Layout.Struct_Field_Name (SN, K);
                        Supplied : Boolean := False;
                     begin
                        for I in E.SL_Fields.First_Index ..
                                 E.SL_Fields.Last_Index
                        loop
                           if SU.To_String (E.SL_Fields.Element (I).Name)
                                = FN
                           then
                              Supplied := True;
                           end if;
                        end loop;
                        --  §5.5.2 `?` padding fields are auto-zeroed and
                        --  never supplied; exempt them from the rule.
                        if FN /= "?"
                          and then not Supplied
                          and then Kurt.Layout.Field_Default (SN, FN) = null
                        then
                           Error ("struct literal of '" & SN
                                  & "' omits field '" & FN
                                  & "' which has no default (spec 5.5.3)");
                        end if;
                     end;
                  end loop;
               end if;
               E.Sem_Ty := Mk_Named (SN);
               return E.Sem_Ty;
            end;

   end Infer_Struct_Lit;
