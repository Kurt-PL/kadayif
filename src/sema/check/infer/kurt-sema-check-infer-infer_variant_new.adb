separate (Kurt.Sema.Check.Infer)
   function Infer_Variant_New return Type_Access is
   begin
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

   end Infer_Variant_New;
