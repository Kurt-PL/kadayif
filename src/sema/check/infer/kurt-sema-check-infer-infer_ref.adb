separate (Kurt.Sema.Check.Infer)
   function Infer_Ref return Type_Access is
   begin
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

   end Infer_Ref;
