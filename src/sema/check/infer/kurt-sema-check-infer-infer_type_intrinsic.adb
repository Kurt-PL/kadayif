separate (Kurt.Sema.Check.Infer)
   function Infer_Type_Intrinsic return Type_Access is
   begin
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

   end Infer_Type_Intrinsic;
