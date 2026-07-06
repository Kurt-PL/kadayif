separate (Kurt.Sema.Check.Infer)
   function Infer_Cast return Type_Access is
   begin
            --  §6.8 cast. Bootstrap scope: integer↔integer (§6.8.2),
            --  enum→discriminant (§6.8.7), integer↔float (§6.8.3-4),
            --  float↔float (§6.8.5), and same-size `as!` reinterpret
            --  (§6.8.11). `as ?` extracts an enum discriminant.
            declare
               Src : constant Type_Access := Infer (E.Cast_Inner, null);
               Src_Is_Enum : constant Boolean :=
                 Src /= null and then Src.Kind = T_Named
                 and then Kurt.Layout.Is_Enum (SU.To_String (Src.Name));
            begin
               if E.Cast_Disc then
                  --  `e as ?` — only permitted on enums.
                  if Src_Is_Enum then
                     declare
                        EN : constant String := SU.To_String (Src.Name);
                        DS : constant Natural :=
                          Kurt.Layout.Enum_Disc_Size (EN);
                     begin
                        if DS = 0 then
                           --  §4.11.3: at most one variant and no
                           --  #wild#(V) — the discriminant type is
                           --  void and carries no value.
                           Error ("`as ?` on enum '" & EN
                                  & "' whose discriminant type is "
                                  & "void (spec 4.11.3)");
                           E.Sem_Ty := Mk_Named ("saddr");
                        else
                           E.Sem_Ty := Mk_Named
                             (Disc_Ty_Name
                                (DS, Kurt.Layout.Enum_Disc_Signed (EN)));
                        end if;
                     end;
                  else
                     Error ("`as ?` requires an enum operand, got '"
                            & Image (Src) & "'");
                     E.Sem_Ty := Mk_Named ("saddr");
                  end if;
               elsif E.Cast_Bang then
                  --  §2.6: `as!` is an airside-only operation.
                  if In_Airside = 0 then
                     Error ("`as!` (bitwise reinterpret) is permitted only "
                            & "in an `airside` region (spec 2.6)");
                  end if;
                  --  §6.8.11: bitwise reinterpret between equal-size types.
                  if Src /= null
                    and then Kurt.Layout.Size_Of (Src)
                               /= Kurt.Layout.Size_Of (E.Cast_Ty)
                  then
                     Error ("`as!` requires equal-size types: '"
                            & Image (Src) & "' and '"
                            & Image (E.Cast_Ty) & "' differ in size");
                  end if;
                  --  §6.8.11/§8.8.2: reinterpreting a value whose type
                  --  satisfies destruct transfers it out of the source
                  --  binding, exactly as an ordinary transfer would --
                  --  the bits now live (bitwise) inside the cast result,
                  --  so the original binding shall not be read again.
                  --  Maybe_Move is a no-op unless the operand is a bare
                  --  binding path of a destruct-satisfying type.
                  Maybe_Move (E.Cast_Inner);
                  E.Sem_Ty := E.Cast_Ty;
               elsif (Src /= null and then Src.Kind = T_Fn)
                 or else (E.Cast_Ty /= null and then E.Cast_Ty.Kind = T_Fn)
               then
                  --  §4.10: `as` shall not apply to or from a subroutine
                  --  pointer; conversions go through `as!` in an airside
                  --  block.
                  Error ("`as` shall not convert to or from a subroutine "
                         & "pointer ('" & Image (Src) & "' as '"
                         & Image (E.Cast_Ty)
                         & "'); use `as!` in an airside block (spec 4.10)");
                  E.Sem_Ty := E.Cast_Ty;
               elsif (Is_Ref (E.Cast_Ty) or else Is_Uaddr (E.Cast_Ty))
                 and then (Is_Ref (Src) or else Is_Uaddr (Src))
                 and then not (Is_Uaddr (E.Cast_Ty) and then Is_Uaddr (Src))
               then
                  --  §8.1.3 reference cast (sigil/modifier conversion).
                  declare
                     Outcome : constant Natural :=
                       Ref_Cast_Outcome (Src, E.Cast_Ty);
                  begin
                     if Outcome = 2 then
                        Error ("reference cast '" & Image (Src)
                               & "' as '" & Image (E.Cast_Ty)
                               & "' is not permitted (spec 8.1.3)");
                     elsif Outcome = 1 and then In_Airside = 0 then
                        --  §8.1.3: an ascending cast `&raw T` -> a managed
                        --  reference (`&T`/`&mut T`/`$T`) begins lifetime
                        --  tracking on an asserted referent and is
                        --  permitted only in an `airside` region.
                        Error ("ascending cast from '" & Image (Src)
                               & "' to a managed reference is permitted "
                               & "only in an `airside` region (spec 8.1.3)");
                     end if;
                     E.Sem_Ty := E.Cast_Ty;
                  end;
               elsif Is_Integer_Type (E.Cast_Ty) then
                  --  §5.9.2 erasure: a source that is an (unbounded)
                  --  generic parameter cannot be checked against a
                  --  concrete numeric type without knowing which
                  --  concrete type it names -- whether the cast is
                  --  actually valid is necessarily a per-instantiation
                  --  question (every generated instance is independently
                  --  checked when Kurt.Mono copies it into U.Fns), not
                  --  one the abstract template can answer.
                  if not (Is_Integer_Type (Src) or else Src_Is_Enum
                          or else Is_Float_Type (Src)
                          or else Is_Generic_Param_Ty (Src))
                  then
                     Error ("cannot cast '" & Image (Src)
                            & "' to integer type '"
                            & Image (E.Cast_Ty) & "'");
                  elsif Src_Is_Enum
                    and then Kurt.Layout.Enum_Disc_Size
                               (SU.To_String (Src.Name)) = 0
                  then
                     Error ("cannot cast enum '"
                            & SU.To_String (Src.Name)
                            & "' whose discriminant type is void "
                            & "(spec 4.11.3)");
                  end if;
                  E.Sem_Ty := E.Cast_Ty;
               elsif Is_Float_Type (E.Cast_Ty) then
                  if not (Is_Integer_Type (Src) or else Is_Float_Type (Src)
                          or else Is_Generic_Param_Ty (Src))
                  then
                     Error ("cannot cast '" & Image (Src)
                            & "' to float type '"
                            & Image (E.Cast_Ty) & "'");
                  end if;
                  E.Sem_Ty := E.Cast_Ty;
               else
                  Error ("unsupported cast target '"
                         & Image (E.Cast_Ty) & "'");
                  E.Sem_Ty := E.Cast_Ty;
               end if;
               return E.Sem_Ty;
            end;

   end Infer_Cast;
