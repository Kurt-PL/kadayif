separate (Kurt.Sema.Check.Infer)
   function Infer_Binary return Type_Access is
   begin
            case E.B_Op is
               when B_Add | B_Sub | B_Mul | B_Div | B_Mod
                  | B_Sat_Add | B_Sat_Sub | B_Sat_Mul | B_Sat_Div
                  | B_And | B_Or | B_Xor | B_Shl | B_Shr =>
                  declare
                     LT : constant Type_Access :=
                       Infer (E.B_Lhs, Expected);
                     RT : Type_Access;
                  begin
                     --  §6.5 `^` is the bitwise XOR (integer operands);
                     --  contract XOR is the distinct `^^` (B_LXor) below.
                     --  §5.9.2 type erasure: arithmetic on a generic
                     --  parameter needs an arithmetic bound, checked
                     --  here on the template — instantiations that
                     --  would individually succeed do not make the
                     --  template legal.
                     if Is_Generic_Param_Ty (LT)
                       and then not Generic_Arith_OK (LT)
                     then
                        Error ("unconstrained parameter '" & Image (LT)
                               & "' is an opaque layout -- arithmetic "
                               & "requires a numeric/integer/primitive "
                               & "bound (spec 5.9)");
                     end if;
                     --  §6.4.2 saturating and §6.5 bitwise/shift operators
                     --  require integer operands; a float lead is a TF (and
                     --  would otherwise reach an unsupported codegen path).
                     if LT /= null and then Is_Float_Type (LT)
                       and then (E.B_Op in B_Sat_Add | B_Sat_Sub
                                   | B_Sat_Mul | B_Sat_Div
                                   | B_And | B_Or | B_Xor | B_Shl | B_Shr)
                     then
                        Error ((if E.B_Op in B_Sat_Add | B_Sat_Sub
                                  | B_Sat_Mul | B_Sat_Div
                                then "saturating" else "bitwise/shift")
                               & " operator requires an integer operand, "
                               & "got float '" & Image (LT)
                               & "' (spec 6.4.2 / 6.5)");
                     end if;
                     --  §6.5 the bitwise `&`/`|`/`^` require operands
                     --  satisfying `integer`. A concrete non-integer lead
                     --  (e.g. a `contract` type) is a TF — contract XOR is
                     --  the distinct `^^`. Generic parameters are checked
                     --  against their bound above (§5.9.2).
                     if LT /= null
                       and then E.B_Op in B_And | B_Or | B_Xor
                       and then not Is_Generic_Param_Ty (LT)
                       and then not Is_Integer_Type (LT)
                     then
                        Error ("bitwise operator requires operands "
                               & "satisfying `integer`, got '" & Image (LT)
                               & "'"
                               & (if E.B_Op = B_Xor and then
                                     Is_Contract_Ty (LT)
                                  then "; contract XOR is `^^`" else "")
                               & " (spec 6.5)");
                     end if;
                     --  Steer a literal rhs toward the lhs type, but
                     --  not when lhs is a reference (§8.6.4 raw
                     --  reference arithmetic: lead &raw T, follow uaddr).
                     if Is_Ref (LT) then
                        RT := Infer (E.B_Rhs, Mk_Named ("uaddr"));
                        if LT.Sigil /= R_Raw then
                           Error ("reference arithmetic requires a "
                                  & "`&raw` family lead operand, got '"
                                  & Image (LT) & "' (spec 8.6.4)");
                        elsif E.B_Op /= B_Add and then E.B_Op /= B_Sub
                        then
                           Error ("only '+' and '-' accept a reference "
                                  & "lead operand (spec 8.6.4)");
                        elsif RT /= null
                          and then not Is_Integer_Type (RT)
                        then
                           Error ("reference arithmetic follow operand "
                                  & "must be 'uaddr', got '" & Image (RT)
                                  & "' (spec 8.6.4)");
                        end if;
                        E.Sem_Ty := LT;       --  modifiers preserved
                     else
                        if E.B_Op in B_Shl | B_Shr then
                           --  §6.5: the shift count satisfies `primitive`
                           --  (unsigned) and has the same size as the
                           --  lead — so an unsuffixed literal count takes
                           --  the unsigned type of the lead's size.
                           RT := Infer
                             (E.B_Rhs,
                              (if LT = null then null
                               else Unsigned_Of_Size
                                 (Kurt.Layout.Size_Of (LT))));
                           if LT /= null and then RT /= null then
                              if not Is_Unsigned_Int_Type (RT) then
                                 Error ("shift count must satisfy "
                                        & "`primitive` (unsigned); got '"
                                        & Image (RT) & "' (spec 6.5)");
                              elsif Kurt.Layout.Size_Of (LT)
                                    /= Kurt.Layout.Size_Of (RT)
                              then
                                 Error ("shift operands must have the "
                                        & "same size; got '" & Image (LT)
                                        & "' and '" & Image (RT)
                                        & "' (spec 6.5)");
                              end if;
                           end if;
                        else
                           RT := Infer (E.B_Rhs, LT);
                           if LT /= null and then RT /= null
                             and then not Same_Type (LT, RT)
                           then
                              --  §6.4/§6.5: both operands of a binary
                              --  arithmetic / bitwise operator shall be
                              --  the same type T.
                              Error ("operands of a binary arithmetic "
                                     & "operator must be the same type; "
                                     & "got '" & Image (LT) & "' and '"
                                     & Image (RT) & "' (spec 6.4)");
                           end if;
                        end if;
                        E.Sem_Ty := LT;
                     end if;
                     return E.Sem_Ty;
                  end;

               when B_Wide_Add | B_Wide_Mul =>
                  --  §6.4.3: result is the anonymous tuple .{T, T}.
                  declare
                     LT : constant Type_Access := Infer (E.B_Lhs, null);
                     RT : constant Type_Access := Infer (E.B_Rhs, LT);
                     Tup : constant Type_Access :=
                       new AST_Type (Kind => T_Tuple);
                     pragma Unreferenced (RT);
                  begin
                     if LT /= null and then not Is_Integer_Type (LT) then
                        Error ("widening operator requires an integer "
                               & "operand, got '" & Image (LT) & "'");
                     end if;
                     Tup.Elems.Append (LT);
                     Tup.Elems.Append (LT);
                     E.Sem_Ty := Tup;
                     return E.Sem_Ty;
                  end;

               when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge =>
                  declare
                     LT : constant Type_Access := Infer (E.B_Lhs, null);
                     RT : constant Type_Access := Infer (E.B_Rhs, LT);
                  begin
                     --  §6.6: both operands of a comparison shall be the
                     --  same type; different numeric types shall not be
                     --  compared without an explicit `as` cast.
                     if LT /= null and then RT /= null
                       and then not Same_Type (LT, RT)
                     then
                        Error ("operands of a comparison must be the "
                               & "same type; got '" & Image (LT)
                               & "' and '" & Image (RT) & "' (spec 6.6)");
                     end if;
                     --  §5.9.2 type erasure: comparison on a generic
                     --  parameter also needs an arithmetic bound.
                     if Is_Generic_Param_Ty (LT)
                       and then not Generic_Arith_OK (LT)
                     then
                        Error ("unconstrained parameter '" & Image (LT)
                               & "' is an opaque layout -- comparison "
                               & "requires a numeric/integer/primitive "
                               & "bound (spec 5.9)");
                     end if;
                     --  §6.6: enums do not satisfy `numeric` and cannot
                     --  be compared with == != < > <= >= (bool is a
                     --  contract enum but only `==`/`!=` are usable
                     --  through contract polarity; the bootstrap accepts
                     --  bool through Is_Integer-like channels for now).
                     if LT /= null and then LT.Kind = T_Named
                       and then Kurt.Layout.Is_Enum (SU.To_String (LT.Name))
                       and then SU.To_String (LT.Name) /= "bool"
                     then
                        Error ("enum type '" & Image (LT)
                               & "' is not numeric -- comparison "
                               & "operators require numeric operands "
                               & "(spec 6.6)");
                     end if;
                     E.Sem_Ty := Mk_Named ("bool");
                     return E.Sem_Ty;
                  end;

               when B_LAnd | B_LOr | B_LXor =>
                  --  §7.2.2 logical operators: each operand satisfies
                  --  `contract`; the result is bool. `&&`/`||` short-
                  --  circuit; `^^` evaluates both. `^^` additionally
                  --  requires `void` success/failure payloads.
                  declare
                     LT  : constant Type_Access := Infer (E.B_Lhs, null);
                     RT  : constant Type_Access := Infer (E.B_Rhs, null);
                     Nm  : constant String :=
                       (case E.B_Op is
                           when B_LAnd => "&&",
                           when B_LOr  => "||",
                           when others => "^^");
                  begin
                     if not Is_Contract_Ty (LT) then
                        Error ("'" & Nm & "' requires operands satisfying "
                               & "`contract`; lhs is '" & Image (LT)
                               & "' (spec 7.2.2)");
                     end if;
                     if not Is_Contract_Ty (RT) then
                        Error ("'" & Nm & "' requires operands satisfying "
                               & "`contract`; rhs is '" & Image (RT)
                               & "' (spec 7.2.2)");
                     end if;
                     if E.B_Op = B_LXor
                       and then not (Contract_Payloads_Void (LT)
                                     and then Contract_Payloads_Void (RT))
                     then
                        Error ("'^^' requires both operands to have `void` "
                               & "success and failure payloads (spec 7.2.2)");
                     end if;
                     E.Sem_Ty := Mk_Named ("bool");
                     return E.Sem_Ty;
                  end;
            end case;

   end Infer_Binary;
