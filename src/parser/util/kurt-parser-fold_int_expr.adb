separate (Kurt.Parser)
   function Fold_Int_Expr
     (U     : Translation_Unit;
      E     : Expr_Access;
      Value : out Long_Long_Integer) return Boolean
   is
      --  Bitwise/shift operators (§6.5) are not predefined on a signed
      --  integer type in Ada; reinterpret through a 64-bit modular type
      --  (matches the pattern already used for static-initializer bit
      --  patterns in Kurt.Codegen.Emit).
      function To_Unsigned is new Ada.Unchecked_Conversion
        (Long_Long_Integer, Interfaces.Unsigned_64);
      function To_Signed is new Ada.Unchecked_Conversion
        (Interfaces.Unsigned_64, Long_Long_Integer);

      --  §6.10: recursion through const references is "bounded by an
      --  implementation defined evaluation limit" -- this bootstrap picks
      --  a small fixed depth so a cyclic const definition (`const A: si4 =
      --  A;`) fails translation cleanly instead of looping/crashing.
      Max_Depth : constant := 64;

      function Fold (E : Expr_Access; Depth : Natural) return Boolean is
      begin
         Value := 0;
         if E = null or else Depth > Max_Depth then
            return False;
         end if;
         case E.Kind is
            when E_Int_Lit =>
               Value := E.Int_V;
               return True;

            when E_Unary =>
               if E.U_Op /= U_Neg then
                  return False;   --  bitwise-not (`!`) not in the fold set
               end if;
               declare
                  V : Long_Long_Integer;
               begin
                  if not Fold (E.U_Operand, Depth + 1) then
                     return False;
                  end if;
                  V := Value;
                  Value := -V;
                  return True;
               end;

            when E_Binary =>
               declare
                  L, R : Long_Long_Integer;
               begin
                  if not Fold (E.B_Lhs, Depth + 1) then
                     return False;
                  end if;
                  L := Value;
                  if not Fold (E.B_Rhs, Depth + 1) then
                     return False;
                  end if;
                  R := Value;
                  case E.B_Op is
                     when B_Add => Value := L + R;
                     when B_Sub => Value := L - R;
                     when B_Mul => Value := L * R;
                     when B_Div =>
                        if R = 0 then
                           return False;
                        end if;
                        Value := L / R;
                     when B_Mod =>
                        if R = 0 then
                           return False;
                        end if;
                        Value := L rem R;
                     when B_And =>
                        Value := To_Signed
                          (Interfaces."and" (To_Unsigned (L), To_Unsigned (R)));
                     when B_Or =>
                        Value := To_Signed
                          (Interfaces."or" (To_Unsigned (L), To_Unsigned (R)));
                     when B_Xor =>
                        Value := To_Signed
                          (Interfaces."xor" (To_Unsigned (L), To_Unsigned (R)));
                     when B_Shl =>
                        if R not in 0 .. 63 then
                           return False;
                        end if;
                        Value := To_Signed
                          (Interfaces.Shift_Left
                             (To_Unsigned (L), Natural (R)));
                     when B_Shr =>
                        if R not in 0 .. 63 then
                           return False;
                        end if;
                        Value := To_Signed
                          (Interfaces.Shift_Right
                             (To_Unsigned (L), Natural (R)));
                     when others =>
                        --  Comparison/logical/saturating/widening operators
                        --  are outside the §5.3/§5.4/§4.7 small-integer
                        --  fold set (bootstrap subset).
                        return False;
                  end case;
                  return True;
               end;

            when E_Path =>
               --  §5.3: a single-segment path naming a top-level integer
               --  `const` folds to that const's own (recursively folded)
               --  initializer value.
               if Natural (E.Segments.Length) /= 1 then
                  return False;
               end if;
               for I in U.Consts.First_Index .. U.Consts.Last_Index loop
                  if SU."=" (U.Consts.Element (I).Name,
                             E.Segments.Last_Element)
                  then
                     return Fold (U.Consts.Element (I).Init, Depth + 1);
                  end if;
               end loop;
               return False;

            when others =>
               return False;
         end case;
      end Fold;
   begin
      return Fold (E, 0);
   exception
      when Constraint_Error =>
         --  §4.7/§5.3/§5.4: overflow of the fold's Long_Long_Integer
         --  accumulator, or division/shift edge cases the checks above
         --  did not already catch, is a clean "not foldable" rather than
         --  a propagated Ada exception.
         Value := 0;
         return False;
   end Fold_Int_Expr;
