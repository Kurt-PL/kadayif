separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Cast is
   begin
         --  §6.8.2 integer↔integer, §6.8.4 float→integer, §6.8.7
         --  enum→discriminant, §6.8.11 reinterpret. (int→float / float→float
         --  produce float results and are handled by Lower_Float_Into_D.)

         --  §8.1.3 reference cast: a sigil/modifier conversion preserves
         --  the address bits (and uaddr ↔ &raw is the same machine word),
         --  so the value is simply moved into the target register. Fat
         --  references are not part of the cast chain, so 8 bytes suffice.
         declare
            function Is_Ref_Or_Uaddr (T : Type_Access) return Boolean is
              (Is_Ref (T)
               or else (T /= null and then T.Kind = T_Named
                        and then SU.To_String (T.Name) = "uaddr"));
            Src_T : constant Type_Access := Type_Of_Expr (E.Cast_Inner, ST);
         begin
            if not E.Cast_Bang and then not E.Cast_Disc
              and then Is_Ref_Or_Uaddr (E.Cast_Ty)
              and then Is_Ref_Or_Uaddr (Src_T)
              and then (Is_Ref (E.Cast_Ty) or else Is_Ref (Src_T))
            then
               Lower_Expr_Into_Reg (F, E.Cast_Inner, Target_Reg, ST);
               return;
            end if;
         end;

         if Is_Float (Type_Of_Expr (E.Cast_Inner, ST)) then
            declare
               Src_T : constant Type_Access :=
                 Type_Of_Expr (E.Cast_Inner, ST);
               SrcW  : constant Boolean := Sizeof (Src_T) = 8;  --  d vs s
               DstW  : constant Boolean := Sizeof (E.Cast_Ty) = 8;
            begin
               Lower_Float_Into_D (F, E.Cast_Inner, 0, ST);
               if E.Cast_Bang then
                  --  §6.8.11: reinterpret FP bits as the integer.
                  IO.Put_Line (F, "    fmov    "
                    & (if DstW then Xreg else Wreg) & ", "
                    & (if SrcW then "d0" else "s0"));
               else
                  --  §6.8.4 float → integer: truncate toward zero, saturating.
                  --  arm64 fcvtzs/fcvtzu already implement the required
                  --  boundary behaviour exactly — finite in range: trunc-zero;
                  --  above max → max; below min → min; +Inf → max;
                  --  -Inf → min (0 for unsigned); NaN → 0 (regardless of sign).
                  declare
                     Rt  : constant String := (if DstW then Xreg else Wreg);
                     Fp  : constant String := (if SrcW then "d0" else "s0");
                     Sgn : constant Boolean := Is_Signed_Int (E.Cast_Ty);
                  begin
                     IO.Put_Line
                       (F, "    " & (if Sgn then "fcvtzs" else "fcvtzu")
                           & "  " & Rt & ", " & Fp);
                  end;
               end if;
            end;
            return;
         end if;
         Lower_Expr_Into_Reg (F, E.Cast_Inner, Target_Reg, ST);
         declare
            Src_T : constant Type_Access := Type_Of_Expr (E.Cast_Inner, ST);
            Src_Is_Enum : constant Boolean :=
              Src_T /= null and then Src_T.Kind = T_Named
              and then Kurt.Layout.Is_Enum (SU.To_String (Src_T.Name));
            Eff_Sz     : Natural;
            Eff_Signed : Boolean;
         begin
            if Src_Is_Enum then
               --  Extract the discriminant at offset 0; mask away any
               --  payload carried in the high bytes. Signedness follows
               --  the chosen discriminant type (§4.11.3).
               declare
                  DS : constant Natural :=
                    Kurt.Layout.Enum_Disc_Size (SU.To_String (Src_T.Name));
               begin
                  Emit_Int_Conv (8, False, DS);
                  Eff_Sz     := DS;
                  Eff_Signed := Kurt.Layout.Enum_Disc_Signed
                                  (SU.To_String (Src_T.Name));
               end;
            else
               Eff_Sz     := Sizeof (Src_T);
               Eff_Signed := Is_Signed_Int (Src_T);
            end if;

            --  `as ?` stops at the discriminant; `as T` converts on.
            if not E.Cast_Disc then
               Emit_Int_Conv (Eff_Sz, Eff_Signed, Sizeof (E.Cast_Ty));
            end if;
         end;

   end Lower_Cast;
