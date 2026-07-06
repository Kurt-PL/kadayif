separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Binary (E : Expr_Access) is
      Xt : constant String := "x" & Img (Target_Reg);
      Wt : constant String := "w" & Img (Target_Reg);
      Xr : constant String := "x" & Img (Target_Reg + 1);
      Wr : constant String := "w" & Img (Target_Reg + 1);

      Lhs_Ty : constant Type_Access := Type_Of_Expr (E.B_Lhs, ST);
      Use_64 : constant Boolean := Is_Ref (Lhs_Ty)
                                or else Sizeof (Lhs_Ty) > 4;
   begin
      --  §4.4.3 floating-point comparison via the hardware `fcmp`, which
      --  follows ISO/IEC 60559:2020 (unordered → all relational false,
      --  ordered-equal handles ±0). The Kurt deviations are patched on top:
      --    == reflexive over NaN (both-NaN → true);
      --    != false when both NaN;
      --    <= and >= true when both NaN.
      --  <, > need no patch — the ordered conditions (mi/gt) already yield
      --  false on any unordered (NaN) operand.
      if Is_Float (Lhs_Ty)
        and then E.B_Op in B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge
      then
         declare
            W64 : constant Boolean := Sizeof (Lhs_Ty) = 8;
            F0  : constant String := (if W64 then "d0" else "s0");
            F1  : constant String := (if W64 then "d1" else "s1");
            Cnd : constant String :=
              (case E.B_Op is
                  when B_Eq => "eq", when B_Ne => "ne",
                  when B_Lt => "mi", when B_Gt => "gt",
                  when B_Le => "ls", when others => "ge");  --  B_Ge
         begin
            Lower_Float_Into_D (F, E.B_Lhs, 0, ST);
            IO.Put_Line (F, "    sub     sp, sp, #16");
            IO.Put_Line (F, "    str     " & F0 & ", [sp]");
            Lower_Float_Into_D (F, E.B_Rhs, 0, ST);   --  rhs in d0/s0
            IO.Put_Line (F, "    ldr     " & F1 & ", [sp]");  --  lhs in d1/s1
            IO.Put_Line (F, "    add     sp, sp, #16");
            IO.Put_Line (F, "    fcmp    " & F1 & ", " & F0);  --  lhs ? rhs
            IO.Put_Line (F, "    cset    " & Wt & ", " & Cnd);
            if E.B_Op in B_Eq | B_Ne | B_Le | B_Ge then
               --  both-NaN := isnan(lhs) and isnan(rhs); `vs` is the
               --  unordered flag, set by `fcmp x, x` exactly when x is NaN.
               IO.Put_Line (F, "    fcmp    " & F1 & ", " & F1);
               IO.Put_Line (F, "    cset    w14, vs");
               IO.Put_Line (F, "    fcmp    " & F0 & ", " & F0);
               IO.Put_Line (F, "    cset    w15, vs");
               IO.Put_Line (F, "    and     w14, w14, w15");
               if E.B_Op = B_Ne then
                  IO.Put_Line (F, "    bic     " & Wt & ", " & Wt & ", w14");
               else
                  IO.Put_Line (F, "    orr     " & Wt & ", " & Wt & ", w14");
               end if;
            end if;
         end;
         return;
      end if;

      --  §7.2.2 `&&` / `||`: short-circuit — the rhs is evaluated only
      --  when the lhs does not decide the result. Both sides reduce to
      --  truthiness (0/1) so the result is the bool value itself.
      if E.B_Op = B_LAnd or else E.B_Op = B_LOr then
         declare
            FN    : constant String  := SU.To_String (ST.Fn_Name);
            Idx   : constant Natural := ST.If_Idx;
            L_End : constant String  := "Llog_" & FN & "_" & Img (Idx);
         begin
            ST.If_Idx := ST.If_Idx + 1;
            Lower_Expr_Into_Reg (F, E.B_Lhs, Target_Reg, ST);
            Emit_Truthify (F, Target_Reg, Type_Of_Expr (E.B_Lhs, ST));
            IO.Put_Line (F, "    "
              & (if E.B_Op = B_LAnd then "cbz " else "cbnz")
              & "    " & Wt & ", " & L_End);
            Lower_Expr_Into_Reg (F, E.B_Rhs, Target_Reg, ST);
            Emit_Truthify (F, Target_Reg, Type_Of_Expr (E.B_Rhs, ST));
            IO.Put_Line (F, L_End & ":");
         end;
         return;
      end if;

      --  §7.2.2 contract `^^`: both operands evaluated, truthified, then
      --  combined with an integer xor (operands are 0/1).
      if E.B_Op = B_LXor then
         Lower_Expr_Into_Reg (F, E.B_Lhs, Target_Reg, ST);
         Emit_Truthify (F, Target_Reg, Lhs_Ty);
         IO.Put_Line (F, "    sub     sp, sp, #16");
         IO.Put_Line (F, "    str     " & Xt & ", [sp]");
         Lower_Expr_Into_Reg (F, E.B_Rhs, Target_Reg + 1, ST);
         Emit_Truthify (F, Target_Reg + 1, Type_Of_Expr (E.B_Rhs, ST));
         IO.Put_Line (F, "    ldr     " & Xt & ", [sp]");
         IO.Put_Line (F, "    add     sp, sp, #16");
         IO.Put_Line (F, "    eor     " & Wt & ", " & Wt & ", " & Wr);
         return;
      end if;

      Lower_Expr_Into_Reg (F, E.B_Lhs, Target_Reg, ST);
      IO.Put_Line (F, "    sub     sp, sp, #16");
      IO.Put_Line (F, "    str     " & Xt & ", [sp]");
      Lower_Expr_Into_Reg (F, E.B_Rhs, Target_Reg + 1, ST);
      IO.Put_Line (F, "    ldr     " & Xt & ", [sp]");
      IO.Put_Line (F, "    add     sp, sp, #16");

      case E.B_Op is
         when B_Add =>
            if Is_Ref (Lhs_Ty) then
               --  Pointer arithmetic: scale rhs by the referent's size.
               declare
                  Scale : constant Cell_Count := Sizeof (Lhs_Ty.Target);
               begin
                  case Scale is
                     when 1 => null;
                     when 2 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #1");
                     when 4 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #2");
                     when 8 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #3");
                     when others =>
                        IO.Put_Line (F, "    mov     x12, #" & Img (Scale));
                        IO.Put_Line (F, "    mul     " & Xr & ", " & Xr
                                        & ", x12");
                  end case;
                  IO.Put_Line (F, "    add     " & Xt & ", " & Xt
                                  & ", " & Xr);
               end;
            elsif Use_64 then
               IO.Put_Line (F, "    add     " & Xt & ", " & Xt & ", " & Xr);
            else
               IO.Put_Line (F, "    add     " & Wt & ", " & Wt & ", " & Wr);
            end if;

         when B_Sub =>
            if Is_Ref (Lhs_Ty) then
               --  §8.6.4: scale the follow operand by the referent's size
               --  (mirrors B_Add reference arithmetic).
               declare
                  Scale : constant Cell_Count := Sizeof (Lhs_Ty.Target);
               begin
                  case Scale is
                     when 1 => null;
                     when 2 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #1");
                     when 4 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #2");
                     when 8 =>
                        IO.Put_Line (F, "    lsl     " & Xr & ", " & Xr
                                        & ", #3");
                     when others =>
                        IO.Put_Line (F, "    mov     x12, #" & Img (Scale));
                        IO.Put_Line (F, "    mul     " & Xr & ", " & Xr
                                        & ", x12");
                  end case;
                  IO.Put_Line (F, "    sub     " & Xt & ", " & Xt
                                  & ", " & Xr);
               end;
            elsif Use_64 then
               IO.Put_Line (F, "    sub     " & Xt & ", " & Xt & ", " & Xr);
            else
               IO.Put_Line (F, "    sub     " & Wt & ", " & Wt & ", " & Wr);
            end if;

         when B_Mul =>
            if Use_64 then
               IO.Put_Line (F, "    mul     " & Xt & ", " & Xt & ", " & Xr);
            else
               IO.Put_Line (F, "    mul     " & Wt & ", " & Wt & ", " & Wr);
            end if;

         when B_Div | B_Mod =>
            --  §6.4.1. The instruction follows the operand signedness, and
            --  narrow operands are normalised first (registers may hold
            --  garbage above the type width). arm64 division semantics
            --  match the spec exactly: x / 0 == 0 and MIN / -1 == MIN, so
            --  a % b = a - (a / b) * b (msub) also yields x % 0 == x and
            --  MIN % -1 == 0 without further correction.
            declare
               W      : constant Cell_Count := Sizeof (Lhs_Ty);
               Signed : constant Boolean := Is_Signed_Int (Lhs_Ty);
               Dv     : constant String  :=
                 (if Signed then "sdiv" else "udiv");
            begin
               if Signed then
                  case W is
                     when 1 =>
                        IO.Put_Line (F, "    sxtb    " & Xt & ", " & Wt);
                        IO.Put_Line (F, "    sxtb    " & Xr & ", " & Wr);
                     when 2 =>
                        IO.Put_Line (F, "    sxth    " & Xt & ", " & Wt);
                        IO.Put_Line (F, "    sxth    " & Xr & ", " & Wr);
                     when 4 =>
                        IO.Put_Line (F, "    sxtw    " & Xt & ", " & Wt);
                        IO.Put_Line (F, "    sxtw    " & Xr & ", " & Wr);
                     when others => null;
                  end case;
               else
                  case W is
                     when 1 =>
                        IO.Put_Line (F, "    uxtb    " & Wt & ", " & Wt);
                        IO.Put_Line (F, "    uxtb    " & Wr & ", " & Wr);
                     when 2 =>
                        IO.Put_Line (F, "    uxth    " & Wt & ", " & Wt);
                        IO.Put_Line (F, "    uxth    " & Wr & ", " & Wr);
                     when 4 =>
                        --  Writing the W-form zeroes the upper 32 bits.
                        IO.Put_Line (F, "    mov     " & Wt & ", " & Wt);
                        IO.Put_Line (F, "    mov     " & Wr & ", " & Wr);
                     when others => null;
                  end case;
               end if;
               --  After normalisation the full 64-bit register holds the
               --  exact value, so the division runs in the X form for all
               --  widths. The wrap case (signed MIN / -1) of narrow types
               --  is exact in 64 bits and re-truncates to MIN naturally.
               if E.B_Op = B_Div then
                  IO.Put_Line (F, "    " & Dv & "    " & Xt
                                  & ", " & Xt & ", " & Xr);
               else
                  IO.Put_Line (F, "    " & Dv & "    x12, " & Xt
                                  & ", " & Xr);
                  IO.Put_Line (F, "    msub    " & Xt & ", x12, " & Xr
                                  & ", " & Xt);
               end if;
            end;

         when B_Sat_Add | B_Sat_Sub | B_Sat_Mul | B_Sat_Div =>
            Lower_Sat (E.B_Op, Lhs_Ty);

         when B_Wide_Add | B_Wide_Mul =>
            --  Result is a tuple aggregate; only valid as a let/mut
            --  initialiser (materialised by Lower_Stmt), not in a register.
            raise Program_Error with
              "codegen: widening `+@`/`*@` is only supported as a "
              & "let/mut initialiser in the bootstrap";

         when B_And | B_Or | B_Xor =>
            declare
               Mn : constant String :=
                 (case E.B_Op is
                     when B_And  => "and ",
                     when B_Or   => "orr ",
                     when others => "eor ");
            begin
               if Use_64 then
                  IO.Put_Line (F, "    " & Mn & "    " & Xt & ", " & Xt
                                  & ", " & Xr);
               else
                  IO.Put_Line (F, "    " & Mn & "    " & Wt & ", " & Wt
                                  & ", " & Wr);
               end if;
            end;

         when B_Shl | B_Shr =>
            --  §6.5.2. Shift in register width; a count >= W (the type's
            --  *bit* width) is forced to the spec result (0, or the sign
            --  for signed `>>`). The hardware masks the count, so the
            --  cmp uses the original count value and overrides via csel.
            declare
               W_Bits : constant Cell_Count := 8 * Sizeof (Lhs_Ty);
               Signed : constant Boolean := Is_Signed_Int (Lhs_Ty);
               T  : constant String := (if Use_64 then Xt else Wt);
               R  : constant String := (if Use_64 then Xr else Wr);
               ZR : constant String := (if Use_64 then "xzr" else "wzr");
               S  : constant String := (if Use_64 then "x12" else "w12");
            begin
               if E.B_Op = B_Shl then
                  IO.Put_Line (F, "    lsl     " & T & ", " & T & ", " & R);
                  IO.Put_Line (F, "    cmp     " & R & ", #" & Img (W_Bits));
                  IO.Put_Line (F, "    csel    " & T & ", " & ZR & ", "
                                  & T & ", hs");
                  --  `<<` is mod 2^W; mask away bits above a narrow width
                  --  (wider results are produced for sub-register types).
                  if W_Bits = 8 then
                     IO.Put_Line (F, "    uxtb    " & Wt & ", " & Wt);
                  elsif W_Bits = 16 then
                     IO.Put_Line (F, "    uxth    " & Wt & ", " & Wt);
                  end if;
               elsif not Signed then
                  IO.Put_Line (F, "    lsr     " & T & ", " & T & ", " & R);
                  IO.Put_Line (F, "    cmp     " & R & ", #" & Img (W_Bits));
                  IO.Put_Line (F, "    csel    " & T & ", " & ZR & ", "
                                  & T & ", hs");
               else
                  --  signed >>: sign-replicate when count >= W.
                  IO.Put_Line (F, "    asr     " & S & ", " & T & ", #"
                                  & Img (W_Bits - 1));
                  IO.Put_Line (F, "    asr     " & T & ", " & T & ", " & R);
                  IO.Put_Line (F, "    cmp     " & R & ", #" & Img (W_Bits));
                  IO.Put_Line (F, "    csel    " & T & ", " & S & ", "
                                  & T & ", hs");
               end if;
            end;

         when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge =>
            --  §6.6: relational codes follow operand signedness. `==`/`!=`
            --  do not depend on it (eq/ne is the same for both), but
            --  </>/<=/>= over an unsigned type must use the unsigned
            --  (carry-based) condition codes lo/hi/ls/hs, not the signed
            --  (overflow-based) lt/gt/le/ge, or e.g. 0xFFFFFFFF > 1 (ui4)
            --  would come out false.
            declare
               Signed : constant Boolean := Is_Signed_Int (Lhs_Ty);
            begin
               if Use_64 then
                  IO.Put_Line (F, "    cmp     " & Xt & ", " & Xr);
               else
                  IO.Put_Line (F, "    cmp     " & Wt & ", " & Wr);
               end if;
               declare
                  C : constant String :=
                    (case E.B_Op is
                        when B_Eq => "eq",
                        when B_Ne => "ne",
                        when B_Lt => (if Signed then "lt" else "lo"),
                        when B_Gt => (if Signed then "gt" else "hi"),
                        when B_Le => (if Signed then "le" else "ls"),
                        when B_Ge => (if Signed then "ge" else "hs"),
                        when others => "eq");
               begin
                  IO.Put_Line (F, "    cset    " & Wt & ", " & C);
               end;
            end;

         when B_LAnd | B_LOr | B_LXor =>
            --  Handled by the short-circuit / contract-XOR paths above.
            raise Program_Error with "codegen: unreachable logical op";
      end case;
   end Lower_Binary;
