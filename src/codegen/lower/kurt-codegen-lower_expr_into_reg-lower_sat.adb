separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Sat (Op : Binary_Op; Ty : Type_Access) is
      W      : constant Natural := Sizeof (Ty);
      Signed : constant Boolean := Is_Signed_Int (Ty);
      Xt : constant String := "x" & Img (Target_Reg);
      Wt : constant String := "w" & Img (Target_Reg);
      Xr : constant String := "x" & Img (Target_Reg + 1);
      Wr : constant String := "w" & Img (Target_Reg + 1);
   begin
      if W < 8 then
         --  Widen both operands to a full 64-bit register.
         if Signed then
            case W is
               when 1 =>
                  IO.Put_Line (F, "    sxtb    " & Xt & ", " & Wt);
                  IO.Put_Line (F, "    sxtb    " & Xr & ", " & Wr);
               when 2 =>
                  IO.Put_Line (F, "    sxth    " & Xt & ", " & Wt);
                  IO.Put_Line (F, "    sxth    " & Xr & ", " & Wr);
               when others =>
                  IO.Put_Line (F, "    sxtw    " & Xt & ", " & Wt);
                  IO.Put_Line (F, "    sxtw    " & Xr & ", " & Wr);
            end case;
         else
            case W is
               when 1 =>
                  IO.Put_Line (F, "    uxtb    " & Wt & ", " & Wt);
                  IO.Put_Line (F, "    uxtb    " & Wr & ", " & Wr);
               when 2 =>
                  IO.Put_Line (F, "    uxth    " & Wt & ", " & Wt);
                  IO.Put_Line (F, "    uxth    " & Wr & ", " & Wr);
               when others =>  --  4: writing Wn zeroes the upper 32
                  IO.Put_Line (F, "    mov     " & Wt & ", " & Wt);
                  IO.Put_Line (F, "    mov     " & Wr & ", " & Wr);
            end case;
         end if;

         if not Signed and then Op = B_Sat_Sub then
            --  Unsigned underflow saturates to 0.
            IO.Put_Line (F, "    subs    " & Xt & ", " & Xt & ", " & Xr);
            IO.Put_Line (F, "    csel    " & Xt & ", xzr, " & Xt & ", mi");
            return;
         end if;

         case Op is
            when B_Sat_Add =>
               IO.Put_Line (F, "    add     " & Xt & ", " & Xt & ", " & Xr);
            when B_Sat_Sub =>
               IO.Put_Line (F, "    sub     " & Xt & ", " & Xt & ", " & Xr);
            when B_Sat_Mul =>
               IO.Put_Line (F, "    mul     " & Xt & ", " & Xt & ", " & Xr);
            when others =>  --  B_Sat_Div
               IO.Put_Line (F, "    " & (if Signed then "sdiv" else "udiv")
                               & "    " & Xt & ", " & Xt & ", " & Xr);
         end case;

         --  Clamp to the type's range. x12 = MAX (and, signed, x13 = MIN).
         if Signed then
            Lower_Imm (F, 12, Long_Long_Integer (2) ** (8 * W - 1) - 1, True);
            IO.Put_Line (F, "    neg     x13, x12");
            IO.Put_Line (F, "    sub     x13, x13, #1");      --  MIN
            IO.Put_Line (F, "    cmp     " & Xt & ", x12");
            IO.Put_Line (F, "    csel    " & Xt & ", x12, " & Xt & ", gt");
            IO.Put_Line (F, "    cmp     " & Xt & ", x13");
            IO.Put_Line (F, "    csel    " & Xt & ", x13, " & Xt & ", lt");
         else
            Lower_Imm (F, 12, Long_Long_Integer (2) ** (8 * W) - 1, True);
            IO.Put_Line (F, "    cmp     " & Xt & ", x12");
            IO.Put_Line (F, "    csel    " & Xt & ", x12, " & Xt & ", hi");
         end if;
         return;
      end if;

      --  W = 8 : flag-based detection.
      if Signed then
         --  x12 = MAX = 0x7FFF_FFFF_FFFF_FFFF
         Lower_Imm (F, 12, Long_Long_Integer'Last, True);
         case Op is
            when B_Sat_Add =>
               IO.Put_Line (F, "    asr     x13, " & Xt & ", #63");
               IO.Put_Line (F, "    adds    " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    eor     x13, x13, x12");
               IO.Put_Line (F, "    csel    " & Xt & ", x13, " & Xt & ", vs");
            when B_Sat_Sub =>
               IO.Put_Line (F, "    asr     x13, " & Xt & ", #63");
               IO.Put_Line (F, "    subs    " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    eor     x13, x13, x12");
               IO.Put_Line (F, "    csel    " & Xt & ", x13, " & Xt & ", vs");
            when B_Sat_Mul =>
               IO.Put_Line (F, "    eor     x13, " & Xt & ", " & Xr);
               IO.Put_Line (F, "    asr     x13, x13, #63");
               IO.Put_Line (F, "    smulh   x14, " & Xt & ", " & Xr);
               IO.Put_Line (F, "    mul     " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    asr     x15, " & Xt & ", #63");
               IO.Put_Line (F, "    eor     x13, x13, x12");
               IO.Put_Line (F, "    cmp     x14, x15");
               IO.Put_Line (F, "    csel    " & Xt & ", x13, " & Xt & ", ne");
            when others =>  --  B_Sat_Div : only MIN / -1 overflows -> MAX
               IO.Put_Line (F, "    mov     x13, #1");
               IO.Put_Line (F, "    lsl     x13, x13, #63");   --  MIN
               IO.Put_Line (F, "    cmp     " & Xt & ", x13");
               IO.Put_Line (F, "    ccmn    " & Xr & ", #1, #0, eq");
               IO.Put_Line (F, "    sdiv    " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    csel    " & Xt & ", x12, " & Xt & ", eq");
         end case;
      else
         case Op is
            when B_Sat_Add =>
               IO.Put_Line (F, "    adds    " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    csinv   " & Xt & ", " & Xt & ", xzr, cc");
            when B_Sat_Sub =>
               IO.Put_Line (F, "    subs    " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    csel    " & Xt & ", xzr, " & Xt & ", cc");
            when B_Sat_Mul =>
               IO.Put_Line (F, "    umulh   x13, " & Xt & ", " & Xr);
               IO.Put_Line (F, "    mul     " & Xt & ", " & Xt & ", " & Xr);
               IO.Put_Line (F, "    cmp     x13, #0");
               IO.Put_Line (F, "    csinv   " & Xt & ", " & Xt & ", xzr, eq");
            when others =>  --  B_Sat_Div : unsigned never overflows
               IO.Put_Line (F, "    udiv    " & Xt & ", " & Xt & ", " & Xr);
         end case;
      end if;
   end Lower_Sat;
