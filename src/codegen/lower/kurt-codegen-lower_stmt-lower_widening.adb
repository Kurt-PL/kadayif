separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_Widening
     (Off : Natural; E : Expr_Access; W_Off : Natural)
   is
      T_Ty   : constant Type_Access := Type_Of_Expr (E.B_Lhs, ST);
      W      : constant Natural := Sizeof (T_Ty);
      Signed : constant Boolean := Is_Signed_Int (T_Ty);
      Add    : constant Boolean := E.B_Op = B_Wide_Add;
   begin
      --  Evaluate operands: lhs -> x9 (spilled), rhs -> x10, reload x9.
      Lower_Expr_Into_Reg (F, E.B_Lhs, 9, ST);
      IO.Put_Line (F, "    sub     sp, sp, #16");
      IO.Put_Line (F, "    str     x9, [sp]");
      Lower_Expr_Into_Reg (F, E.B_Rhs, 10, ST);
      IO.Put_Line (F, "    ldr     x9, [sp]");
      IO.Put_Line (F, "    add     sp, sp, #16");

      if W < 8 then
         --  Exact in 64-bit; low and high are W-byte slices.
         if Signed then
            IO.Put_Line (F, "    sxt" & (if W = 1 then "b" elsif W = 2
                            then "h" else "w") & "    x9, w9");
            IO.Put_Line (F, "    sxt" & (if W = 1 then "b" elsif W = 2
                            then "h" else "w") & "    x10, w10");
         else
            if W = 1 then
               IO.Put_Line (F, "    uxtb    w9, w9");
               IO.Put_Line (F, "    uxtb    w10, w10");
            elsif W = 2 then
               IO.Put_Line (F, "    uxth    w9, w9");
               IO.Put_Line (F, "    uxth    w10, w10");
            else
               IO.Put_Line (F, "    mov     w9, w9");
               IO.Put_Line (F, "    mov     w10, w10");
            end if;
         end if;
         IO.Put_Line (F, "    " & (if Add then "add " else "mul ")
                         & "    x11, x9, x10");
         IO.Put_Line (F, "    mov     x9, x11");
         Store_Sized (Off, W);                       --  low
         IO.Put_Line (F, "    " & (if Signed then "asr " else "lsr ")
                         & "    x9, x11, #" & Img (8 * W));
         Store_Sized (Off + W_Off, W);               --  high
      else
         --  64-bit: flag/high-multiply based.
         if Add then
            if Signed then
               IO.Put_Line (F, "    asr     x11, x9, #63");
               IO.Put_Line (F, "    asr     x12, x10, #63");
               IO.Put_Line (F, "    adds    x9, x9, x10");
               Store_Sized (Off, 8);
               IO.Put_Line (F, "    adc     x9, x11, x12");
               Store_Sized (Off + W_Off, 8);
            else
               IO.Put_Line (F, "    adds    x9, x9, x10");
               Store_Sized (Off, 8);
               IO.Put_Line (F, "    adc     x9, xzr, xzr");
               Store_Sized (Off + W_Off, 8);
            end if;
         else  --  multiply
            IO.Put_Line (F, "    " & (if Signed then "smulh" else "umulh")
                            & "   x11, x9, x10");
            IO.Put_Line (F, "    mul     x9, x9, x10");
            Store_Sized (Off, 8);
            IO.Put_Line (F, "    mov     x9, x11");
            Store_Sized (Off + W_Off, 8);
         end if;
      end if;
   end Lower_Widening;
