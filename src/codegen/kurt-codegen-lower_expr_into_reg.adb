--  Expression lowering (subunit of Kurt.Codegen).
--  Computes the value of E into x<Target_Reg>. Sees all of the parent
--  body's declarations (helpers, Lower_State, Lower_Imm, Lower_Stmt …).

separate (Kurt.Codegen)
procedure Lower_Expr_Into_Reg
  (F          : IO.File_Type;
   E          : Expr_Access;
   Target_Reg : Natural;
   ST         : in out Lower_State)
is
   Xreg : constant String := "x" & Img (Target_Reg);
   Wreg : constant String := "w" & Img (Target_Reg);

   --  Convert the integer held in Target_Reg from a Src_Sz-byte value to
   --  a Tgt_Sz-byte value (§6.8.2). Widening follows the *source*
   --  signedness (sext if signed, zext otherwise — target signedness only
   --  reinterprets the same bits); narrowing keeps the low Tgt_Sz bytes.
   procedure Emit_Int_Conv
     (Src_Sz : Natural; Src_Signed : Boolean; Tgt_Sz : Natural) is
   begin
      if Tgt_Sz = Src_Sz then
         return;  --  identity / reinterpret
      elsif Tgt_Sz > Src_Sz then
         if Src_Signed then
            case Src_Sz is
               when 1 =>
                  IO.Put_Line (F, "    sxtb    "
                    & (if Tgt_Sz >= 8 then Xreg else Wreg) & ", " & Wreg);
               when 2 =>
                  IO.Put_Line (F, "    sxth    "
                    & (if Tgt_Sz >= 8 then Xreg else Wreg) & ", " & Wreg);
               when others =>  --  4 -> 8
                  IO.Put_Line (F, "    sxtw    " & Xreg & ", " & Wreg);
            end case;
         else
            case Src_Sz is
               when 1 => IO.Put_Line (F, "    uxtb    " & Wreg & ", " & Wreg);
               when 2 => IO.Put_Line (F, "    uxth    " & Wreg & ", " & Wreg);
               when others =>  --  4 -> 8: writing Wreg zeroes the upper 32
                  IO.Put_Line (F, "    mov     " & Wreg & ", " & Wreg);
            end case;
         end if;
      else  --  Tgt_Sz < Src_Sz : truncate to the low bytes
         case Tgt_Sz is
            when 1 => IO.Put_Line (F, "    uxtb    " & Wreg & ", " & Wreg);
            when 2 => IO.Put_Line (F, "    uxth    " & Wreg & ", " & Wreg);
            when others =>  --  -> 4: writing Wreg zeroes the upper 32
               IO.Put_Line (F, "    mov     " & Wreg & ", " & Wreg);
         end case;
      end if;
   end Emit_Int_Conv;

   ------------------------------------------------------------------
   --  Call lowering. Arguments are evaluated to stack scratch slots in
   --  source order (§2.7.1), then fixed args are loaded into x0..x7.
   --  Variadic args (Apple arm64 ABI) sit at the bottom of the frame.
   ------------------------------------------------------------------
   procedure Lower_Call (E : Expr_Access) is
      Callee_Name : constant String := Path_Symbol (E.C_Callee);
      N           : constant Natural := Natural (E.C_Args.Length);

      Info      : Dyn_Sym;
      Has_Info  : constant Boolean := Lookup_Dyn_Sym (ST, Callee_Name, Info);
      --  §5.15: a `@symbol "name"` on the (dyn) callee overrides the
      --  external name; otherwise the identifier is used.
      Sym       : constant String := "_"
        & (if Has_Info and then SU.Length (Info.Symbol) > 0
           then SU.To_String (Info.Symbol) else Callee_Name);
      Is_Var    : constant Boolean := Has_Info and then Info.Is_Variadic;
      Fixed     : constant Natural :=
        (if Is_Var then Natural'Min (Info.Fixed_Args, N) else N);
      Var_Count : constant Natural := N - Fixed;
      Var_Bytes : constant Natural := Var_Count * 8;

      --  Consume the pending sret slot immediately so nested calls inside
      --  the arguments cannot steal it; only this (outermost) call uses it.
      Sret_Slot : constant Integer := ST.Pending_Sret;

      --  AAPCS64 per-argument classification of the fixed args.
      Max_Args : constant Natural := 16;
      type Off_Arr is array (0 .. Max_Args) of Natural;
      type Cls_Arr is array (0 .. Max_Args) of Agg_Class;
      Slot_Off : Off_Arr := (others => 0);   --  fixed-arg scratch slot
      Copy_Off : Off_Arr := (others => 0);   --  >16B copy area
      Cls      : Cls_Arr := (others => Not_Agg);
      Fix_Bytes  : Natural := 0;
      Copy_Bytes : Natural := 0;
      Total      : Natural;
   begin
      if N > Max_Args then
         raise Program_Error with
           "codegen: more than 16 arguments not supported";
      end if;
      ST.Pending_Sret := -1;

      --  First pass: lay out the scratch region.
      --    [0 .. Var_Bytes)              variadic args (8 bytes each)
      --    [Var_Bytes .. +Fix_Bytes)     fixed-arg slots (8 or 16 bytes)
      --    [.. +Copy_Bytes)              copies of indirect aggregates
      for K in 0 .. Fixed - 1 loop
         declare
            Arg : constant Expr_Access :=
              E.C_Args.Element (E.C_Args.First_Index + K);
            C   : constant Agg_Class :=
              Classify_Agg (Type_Of_Expr (Arg, ST));
         begin
            Cls (K)      := C;
            Slot_Off (K) := Var_Bytes + Fix_Bytes;
            Fix_Bytes    := Fix_Bytes + (if C = Two_Regs then 16 else 8);
         end;
      end loop;
      for K in 0 .. Fixed - 1 loop
         if Cls (K) = Indirect then
            declare
               Sz : constant Natural := Sizeof (Type_Of_Expr
                 (E.C_Args.Element (E.C_Args.First_Index + K), ST));
            begin
               Copy_Off (K) := Var_Bytes + Fix_Bytes + Copy_Bytes;
               Copy_Bytes   := Copy_Bytes + ((Sz + 7) / 8) * 8;
            end;
         end if;
      end loop;
      Total := ((Var_Bytes + Fix_Bytes + Copy_Bytes + 15) / 16) * 16;

      if Total > 0 then
         IO.Put_Line (F, "    sub     sp, sp, #" & Img (Total));
      end if;

      --  Evaluate every argument in source order into its slot.
      for K in 0 .. N - 1 loop
         declare
            Arg : constant Expr_Access :=
              E.C_Args.Element (E.C_Args.First_Index + K);
            Off : constant Natural :=
              (if K < Fixed then Slot_Off (K) else (K - Fixed) * 8);
         begin
            if Is_Float (Type_Of_Expr (Arg, ST)) then
               --  Apple variadic ABI: a float argument is promoted to a
               --  double and passed on the stack (§ C varargs).
               Lower_Float_Into_D (F, Arg, 0, ST);
               if Sizeof (Type_Of_Expr (Arg, ST)) = 4 then
                  IO.Put_Line (F, "    fcvt    d0, s0");   --  f32 -> f64
               end if;
               IO.Put_Line (F, "    str     d0, [sp, #" & Img (Off) & "]");
            elsif K < Fixed and then Cls (K) = Two_Regs then
               --  9–16-byte aggregate: copy both halves from the value's
               --  frame slot (binding) or from x0/x1 (nested call).
               if Arg.Kind = E_Dyn_Cast then
                  --  §9.5 build the fat reference in the arg slot:
                  --    [off]   = value pointer (the inner `&T`)
                  --    [off+8] = address of the dispatch table for (T,Trait)
                  Lower_Expr_Into_Reg (F, Arg.DC_Inner, 9, ST);
                  IO.Put_Line (F, "    str     x9, [sp, #" & Img (Off) & "]");
                  declare
                     Lbl : constant String := "_Ldtable_"
                       & SU.To_String (Arg.DC_Conc) & "_"
                       & SU.To_String (Arg.DC_Trait);
                  begin
                     IO.Put_Line (F, "    adrp    x9, " & Lbl & "@PAGE");
                     IO.Put_Line (F, "    add     x9, x9, " & Lbl
                                     & "@PAGEOFF");
                     IO.Put_Line (F, "    str     x9, [sp, #"
                                     & Img (Off + 8) & "]");
                  end;
               elsif Arg.Kind = E_Slice_Cast then
                  --  §4.6 build the slice fat reference in the arg slot:
                  --    [off]   = ptr (the array address: inner `&[T;N]`)
                  --    [off+8] = len (the static element count N)
                  Lower_Expr_Into_Reg (F, Arg.SC_Inner, 9, ST);
                  IO.Put_Line (F, "    str     x9, [sp, #" & Img (Off) & "]");
                  Lower_Imm (F, 9,
                    Long_Long_Integer (Arg.SC_Len), True);
                  IO.Put_Line (F, "    str     x9, [sp, #"
                                  & Img (Off + 8) & "]");
               elsif Arg.Kind = E_Path
                 and then Natural (Arg.Segments.Length) = 1
                 and then Find_Binding
                   (ST, SU.To_String (Arg.Segments.Last_Element)) /= 0
               then
                  declare
                     B : constant Binding := ST.Bindings.Element
                       (Find_Binding
                          (ST, SU.To_String (Arg.Segments.Last_Element)));
                  begin
                     IO.Put_Line (F, "    ldr     x9, [x29, #"
                                     & Img (B.Offset) & "]");
                     IO.Put_Line (F, "    str     x9, [sp, #"
                                     & Img (Off) & "]");
                     IO.Put_Line (F, "    ldr     x9, [x29, #"
                                     & Img (B.Offset + 8) & "]");
                     IO.Put_Line (F, "    str     x9, [sp, #"
                                     & Img (Off + 8) & "]");
                  end;
               elsif Arg.Kind = E_Call then
                  Lower_Call (Arg);
                  IO.Put_Line (F, "    str     x0, [sp, #"
                                  & Img (Off) & "]");
                  IO.Put_Line (F, "    str     x1, [sp, #"
                                  & Img (Off + 8) & "]");
               else
                  raise Program_Error with
                    "codegen: unsupported two-register aggregate argument "
                    & "(bootstrap accepts a binding or a call result)";
               end if;
            elsif K < Fixed and then Cls (K) = Indirect then
               --  >16-byte aggregate: copy into the caller-owned area and
               --  pass its address (§8.8.1 copy semantics preserved).
               if Arg.Kind = E_Path
                 and then Natural (Arg.Segments.Length) = 1
                 and then Find_Binding
                   (ST, SU.To_String (Arg.Segments.Last_Element)) /= 0
               then
                  declare
                     B  : constant Binding := ST.Bindings.Element
                       (Find_Binding
                          (ST, SU.To_String (Arg.Segments.Last_Element)));
                     Sz : constant Natural := Sizeof (B.Ty);
                  begin
                     IO.Put_Line (F, "    mov     x10, sp");
                     Emit_Mem_Copy
                       (F, "x29", B.Offset, "x10", Copy_Off (K), Sz);
                     IO.Put_Line (F, "    add     x9, sp, #"
                                     & Img (Copy_Off (K)));
                     IO.Put_Line (F, "    str     x9, [sp, #"
                                     & Img (Off) & "]");
                  end;
               else
                  raise Program_Error with
                    "codegen: unsupported indirect aggregate argument "
                    & "(bootstrap accepts a binding)";
               end if;
            else
               Lower_Expr_Into_Reg (F, Arg, 9, ST);
               --  A sub-8-byte integer travels as a full register and the
               --  loose register invariant allows garbage above the type
               --  width: normalise per the operand signedness (this is
               --  also the C variadic integer promotion for §5.1.3 calls).
               declare
                  Arg_T : constant Type_Access := Type_Of_Expr (Arg, ST);
               begin
                  if Arg_T /= null and then Arg_T.Kind = T_Named
                    and then not Is_Float (Arg_T)
                    and then not Is_Aggregate_Type (Arg_T)
                    and then Sizeof (Arg_T) < 8
                  then
                     if Is_Signed_Int (Arg_T) then
                        case Sizeof (Arg_T) is
                           when 1 =>
                              IO.Put_Line (F, "    sxtb    x9, w9");
                           when 2 =>
                              IO.Put_Line (F, "    sxth    x9, w9");
                           when others =>
                              IO.Put_Line (F, "    sxtw    x9, w9");
                        end case;
                     else
                        case Sizeof (Arg_T) is
                           when 1 =>
                              IO.Put_Line (F, "    uxtb    w9, w9");
                           when 2 =>
                              IO.Put_Line (F, "    uxth    w9, w9");
                           when others =>
                              --  Writing the W form zeroes the upper 32.
                              IO.Put_Line (F, "    mov     w9, w9");
                        end case;
                     end if;
                  end if;
               end;
               IO.Put_Line (F, "    str     x9, [sp, #" & Img (Off) & "]");
            end if;
         end;
      end loop;

      --  Load fixed args into the general-purpose registers (NGRN walk).
      declare
         NGRN : Natural := 0;
      begin
         for K in 0 .. Fixed - 1 loop
            IO.Put_Line (F, "    ldr     x" & Img (NGRN)
                            & ", [sp, #" & Img (Slot_Off (K)) & "]");
            NGRN := NGRN + 1;
            if Cls (K) = Two_Regs then
               IO.Put_Line (F, "    ldr     x" & Img (NGRN)
                               & ", [sp, #" & Img (Slot_Off (K) + 8) & "]");
               NGRN := NGRN + 1;
            end if;
         end loop;
         if NGRN > 8 then
            raise Program_Error with
              "codegen: fixed arguments exceed 8 registers";
         end if;
      end;

      --  sret: an indirect-class return needs the destination address in
      --  x8 (AAPCS64). The destination slot is provided by the enclosing
      --  let-binding via Pending_Sret.
      if Classify_Agg (Lookup_Fn_Ret (ST, Callee_Name)) = Indirect then
         if Sret_Slot < 0 then
            raise Program_Error with
              "codegen: a call returning a >16-byte aggregate is only "
              & "supported as a let/mut initialiser";
         end if;
         IO.Put_Line (F, "    add     x8, x29, #" & Img (Sret_Slot));
      end if;

      IO.Put_Line (F, "    bl      " & Sym);

      if Total > 0 then
         IO.Put_Line (F, "    add     sp, sp, #" & Img (Total));
      end if;
   end Lower_Call;

   ------------------------------------------------------------------
   --  Binary lowering. lhs → x<target>, rhs → x<target+1> (lhs spilled
   --  across rhs evaluation to survive caller-saved clobber); the result
   --  lands in x<target>.
   ------------------------------------------------------------------
   --  Saturating arithmetic (§6.4.2). lhs is in x<Target_Reg>, rhs in
   --  x<Target_Reg+1>; the clamped result lands back in x<Target_Reg>.
   --  Scratch: x12..x15.
   --
   --  Types narrower than a cell-pair (W < 8) are computed exactly in
   --  64-bit (operands sign/zero-extended; +,-,* of ≤32-bit operands
   --  never overflow 64 bits) and then clamped to [MIN, MAX]. The 8-byte
   --  types use flag-based overflow/carry detection.
   ------------------------------------------------------------------
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

   ------------------------------------------------------------------
   --  §9.5 dynamic dispatch: `recv.method(args)` where recv is a
   --  `&dyn Trait` binding. The fat reference holds the value pointer
   --  (slot+0) and the dispatch-table pointer (slot+8). The method's
   --  subroutine pointer is loaded from dtable field `3 + k` and invoked
   --  indirectly; the value pointer is passed as the erased self.
   --  Bootstrap: extra arguments are scalar/reference (≤8 bytes).
   ------------------------------------------------------------------
   procedure Lower_Dyn_Call (E : Expr_Access) is
      Recv  : constant Expr_Access := E.C_Callee.F_Recv;
      RT    : constant Type_Access := Type_Of_Expr (Recv, ST);
      Trait : constant String := SU.To_String (RT.Target.Trait_Name);
      Field : constant Integer :=
        Method_Field_Index (Trait, SU.To_String (E.C_Callee.F_Name));
      N     : constant Natural := Natural (E.C_Args.Length);
      Total : constant Natural := ((N * 8 + 15) / 16) * 16;
      Bi    : constant Natural :=
        (if Recv.Kind = E_Path
            and then Natural (Recv.Segments.Length) = 1
         then Find_Binding (ST, SU.To_String (Recv.Segments.Last_Element))
         else 0);
   begin
      if Bi = 0 then
         raise Program_Error with
           "codegen: dynamic-dispatch receiver must be a `&dyn` binding";
      end if;
      if Field < 0 then
         raise Program_Error with
           "codegen: method not found in trait '" & Trait & "'";
      end if;
      declare
         Off : constant Natural := ST.Bindings.Element (Bi).Offset;
      begin
         --  Evaluate the explicit (non-self) arguments into scratch slots.
         if Total > 0 then
            IO.Put_Line (F, "    sub     sp, sp, #" & Img (Total));
         end if;
         for K in 0 .. N - 1 loop
            Lower_Expr_Into_Reg
              (F, E.C_Args.Element (E.C_Args.First_Index + K), 9, ST);
            IO.Put_Line (F, "    str     x9, [sp, #" & Img (K * 8) & "]");
         end loop;
         --  self pointer -> x0, explicit args -> x1..
         IO.Put_Line (F, "    ldr     x0, [x29, #" & Img (Off) & "]");
         for K in 0 .. N - 1 loop
            IO.Put_Line (F, "    ldr     x" & Img (K + 1)
                            & ", [sp, #" & Img (K * 8) & "]");
         end loop;
         --  dispatch table -> x9, method pointer at field*8 -> x9, blr.
         IO.Put_Line (F, "    ldr     x9, [x29, #" & Img (Off + 8) & "]");
         IO.Put_Line (F, "    ldr     x9, [x9, #" & Img (Field * 8) & "]");
         IO.Put_Line (F, "    blr     x9");
         if Total > 0 then
            IO.Put_Line (F, "    add     sp, sp, #" & Img (Total));
         end if;
         if Target_Reg /= 0 then
            IO.Put_Line (F, "    mov     " & Xreg & ", x0");
         end if;
      end;
   end Lower_Dyn_Call;

   ------------------------------------------------------------------
   procedure Lower_Binary (E : Expr_Access) is
      Xt : constant String := "x" & Img (Target_Reg);
      Wt : constant String := "w" & Img (Target_Reg);
      Xr : constant String := "x" & Img (Target_Reg + 1);
      Wr : constant String := "w" & Img (Target_Reg + 1);

      Lhs_Ty : constant Type_Access := Type_Of_Expr (E.B_Lhs, ST);
      Use_64 : constant Boolean := Is_Ref (Lhs_Ty)
                                or else Sizeof (Lhs_Ty) > 4;
   begin
      --  §4.3.3 floating-point comparison via the hardware `fcmp`, which
      --  follows ISO/IEC/IEEE 60559:2020 (unordered → all relational false,
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

      --  §7.2.2 contract `^`: both operands evaluated, truthified, then
      --  combined with an integer xor (operands are 0/1).
      if E.B_Op = B_Xor and then Is_Contract_Ty (Lhs_Ty) then
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
                  Scale : constant Natural := Sizeof (Lhs_Ty.Target);
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
                  Scale : constant Natural := Sizeof (Lhs_Ty.Target);
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
               W      : constant Natural := Sizeof (Lhs_Ty);
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
               W_Bits : constant Natural := 8 * Sizeof (Lhs_Ty);
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
                     when B_Lt => "lt",
                     when B_Gt => "gt",
                     when B_Le => "le",
                     when B_Ge => "ge",
                     when others => "eq");
            begin
               IO.Put_Line (F, "    cset    " & Wt & ", " & C);
            end;

         when B_LAnd | B_LOr =>
            --  Handled by the short-circuit path above; unreachable.
            raise Program_Error with "codegen: unreachable logical op";
      end case;
   end Lower_Binary;

   ------------------------------------------------------------------
   --  If-expression lowering (cbz on the materialised condition).
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   --  Match lowering: evaluate the scrutinee once onto the stack, then
   --  test each arm in order with cmp/b.ne; the matched arm's body lands
   --  in x<target>. A #wild# arm always matches.
   ------------------------------------------------------------------
   --  Load a value of Sz cells from [x29, #Off] into w9 (zero-extended).
   procedure Load_From_Frame (Off, Sz : Natural) is
      Loc : constant String := ", [x29, #" & Img (Off) & "]";
   begin
      if Sz >= 4 then
         IO.Put_Line (F, "    ldr     w9" & Loc);
      elsif Sz = 2 then
         IO.Put_Line (F, "    ldrh    w9" & Loc);
      else
         IO.Put_Line (F, "    ldrb    w9" & Loc);
      end if;
   end Load_From_Frame;

   procedure Lower_Match (E : Expr_Access) is
      FN      : constant String  := SU.To_String (ST.Fn_Name);
      Idx     : constant Natural := ST.If_Idx;
      L_End   : constant String  := "Lmatch_" & FN & "_end_" & Img (Idx);
      Scrut_T : constant Type_Access := Type_Of_Expr (E.M_Scrut, ST);

      --  An enum scrutinee bound to a local is matched in place: the
      --  discriminant sits at the binding's slot start and payload fields
      --  are bound as slot+offset aliases (no copy).
      Enum_Binding : Boolean := False;
      Base         : Natural := 0;
      EN           : SU.Unbounded_String;
   begin
      ST.If_Idx := ST.If_Idx + 1;

      if Scrut_T /= null and then Scrut_T.Kind = T_Named
        and then Kurt.Layout.Is_Enum (SU.To_String (Scrut_T.Name))
        and then E.M_Scrut.Kind = E_Path
        and then Natural (E.M_Scrut.Segments.Length) = 1
      then
         declare
            Bi : constant Natural :=
              Find_Binding (ST, SU.To_String
                              (E.M_Scrut.Segments.Last_Element));
         begin
            if Bi /= 0 then
               Enum_Binding := True;
               Base := ST.Bindings.Element (Bi).Offset;
               EN   := Scrut_T.Name;
            end if;
         end;
      end if;

      if Enum_Binding then
         declare
            Ename     : constant String  := SU.To_String (EN);
            Disc_Size : constant Natural :=
              Kurt.Layout.Enum_Disc_Size (Ename);
         begin
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
               begin
                  case Arm.Pat.Kind is
                     when Pat_Wild =>
                        Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                        IO.Put_Line (F, "    b       " & L_End);
                     when Pat_Variant =>
                        declare
                           VN  : constant String := SU.To_String
                             (Arm.Pat.Path.Last_Element);
                           Saved : constant Natural :=
                             Natural (ST.Bindings.Length);
                        begin
                           --  A void discriminant (§4.11.3: single
                           --  variant) matches unconditionally.
                           if Disc_Size > 0 then
                              Load_From_Frame (Base, Disc_Size);
                              Lower_Imm (F, 10,
                                Kurt.Layout.Variant_Value (Ename, VN),
                                False);
                              IO.Put_Line (F, "    cmp     w9, w10");
                              IO.Put_Line (F, "    b.ne    " & L_Next);
                           end if;
                           --  Bind payload fields as slot+offset aliases.
                           for K in 1 .. Natural (Arm.Pat.Bindings.Length)
                           loop
                              ST.Bindings.Append
                                ((Name   => Arm.Pat.Bindings.Element (K),
                                  Offset => Base
                                    + Kurt.Layout.Variant_Field_Offset
                                        (Scrut_T, VN, K),
                                  Ty     => Kurt.Layout.Variant_Field_Type
                                              (Scrut_T, VN, K)));
                           end loop;
                           Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                           while Natural (ST.Bindings.Length) > Saved loop
                              ST.Bindings.Delete_Last;
                           end loop;
                           IO.Put_Line (F, "    b       " & L_End);
                           IO.Put_Line (F, L_Next & ":");
                        end;
                     when Pat_Int =>
                        raise Program_Error with
                          "codegen: integer pattern on enum scrutinee";
                  end case;
               end;
            end loop;
         end;
      else
         --  Scalar scrutinee (integer, or unit enum value): stash it in a
         --  frame slot (not the stack pointer, so an arm's `b` to the end
         --  needs no fix-up) and compare in a register per arm.
         declare
            Wide  : constant Boolean := Sizeof (Scrut_T) > 4;
            SR    : constant String := (if Wide then "x9" else "w9");
            CR    : constant String := (if Wide then "x10" else "w10");
            Slot  : constant Natural := ST.Next_Offset;
         begin
            ST.Next_Offset := ST.Next_Offset + 8;
            Lower_Expr_Into_Reg (F, E.M_Scrut, 9, ST);
            IO.Put_Line (F, "    str     " & (if Wide then "x9" else "w9")
                            & ", [x29, #" & Img (Slot) & "]");
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
                  Val    : Long_Long_Integer := 0;
                  Is_Cmp : Boolean := True;
               begin
                  case Arm.Pat.Kind is
                     when Pat_Wild    => Is_Cmp := False;
                     when Pat_Int     => Val := Arm.Pat.Int_V;
                     when Pat_Variant =>
                        Val := Kurt.Layout.Variant_Value
                          (SU.To_String (Arm.Pat.Path.First_Element),
                           SU.To_String (Arm.Pat.Path.Last_Element));
                  end case;
                  if Is_Cmp then
                     IO.Put_Line (F, "    ldr     " & SR
                                     & ", [x29, #" & Img (Slot) & "]");
                     Lower_Imm (F, 10, Val, Wide);
                     IO.Put_Line (F, "    cmp     " & SR & ", " & CR);
                     IO.Put_Line (F, "    b.ne    " & L_Next);
                     Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                     IO.Put_Line (F, "    b       " & L_End);
                     IO.Put_Line (F, L_Next & ":");
                  else
                     Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                     IO.Put_Line (F, "    b       " & L_End);
                  end if;
               end;
            end loop;
         end;
      end if;

      IO.Put_Line (F, L_End & ":");
   end Lower_Match;

   procedure Lower_If (E : Expr_Access) is
      FN     : constant String  := SU.To_String (ST.Fn_Name);
      Idx    : constant Natural := ST.If_Idx;
      L_Else : constant String  := "Lelse_" & FN & "_" & Img (Idx);
      L_End  : constant String  := "Lendif_" & FN & "_" & Img (Idx);
      Wt     : constant String  := "w" & Img (Target_Reg);
   begin
      ST.If_Idx := ST.If_Idx + 1;
      Lower_Expr_Into_Reg (F, E.I_Cond, Target_Reg, ST);
      IO.Put_Line (F, "    cbz     " & Wt & ", " & L_Else);
      Lower_Expr_Into_Reg (F, E.I_Then, Target_Reg, ST);
      IO.Put_Line (F, "    b       " & L_End);
      IO.Put_Line (F, L_Else & ":");
      Lower_Expr_Into_Reg (F, E.I_Else, Target_Reg, ST);
      IO.Put_Line (F, L_End & ":");
   end Lower_If;

begin
   case E.Kind is
      when E_Range =>
         --  §4.8: a range is an aggregate; it is built in place by the
         --  let/mut initialiser path, never produced in a register.
         raise Program_Error with
           "codegen: range value outside a binding initialiser";

      when E_Uninit =>
         --  §6.1.8: an uninitialized value. Valid `uninit` positions
         --  (let/mut/assign) are intercepted earlier and store nothing;
         --  if one reaches here the target register simply keeps its
         --  current (indeterminate) contents — no instruction is emitted.
         null;

      when E_Int_Lit =>
         --  Width follows the inferred type; values wider than 16 bits
         --  are built with a movz/movk chain.
         Lower_Imm (F, Target_Reg, E.Int_V, Sizeof (E.Sem_Ty) > 4);

      when E_Float_Lit =>
         --  A float value belongs in an FP register; it reaches the
         --  integer path only in an unsupported position (e.g. float
         --  return or a fixed FP call argument — deferred).
         raise Program_Error with
           "codegen: floating-point value in an unsupported position "
           & "(float return / FP call ABI not yet implemented)";

      when E_Bool_Lit =>
         --  bool = verdict.<void,void>; Pass discrim = 1, Fail = 0.
         Lower_Imm (F, Target_Reg,
           (if E.Bool_V then 1 else 0), Sizeof (E.Sem_Ty) > 4);

      when E_String_Lit =>
         declare
            Label : constant String := "Lstr" & Img (ST.Next_Str_Idx);
         begin
            ST.Next_Str_Idx := ST.Next_Str_Idx + 1;
            IO.Put_Line (F, "    adrp    " & Xreg & ", " & Label & "@PAGE");
            IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                            & ", " & Label & "@PAGEOFF");
         end;

      when E_Field =>
         if E.F_Recv.Kind = E_String_Lit
           and then SU.To_String (E.F_Name) = "ptr"
         then
            declare
               Label : constant String := "Lstr" & Img (ST.Next_Str_Idx);
            begin
               ST.Next_Str_Idx := ST.Next_Str_Idx + 1;
               IO.Put_Line (F, "    adrp    " & Xreg & ", " & Label
                               & "@PAGE");
               IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                               & ", " & Label & "@PAGEOFF");
            end;
         elsif E.F_Recv.Kind = E_Path
           and then Natural (E.F_Recv.Segments.Length) = 1
         then
            --  Struct field load: the struct lives inline in its stack
            --  slot, so the field is at [x29, slot_off + field_off].
            declare
               Name : constant String :=
                 SU.To_String (E.F_Recv.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  raise Program_Error with
                    "codegen: unknown binding '" & Name & "'";
               end if;
               declare
                  B     : constant Binding := ST.Bindings.Element (Idx);
                  FName : constant String  := SU.To_String (E.F_Name);
                  Off   : Natural;
                  FT    : Type_Access;
               begin
                  if B.Ty /= null and then B.Ty.Kind = T_Ref
                    and then B.Ty.Target /= null
                    and then B.Ty.Target.Kind = T_Named
                    and then Kurt.Layout.Is_Struct
                      (SU.To_String (B.Ty.Target.Name))
                  then
                     --  §6.2.5 reference transparency: `self.f` — load the
                     --  reference, then the field through it.
                     declare
                        SName : constant String :=
                          SU.To_String (B.Ty.Target.Name);
                        FOff  : constant Natural :=
                          Kurt.Layout.Field_Offset (SName, FName);
                        FT2   : constant Type_Access :=
                          Kurt.Layout.Field_Type (SName, FName);
                        Sz    : constant Natural := Sizeof (FT2);
                        Loc   : constant String :=
                          ", [x10, #" & Img (FOff) & "]";
                     begin
                        IO.Put_Line (F, "    ldr     x10, [x29, #"
                                        & Img (B.Offset) & "]");
                        if Is_Ref (FT2) or else Sz >= 8 then
                           IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                        elsif Sz = 4 then
                           IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                        elsif Sz = 2 then
                           IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                        else
                           IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                        end if;
                     end;
                     return;
                  end if;
                  if Is_Slice_Ref (B.Ty) then
                     --  §4.6.1 materialised slice view: load `.ptr` from
                     --  the fat reference's first field, `.len` from the
                     --  second.
                     if FName = "ptr" then
                        IO.Put_Line (F, "    ldr     " & Xreg
                          & ", [x29, #" & Img (B.Offset) & "]");
                     elsif FName = "len" then
                        IO.Put_Line (F, "    ldr     " & Xreg
                          & ", [x29, #" & Img (B.Offset + 8) & "]");
                     else
                        raise Program_Error with
                          "codegen: slice has no field '" & FName & "'";
                     end if;
                     return;
                  end if;
                  if B.Ty /= null and then B.Ty.Kind = T_Array then
                     --  §4.6.1 array views: `.ptr` is the first element's
                     --  address, `.len` the (static) element count.
                     if FName = "ptr" then
                        IO.Put_Line (F, "    add     " & Xreg & ", x29, #"
                                        & Img (B.Offset));
                     elsif FName = "len" then
                        Lower_Imm (F, Target_Reg,
                          Long_Long_Integer (B.Ty.Len), True);
                     else
                        raise Program_Error with
                          "codegen: array has no field '" & FName & "'";
                     end if;
                     return;
                  end if;
                  if B.Ty /= null and then B.Ty.Kind = T_Range then
                     --  §4.8 range fields: `start` at offset 0, `end` at
                     --  size(T); both have type T.
                     FT  := B.Ty.Rng_Elem;
                     Off := B.Offset
                       + (if FName = "end" then Sizeof (B.Ty.Rng_Elem) else 0);
                  elsif B.Ty /= null and then B.Ty.Kind = T_Tuple then
                     --  §6.2.2 tuple field by index `.N`.
                     declare
                        TI : constant Natural := Natural'Value (FName);
                     begin
                        Off := B.Offset
                          + Kurt.Layout.Tuple_Field_Offset (B.Ty, TI);
                        FT  := Kurt.Layout.Tuple_Field_Type (B.Ty, TI);
                     end;
                  else
                     declare
                        SName : constant String := SU.To_String (B.Ty.Name);
                     begin
                        Off := B.Offset
                          + Kurt.Layout.Field_Offset (SName, FName);
                        FT  := Kurt.Layout.Field_Type (SName, FName);
                     end;
                  end if;
                  declare
                     Sz  : constant Natural := Sizeof (FT);
                     Loc : constant String  :=
                       ", [x29, #" & Img (Off) & "]";
                  begin
                     if Is_Ref (FT) or else Sz >= 8 then
                        IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                     elsif Sz = 4 then
                        IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                     elsif Sz = 2 then
                        IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                     else
                        IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                     end if;
                  end;
               end;
            end;
         else
            raise Program_Error with
              "codegen: unsupported field access form";
         end if;

      when E_Struct_Lit | E_Variant_New | E_Tuple_Lit | E_Array_Lit =>
         raise Program_Error with
           "codegen: a struct/variant/tuple/array literal is only supported "
           & "as a let/mut initialiser in the bootstrap";


      when E_Dyn_Cast | E_Slice_Cast =>
         raise Program_Error with
           "codegen: a `&dyn` / slice coercion is only supported as a "
           & "call argument or let initialiser in the bootstrap";

      when E_Type_Intrinsic =>
         --  §6.12.1: implicitly-xlatime layout query, folded to a
         --  `uaddr` constant from the KSA layout model.
         declare
            V : Long_Long_Integer;
         begin
            case E.TI_Op is
               when TI_Size =>
                  V := Long_Long_Integer (Sizeof (E.TI_Ty));
               when TI_Align =>
                  V := Long_Long_Integer (Kurt.Layout.Align_Of (E.TI_Ty));
               when TI_Offset =>
                  V := Long_Long_Integer
                    (Kurt.Layout.Field_Offset
                       (SU.To_String (E.TI_Ty.Name),
                        SU.To_String (E.TI_Field)));
            end case;
            Lower_Imm (F, Target_Reg, V, True);
         end;

      when E_Call =>
         --  §9.5: a method call whose receiver is `&dyn Trait` dispatches
         --  dynamically; sema leaves such calls with an E_Field callee.
         if E.C_Callee.Kind = E_Field
           and then Is_Dyn_Ref (Type_Of_Expr (E.C_Callee.F_Recv, ST))
         then
            Lower_Dyn_Call (E);
            return;
         end if;
         Lower_Call (E);
         if Target_Reg /= 0 then
            IO.Put_Line (F, "    mov     " & Xreg & ", x0");
         end if;

      when E_Path =>
         --  §9.3.2 associated-const access resolved by sema to a value.
         if E.P_Assoc_Val /= null then
            Lower_Expr_Into_Reg (F, E.P_Assoc_Val, Target_Reg, ST);
            return;
         end if;
         --  §4.10: a bare subroutine name used as a value — load its
         --  address (the subroutine pointer).
         if E.P_Is_Fn_Ptr then
            declare
               Lbl : constant String :=
                 "_" & SU.To_String (E.Segments.Last_Element);
            begin
               IO.Put_Line (F, "    adrp    " & Xreg & ", " & Lbl & "@PAGE");
               IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                               & ", " & Lbl & "@PAGEOFF");
               return;
            end;
         end if;
         if Natural (E.Segments.Length) = 1 then
            declare
               Name : constant String :=
                 SU.To_String (E.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  --  §5.4: fall back to a static binding (global label).
                  declare
                     SI : constant Natural := Find_Static (Name);
                  begin
                     if SI = 0 then
                        raise Program_Error with
                          "codegen: unknown binding '" & Name & "'";
                     end if;
                     declare
                        Sz  : constant Natural :=
                          Sizeof (Unit_Statics.Element (SI).Ty);
                        Lbl : constant String := "_Kst_" & Name;
                     begin
                        IO.Put_Line (F, "    adrp    " & Xreg & ", "
                                        & Lbl & "@PAGE");
                        IO.Put_Line (F, "    add     " & Xreg & ", "
                                        & Xreg & ", " & Lbl & "@PAGEOFF");
                        if Sz >= 8 then
                           IO.Put_Line (F, "    ldr     " & Xreg
                                           & ", [" & Xreg & "]");
                        elsif Sz = 4 then
                           IO.Put_Line (F, "    ldr     " & Wreg
                                           & ", [" & Xreg & "]");
                        elsif Sz = 2 then
                           IO.Put_Line (F, "    ldrh    " & Wreg
                                           & ", [" & Xreg & "]");
                        else
                           IO.Put_Line (F, "    ldrb    " & Wreg
                                           & ", [" & Xreg & "]");
                        end if;
                        return;
                     end;
                  end;
               end if;
               declare
                  B   : constant Binding := ST.Bindings.Element (Idx);
                  Sz  : constant Natural := Sizeof (B.Ty);
                  Loc : constant String :=
                    ", [x29, #" & Img (B.Offset) & "]";
               begin
                  --  Load width matches the store width (see Store_Sized)
                  --  so e.g. a 1-cell enum discriminant round-trips.
                  if Is_Ref (B.Ty) or else Sz >= 8 then
                     IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                  elsif Sz = 4 then
                     IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                  elsif Sz = 2 then
                     IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                  else
                     IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                  end if;
               end;
            end;
         elsif Natural (E.Segments.Length) = 2 then
            --  Enum variant: materialise its discriminant value. The
            --  concrete enum is taken from Sem_Ty (so generic instances
            --  resolve to e.g. Opt$si4), falling back to the written name.
            declare
               EN : constant String :=
                 (if E.Sem_Ty /= null and then E.Sem_Ty.Kind = T_Named
                  then SU.To_String (E.Sem_Ty.Name)
                  else SU.To_String (E.Segments.First_Element));
               VN : constant String :=
                 SU.To_String (E.Segments.Last_Element);
            begin
               if Kurt.Layout.Is_Enum (EN)
                 and then Kurt.Layout.Has_Variant (EN, VN)
               then
                  Lower_Imm (F, Target_Reg,
                    Kurt.Layout.Variant_Value (EN, VN),
                    Sizeof (E.Sem_Ty) > 4);
               else
                  raise Program_Error with
                    "codegen: '" & EN & "::" & VN
                    & "' is not a known enum variant";
               end if;
            end;
         else
            raise Program_Error with
              "codegen: multi-segment path as value not supported "
              & "(only enum variants or call callees)";
         end if;

      when E_If =>
         Lower_If (E);

      when E_Match =>
         Lower_Match (E);

      when E_Binary =>
         Lower_Binary (E);

      when E_Deref =>
         Lower_Expr_Into_Reg (F, E.D_Inner, Target_Reg, ST);
         declare
            Inner_Ty : constant Type_Access := Type_Of_Expr (E.D_Inner, ST);
            Sz       : Natural := 8;
            Guarded  : Boolean := False;
         begin
            if Is_Ref (Inner_Ty) then
               Sz := Sizeof (Inner_Ty.Target);
               --  §8.5: a `guard` load is fully ordered (load-acquire).
               --  An `atomic` load needs no extra instruction — aligned
               --  loads up to 8 bytes are single-copy atomic on arm64.
               Guarded := Inner_Ty.R_Store = RS_Guard;
            end if;
            if Guarded then
               if Sz >= 8 then
                  IO.Put_Line (F, "    ldar    " & Xreg
                                  & ", [" & Xreg & "]");
               elsif Sz = 4 then
                  IO.Put_Line (F, "    ldar    " & Wreg
                                  & ", [" & Xreg & "]");
               elsif Sz = 2 then
                  IO.Put_Line (F, "    ldarh   " & Wreg
                                  & ", [" & Xreg & "]");
               else
                  IO.Put_Line (F, "    ldarb   " & Wreg
                                  & ", [" & Xreg & "]");
               end if;
            elsif Sz >= 8 then
               IO.Put_Line (F, "    ldr     " & Xreg & ", [" & Xreg & "]");
            elsif Sz = 4 then
               IO.Put_Line (F, "    ldr     " & Wreg & ", [" & Xreg & "]");
            elsif Sz = 2 then
               IO.Put_Line (F, "    ldrh    " & Wreg & ", [" & Xreg & "]");
            else
               IO.Put_Line (F, "    ldrb    " & Wreg & ", [" & Xreg & "]");
            end if;
         end;

      when E_Ref =>
         --  §8.1 reference creation: materialise the address of the place.
         --  Bootstrap places: a binding (its frame slot), a field of a
         --  binding (slot + field offset), or a reref `&mods *expr` (the
         --  referent address is the inner reference's value).
         if E.Rf_Place.Kind = E_Path
           and then Natural (E.Rf_Place.Segments.Length) = 1
         then
            declare
               Name : constant String :=
                 SU.To_String (E.Rf_Place.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  --  §5.4: the address of a static binding.
                  if Find_Static (Name) /= 0 then
                     declare
                        Lbl : constant String := "_Kst_" & Name;
                     begin
                        IO.Put_Line (F, "    adrp    " & Xreg & ", "
                                        & Lbl & "@PAGE");
                        IO.Put_Line (F, "    add     " & Xreg & ", "
                                        & Xreg & ", " & Lbl
                                        & "@PAGEOFF");
                     end;
                     return;
                  end if;
                  raise Program_Error with
                    "codegen: unknown binding '" & Name & "'";
               end if;
               IO.Put_Line (F, "    add     " & Xreg & ", x29, #"
                               & Img (ST.Bindings.Element (Idx).Offset));
            end;
         elsif E.Rf_Place.Kind = E_Field
           and then E.Rf_Place.F_Recv.Kind = E_Path
           and then Natural (E.Rf_Place.F_Recv.Segments.Length) = 1
         then
            declare
               Name : constant String :=
                 SU.To_String (E.Rf_Place.F_Recv.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  raise Program_Error with
                    "codegen: unknown binding '" & Name & "'";
               end if;
               declare
                  B     : constant Binding := ST.Bindings.Element (Idx);
                  FName : constant String  :=
                    SU.To_String (E.Rf_Place.F_Name);
                  Off   : Natural;
               begin
                  if B.Ty /= null and then B.Ty.Kind = T_Tuple then
                     Off := B.Offset + Kurt.Layout.Tuple_Field_Offset
                       (B.Ty, Natural'Value (FName));
                  else
                     Off := B.Offset + Kurt.Layout.Field_Offset
                       (SU.To_String (B.Ty.Name), FName);
                  end if;
                  IO.Put_Line (F, "    add     " & Xreg & ", x29, #"
                                  & Img (Off));
               end;
            end;
         elsif E.Rf_Place.Kind = E_Deref then
            --  Reref (§8.1.3): the new reference designates the same
            --  storage as the dereferenced source reference.
            Lower_Expr_Into_Reg (F, E.Rf_Place.D_Inner, Target_Reg, ST);
         else
            raise Program_Error with
              "codegen: unsupported place in reference creation "
              & "(bootstrap accepts a binding, a field, or a reref)";
         end if;

      when E_CAS =>
         --  §8.7 compare-and-swap via an exclusive load/store loop.
         --  Result: the verdict.<T, T> aggregate (≤ 8 bytes) built in
         --  x<Target_Reg> with the discriminant at bit 0 and the payload
         --  (old value on success, actual on failure) at its field offset.
         declare
            Tgt_Ty : constant Type_Access := Type_Of_Expr (E.CAS_Tgt, ST);
            Ref_T  : constant Type_Access :=
              (if Is_Ref (Tgt_Ty) then Tgt_Ty.Target else null);
            Sz     : constant Natural := Sizeof (Ref_T);
            EN     : constant String :=
              (if E.Sem_Ty /= null then SU.To_String (E.Sem_Ty.Name)
               else "");
            Acq    : constant Boolean :=
              Is_Ref (Tgt_Ty) and then Tgt_Ty.R_Store = RS_Guard;
            FN     : constant String  := SU.To_String (ST.Fn_Name);
            Idx    : constant Natural := ST.If_Idx;
            L_Top  : constant String :=
              "Lcas_" & FN & "_top_" & Img (Idx);
            L_Fail : constant String :=
              "Lcas_" & FN & "_fail_" & Img (Idx);
            L_Done : constant String :=
              "Lcas_" & FN & "_done_" & Img (Idx);
            --  Width-specific exclusive mnemonics. `guard` uses the
            --  acquire/release forms (fully ordered); `atomic` the plain
            --  exclusive forms (unordered).
            Lx : constant String :=
              (if Sz = 1 then (if Acq then "ldaxrb" else "ldxrb")
               elsif Sz = 2 then (if Acq then "ldaxrh" else "ldxrh")
               else (if Acq then "ldaxr" else "ldxr"));
            Sx : constant String :=
              (if Sz = 1 then (if Acq then "stlxrb" else "stxrb")
               elsif Sz = 2 then (if Acq then "stlxrh" else "stxrh")
               else (if Acq then "stlxr" else "stxr"));
            VR : constant String := (if Sz >= 8 then "x13" else "w13");
            NR : constant String := (if Sz >= 8 then "x11" else "w11");
            CR : constant String := (if Sz >= 8 then "x10" else "w10");
         begin
            if EN = "" or else Sizeof (E.Sem_Ty) > 8 then
               raise Program_Error with
                 "codegen: CAS result wider than 8 bytes is not yet "
                 & "supported (referent must be ui1/ui2/ui4)";
            end if;
            ST.If_Idx := ST.If_Idx + 1;

            --  Evaluate target address, expected, and new value.
            Lower_Expr_Into_Reg (F, E.CAS_Tgt, 9, ST);
            IO.Put_Line (F, "    sub     sp, sp, #16");
            IO.Put_Line (F, "    str     x9, [sp]");
            Lower_Expr_Into_Reg (F, E.CAS_Exp, 9, ST);
            IO.Put_Line (F, "    str     x9, [sp, #8]");
            Lower_Expr_Into_Reg (F, E.CAS_New, 11, ST);
            IO.Put_Line (F, "    ldr     x10, [sp, #8]");
            IO.Put_Line (F, "    ldr     x9, [sp]");
            IO.Put_Line (F, "    add     sp, sp, #16");

            IO.Put_Line (F, L_Top & ":");
            IO.Put_Line (F, "    " & Lx & "   " & VR & ", [x9]");
            IO.Put_Line (F, "    cmp     " & VR & ", " & CR);
            --  eq-CAS swaps on equal (branch away when not equal);
            --  ne-CAS swaps on not-equal (branch away when equal).
            IO.Put_Line (F, "    b." & (if E.CAS_Ne then "eq" else "ne")
                            & "    " & L_Fail);
            IO.Put_Line (F, "    " & Sx & "  w12, " & NR & ", [x9]");
            IO.Put_Line (F, "    cbnz    w12, " & L_Top);
            Lower_Imm (F, 12, Kurt.Layout.Variant_Value
              (EN, Kurt.Layout.Contract_Success_Variant (EN)), False);
            IO.Put_Line (F, "    b       " & L_Done);
            IO.Put_Line (F, L_Fail & ":");
            IO.Put_Line (F, "    clrex");
            Lower_Imm (F, 12, Kurt.Layout.Variant_Value
              (EN, Kurt.Layout.Contract_Fail_Variant (EN)), False);
            IO.Put_Line (F, L_Done & ":");

            --  Pack the aggregate: payload (w13) at its field offset,
            --  discriminant (w12) at offset 0.
            declare
               PO : constant Natural := Kurt.Layout.Variant_Field_Offset
                 (E.Sem_Ty, Kurt.Layout.Contract_Success_Variant (EN), 1);
            begin
               IO.Put_Line (F, "    lsl     " & Xreg & ", x13, #"
                               & Img (8 * PO));
               IO.Put_Line (F, "    orr     " & Xreg & ", " & Xreg
                               & ", x12");
            end;
         end;

      when E_Cast =>
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

      when E_Question =>
         --  §6.2.4 / §7.2.4 contract propagation. Bootstrap restriction:
         --  the operand shall be a binding (single-segment path) so the
         --  enum aggregate is already materialised in a frame slot.
         declare
            Inner : constant Expr_Access := E.Q_Inner;
            Inner_Ty : constant Type_Access := Type_Of_Expr (Inner, ST);
            EN  : constant String := SU.To_String (Inner_Ty.Name);
            Bi  : constant Natural := Find_Binding
              (ST, SU.To_String (Inner.Segments.Last_Element));
            B   : constant Binding := ST.Bindings.Element (Bi);
            DS  : constant Natural := Kurt.Layout.Enum_Disc_Size (EN);
            Succ_V : constant String :=
              Kurt.Layout.Contract_Success_Variant (EN);
            Succ_Disc : constant Long_Long_Integer :=
              Kurt.Layout.Variant_Value (EN, Succ_V);
            FN_S : constant String := SU.To_String (ST.Fn_Name);
            Idx  : constant Natural := ST.If_Idx;
            L_Fail : constant String :=
              "Lq_" & FN_S & "_fail_" & Img (Idx);
            L_Done : constant String :=
              "Lq_" & FN_S & "_done_" & Img (Idx);
            Pay_Off : constant Natural :=
              B.Offset + Kurt.Layout.Variant_Field_Offset
                           (Inner_Ty, Succ_V, 1);
            Pay_Ty  : constant Type_Access :=
              Kurt.Layout.Variant_Field_Type (Inner_Ty, Succ_V, 1);
            Pay_Sz  : constant Natural := Sizeof (Pay_Ty);
            Whole_Sz : constant Natural := Sizeof (Inner_Ty);
            Loc_P : constant String :=
              ", [x29, #" & Img (Pay_Off) & "]";
            Loc_W : constant String :=
              ", [x29, #" & Img (B.Offset) & "]";
         begin
            ST.If_Idx := ST.If_Idx + 1;
            if Bi = 0 or else Inner.Kind /= E_Path
              or else Natural (Inner.Segments.Length) /= 1
            then
               raise Program_Error with
                 "codegen: `?` operand must be a binding (bootstrap)";
            end if;
            --  Load discriminant from offset 0 of the inner's slot.
            if DS = 1 then
               IO.Put_Line (F, "    ldrb    w9" & Loc_W);
            elsif DS = 2 then
               IO.Put_Line (F, "    ldrh    w9" & Loc_W);
            elsif DS = 4 then
               IO.Put_Line (F, "    ldr     w9" & Loc_W);
            else
               IO.Put_Line (F, "    ldr     x9" & Loc_W);
            end if;
            Lower_Imm (F, 10, Succ_Disc, False);
            IO.Put_Line (F, "    cmp     w9, w10");
            IO.Put_Line (F, "    b.ne    " & L_Fail);
            --  Success: load payload field 1 into Target_Reg.
            if Pay_Sz >= 8 then
               IO.Put_Line (F, "    ldr     " & Xreg & Loc_P);
            elsif Pay_Sz = 4 then
               IO.Put_Line (F, "    ldr     " & Wreg & Loc_P);
            elsif Pay_Sz = 2 then
               IO.Put_Line (F, "    ldrh    " & Wreg & Loc_P);
            else
               IO.Put_Line (F, "    ldrb    " & Wreg & Loc_P);
            end if;
            IO.Put_Line (F, "    b       " & L_Done);
            --  Failure: return the inner verdict via x0 (aggregate ABI for
            --  contract enums up to 8 bytes; the caller receives x0 with the
            --  same bit pattern). Larger contract types are deferred.
            IO.Put_Line (F, L_Fail & ":");
            if Whole_Sz >= 8 then
               IO.Put_Line (F, "    ldr     x0" & Loc_W);
            elsif Whole_Sz = 4 then
               IO.Put_Line (F, "    ldr     w0" & Loc_W);
            elsif Whole_Sz = 2 then
               IO.Put_Line (F, "    ldrh    w0" & Loc_W);
            else
               IO.Put_Line (F, "    ldrb    w0" & Loc_W);
            end if;
            IO.Put_Line (F, "    b       "
                            & SU.To_String (ST.Epilogue_Lbl));
            IO.Put_Line (F, L_Done & ":");
         end;

      when E_Unary =>
         --  §6.3.1 negation (two's complement) / §6.5.3 bitwise NOT
         --  (one's complement) / §7.2.1 contract polarity inversion.
         Lower_Expr_Into_Reg (F, E.U_Operand, Target_Reg, ST);
         declare
            OT : constant Type_Access := Type_Of_Expr (E.U_Operand, ST);
         begin
            if E.U_Op = U_Not and then Is_Contract_Ty (OT) then
               --  §7.2.1: exchange the success/failure variants of the
               --  self-inverse contract (sema guarantees symmetric
               --  payloads, so the payload bits are preserved unchanged;
               --  only the discriminant is rewritten).
               declare
                  Is_Bool : constant Boolean :=
                    SU.To_String (OT.Name) = "bool";
                  Has_Pay : constant Boolean :=
                    not Is_Bool and then Kurt.Layout.Enum_Has_Payload
                      (SU.To_String (OT.Name));
                  DSz : constant Natural :=
                    (if Is_Bool then 1
                     else Kurt.Layout.Enum_Disc_Size
                       (SU.To_String (OT.Name)));
               begin
                  if Has_Pay then
                     --  Whole ≤8B aggregate in the register: test the
                     --  masked discriminant, then bfi the flipped one.
                     IO.Put_Line (F, "    and     x12, " & Xreg & ", #0x"
                       & (case DSz is
                             when 1 => "ff", when 2 => "ffff",
                             when others => "ffffffff"));
                     Lower_Imm (F, 13, Contract_Succ_Val (OT), True);
                     IO.Put_Line (F, "    cmp     x12, x13");
                     Lower_Imm (F, 12, Contract_Fail_Val (OT), True);
                     IO.Put_Line (F, "    csel    x12, x12, x13, eq");
                     IO.Put_Line (F, "    bfi     " & Xreg
                                     & ", x12, #0, #" & Img (8 * DSz));
                  else
                     --  Scalar discriminant: select the opposite value.
                     Lower_Imm (F, 12, Contract_Succ_Val (OT), True);
                     IO.Put_Line (F, "    cmp     " & Xreg & ", x12");
                     Lower_Imm (F, 12, Contract_Fail_Val (OT), True);
                     Lower_Imm (F, 13, Contract_Succ_Val (OT), True);
                     IO.Put_Line (F, "    csel    " & Xreg
                                     & ", x12, x13, eq");
                  end if;
               end;
               return;
            end if;
            declare
               Mn   : constant String :=
                 (if E.U_Op = U_Neg then "neg " else "mvn ");
               Wide : constant Boolean := Sizeof (OT) > 4;
            begin
               if Wide then
                  IO.Put_Line (F, "    " & Mn & "    " & Xreg & ", " & Xreg);
               else
                  IO.Put_Line (F, "    " & Mn & "    " & Wreg & ", " & Wreg);
               end if;
            end;
         end;
   end case;
end Lower_Expr_Into_Reg;
