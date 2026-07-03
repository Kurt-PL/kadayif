separate (Kurt.Codegen.Lower_Expr_Into_Reg)
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

      --  §8.8.2: a `destruct`-typed argument is transferred (moved) into the
      --  call; skip the source's scope-exit destructor.
      for K in E.C_Args.First_Index .. E.C_Args.Last_Index loop
         Note_Move (F, ST, E.C_Args.Element (K));
      end loop;

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

      if E.C_Indirect then
         --  §4.10 indirect call: the fixed args are already in x0..x7, so
         --  load the subroutine-pointer value into x9 (a binding/field load
         --  does not touch the argument registers) and branch to it.
         Lower_Expr_Into_Reg (F, E.C_Callee, 9, ST);
         IO.Put_Line (F, "    blr     x9");
      else
         IO.Put_Line (F, "    bl      " & Sym);
      end if;

      if Total > 0 then
         IO.Put_Line (F, "    add     sp, sp, #" & Img (Total));
      end if;
   end Lower_Call;
