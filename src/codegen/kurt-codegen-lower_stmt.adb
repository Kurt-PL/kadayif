--  Statement lowering (subunit of Kurt.Codegen).
--  Sees all of the parent body's declarations and recurses into
--  Lower_Expr_Into_Reg / Lower_Stmt freely.

separate (Kurt.Codegen)
procedure Lower_Stmt
  (F  : IO.File_Type;
   S  : Stmt_Access;
   ST : in out Lower_State)
is
   --  §7.9: resolve the loop targeted by a `break`/`continue`. An empty
   --  label denotes the innermost loop; a non-empty label selects the
   --  nearest enclosing loop with that source name.
   function Target_Loop
     (ST : Lower_State; Label : SU.Unbounded_String) return Loop_Labels is
   begin
      if SU.Length (Label) = 0 then
         return ST.Loops.Last_Element;
      end if;
      for I in reverse ST.Loops.First_Index .. ST.Loops.Last_Index loop
         if SU.To_String (ST.Loops.Element (I).Name)
              = SU.To_String (Label)
         then
            return ST.Loops.Element (I);
         end if;
      end loop;
      raise Program_Error with
        "codegen: break/continue to unknown loop label '"
        & SU.To_String (Label) & "'";
   end Target_Loop;


   --  Store the value currently in x9/w9 to [x29, Off] using the width
   --  implied by Sz cells.
   procedure Store_Sized (Off : Natural; Sz : Natural) is
      Loc : constant String := ", [x29, #" & Img (Off) & "]";
   begin
      if Sz >= 8 then
         IO.Put_Line (F, "    str     x9" & Loc);
      elsif Sz = 4 then
         IO.Put_Line (F, "    str     w9" & Loc);
      elsif Sz = 2 then
         IO.Put_Line (F, "    strh    w9" & Loc);
      elsif Sz = 1 then
         IO.Put_Line (F, "    strb    w9" & Loc);
      end if;  --  Sz = 0 (void): nothing to store
   end Store_Sized;

   procedure Zero_Fill (Off : Natural; Sz : Natural) is
      Curr : Natural := Off;
      Rem_Sz : Natural := Sz;
   begin
      while Rem_Sz >= 8 loop
         IO.Put_Line (F, "    str     xzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 8;
         Rem_Sz := Rem_Sz - 8;
      end loop;
      if Rem_Sz >= 4 then
         IO.Put_Line (F, "    str     wzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 4;
         Rem_Sz := Rem_Sz - 4;
      end if;
      if Rem_Sz >= 2 then
         IO.Put_Line (F, "    strh    wzr, [x29, #" & Img (Curr) & "]");
         Curr := Curr + 2;
         Rem_Sz := Rem_Sz - 2;
      end if;
      if Rem_Sz >= 1 then
         IO.Put_Line (F, "    strb    wzr, [x29, #" & Img (Curr) & "]");
      end if;
   end Zero_Fill;

   --  §6.4.3 widening `a +@ b` / `a *@ b`: materialise the .{low, high}
   --  tuple at Off+0 (low) and Off+W (high). Operand type T is W bytes.
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

   --  Materialise a tuple-typed initialiser into the frame slot at Off.
   procedure Store_Tuple_Init
     (Off : Natural; Tup : Type_Access; Init : Expr_Access)
   is
   begin
      if Init.Kind = E_Tuple_Lit then
         for I in Init.TL_Elems.First_Index .. Init.TL_Elems.Last_Index loop
            declare
               Idx : constant Natural := I - Init.TL_Elems.First_Index;
            begin
               Lower_Expr_Into_Reg (F, Init.TL_Elems.Element (I), 9, ST);
               Store_Sized
                 (Off + Kurt.Layout.Tuple_Field_Offset (Tup, Idx),
                  Sizeof (Kurt.Layout.Tuple_Field_Type (Tup, Idx)));
            end;
         end loop;
      elsif Init.Kind = E_Binary
        and then (Init.B_Op = B_Wide_Add or else Init.B_Op = B_Wide_Mul)
      then
         Lower_Widening (Off, Init, Kurt.Layout.Tuple_Field_Offset (Tup, 1));
      else
         raise Program_Error with
           "codegen: unsupported tuple initialiser";
      end if;
   end Store_Tuple_Init;

   --  §8.4 lower a brace-delimited statement list as a lexical scope: the
   --  block's `with destruct` locals are destroyed (LIFO) at its textual
   --  end — before any enclosing-scope object — and then leave scope so the
   --  fn epilogue does not destroy them again. An early `return` inside the
   --  block runs its own inline drops (it never reaches this textual end).
   procedure Lower_Scoped (Stmts : Stmt_Vectors.Vector) is
      Entry_Len : constant Natural := Natural (ST.Bindings.Length);
   begin
      for I in Stmts.First_Index .. Stmts.Last_Index loop
         Lower_Stmt (F, Stmts.Element (I), ST);
      end loop;
      Emit_Binding_Drops (F, ST, Keep => Entry_Len, Preserve_Ret => False);
      while Natural (ST.Bindings.Length) > Entry_Len loop
         ST.Bindings.Delete_Last;
      end loop;
   end Lower_Scoped;
begin
   case S.Kind is
      when S_Return =>
         --  AAPCS64 aggregate returns: ≤8B in x0 (the scalar path below),
         --  9–16B in x0+x1, >16B copied through the incoming x8 pointer.
         case Classify_Agg (ST.Ret_Ty) is
            when Two_Regs | Indirect =>
               if S.R_Val = null or else S.R_Val.Kind /= E_Path
                 or else Natural (S.R_Val.Segments.Length) /= 1
                 or else Find_Binding
                   (ST, SU.To_String (S.R_Val.Segments.Last_Element)) = 0
               then
                  raise Program_Error with
                    "codegen: a wide aggregate return value must be a "
                    & "binding (bootstrap)";
               end if;
               declare
                  B : constant Binding := ST.Bindings.Element
                    (Find_Binding
                       (ST, SU.To_String (S.R_Val.Segments.Last_Element)));
               begin
                  if Classify_Agg (ST.Ret_Ty) = Two_Regs then
                     IO.Put_Line (F, "    ldr     x0, [x29, #"
                                     & Img (B.Offset) & "]");
                     IO.Put_Line (F, "    ldr     x1, [x29, #"
                                     & Img (B.Offset + 8) & "]");
                  else
                     IO.Put_Line (F, "    ldr     x10, [x29, #"
                                     & Img (Natural (ST.Sret_Off)) & "]");
                     Emit_Mem_Copy (F, "x29", B.Offset, "x10", 0,
                                    Sizeof (ST.Ret_Ty));
                  end if;
               end;
            when Not_Agg | One_Reg =>
               Lower_Expr_Into_Reg (F, S.R_Val, 0, ST);
         end case;
         --  §8.8.2: returning a binding transfers it (skip its drop).
         Note_Move (F, ST, S.R_Val);
         --  §8.4 destroy every binding live at this return point — exactly
         --  the in-scope set, since bindings declared after are not yet in
         --  ST.Bindings and inner-block locals declared before still are.
         --  The return value (x0/x1) is preserved across the drops; then
         --  branch to the bare epilogue (which performs no further drops).
         Emit_Binding_Drops (F, ST, Keep => 0, Preserve_Ret => True);
         IO.Put_Line (F, "    b       "
                         & SU.To_String (ST.Epilogue_Lbl) & "_bare");

      when S_Expr =>
         --  Evaluate for effect into a scratch register; result ignored.
         Lower_Expr_Into_Reg (F, S.E_Val, 9, ST);

      when S_Airside_Block =>
         Lower_Scoped (S.A_Stmts);

      when S_Let | S_Mut =>
         --  Allocate a slot, evaluate the initialiser (if any), store it,
         --  and register the binding. §5.2 lets `mut` omit the
         --  initialiser. Per §2.2.3 every binding object — struct or
         --  scalar — gets a stack slot (never a register).
         --  §6.1.8: `= uninit` allocates the slot and registers the binding
         --  but performs no store, exactly like an omitted initialiser.
         if S.L_Init /= null and then S.L_Init.Kind = E_Uninit then
            S.L_Init := null;
         end if;
         --  §8.8.2: initialising from a binding transfers it (skip its drop).
         Note_Move (F, ST, S.L_Init);
         declare
            Ty : Type_Access := S.L_Ty;
         begin
            if Ty = null and then S.L_Init /= null then
               Ty := Type_Of_Expr (S.L_Init, ST);
            end if;

            declare
               --  Aggregates that live in RAM (struct / payload enum /
               --  tuple / array); a unit-only enum is a scalar. A `&[T]`
               --  slice or `&dyn Trait` is a 16-byte fat reference.
               Is_Agg  : constant Boolean := Is_Aggregate_Type (Ty);
               Is_Fat  : constant Boolean :=
                 Is_Slice_Ref (Ty) or else Is_Dyn_Ref (Ty);
               Slot : constant Natural :=
                 (if Is_Fat then 16
                  elsif Is_Agg then ((Sizeof (Ty) + 7) / 8) * 8 else 8);
               Off  : constant Natural := ST.Next_Offset;
            begin
               ST.Next_Offset := ST.Next_Offset + Slot;

               if Is_Fat then
                  --  §4.6 / §9.5 fat-reference initialiser.
                  if S.L_Init = null then
                     null;  --  mut without initialiser
                  elsif S.L_Init.Kind = E_Slice_Cast then
                     Lower_Expr_Into_Reg (F, S.L_Init.SC_Inner, 9, ST);
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (Off) & "]");
                     Lower_Imm (F, 9,
                       Long_Long_Integer (S.L_Init.SC_Len), True);
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (Off + 8) & "]");
                  elsif S.L_Init.Kind = E_String_Lit then
                     declare
                        Label : constant String := "Lstr" & Img (ST.Next_Str_Idx);
                     begin
                        ST.Next_Str_Idx := ST.Next_Str_Idx + 1;
                        IO.Put_Line (F, "    adrp    x9, " & Label & "@PAGE");
                        IO.Put_Line (F, "    add     x9, x9, " & Label & "@PAGEOFF");
                        IO.Put_Line (F, "    str     x9, [x29, #" & Img (Off) & "]");
                        Lower_Imm (F, 9,
                          Long_Long_Integer (SU.Length (S.L_Init.Str_Bytes)), True);
                        IO.Put_Line (F, "    str     x9, [x29, #"
                                        & Img (Off + 8) & "]");
                     end;
                  elsif S.L_Init.Kind = E_Path
                    and then Natural (S.L_Init.Segments.Length) = 1
                    and then Find_Binding
                      (ST, SU.To_String (S.L_Init.Segments.Last_Element))
                        /= 0
                  then
                     --  copy another fat reference binding (both halves)
                     declare
                        SB : constant Binding := ST.Bindings.Element
                          (Find_Binding
                             (ST, SU.To_String
                                (S.L_Init.Segments.Last_Element)));
                     begin
                        Emit_Mem_Copy (F, "x29", SB.Offset, "x29", Off, 16);
                     end;
                  elsif S.L_Init.Kind = E_Deref then
                     --  §9.5 load a fat reference from memory, e.g. an
                     --  element of a `[&dyn T; N]` array via
                     --  `*(arr.ptr + i)`. The address is in x10; copy the
                     --  two pointer-sized halves into the slot.
                     Lower_Expr_Into_Reg (F, S.L_Init.D_Inner, 10, ST);
                     IO.Put_Line (F, "    ldr     x9, [x10]");
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (Off) & "]");
                     IO.Put_Line (F, "    ldr     x9, [x10, #8]");
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (Off + 8) & "]");
                  else
                     raise Program_Error with
                       "codegen: unsupported fat-reference initialiser";
                  end if;
                  ST.Bindings.Append
                    ((Name => S.L_Name, Offset => Off, Ty => Ty));
               elsif Is_Agg then
                  if S.L_Init = null then
                     null;  --  mut without initialiser
                  elsif S.L_Init.Kind = E_Struct_Lit then
                     Zero_Fill (Off, Sizeof (Ty));
                     declare
                        --  Concrete struct name (post-monomorphisation)
                        --  from the inferred type, falling back to the
                        --  literal's written name.
                        SN : constant String :=
                          (if S.L_Init.Sem_Ty /= null
                           then SU.To_String (S.L_Init.Sem_Ty.Name)
                           else SU.To_String (S.L_Init.SL_Name));
                     begin
                        for I in S.L_Init.SL_Fields.First_Index ..
                                 S.L_Init.SL_Fields.Last_Index
                        loop
                           declare
                              FI : constant Field_Init :=
                                S.L_Init.SL_Fields.Element (I);
                              FN : constant String := SU.To_String (FI.Name);
                           begin
                              Lower_Expr_Into_Reg (F, FI.Val, 9, ST);
                              Store_Sized
                                (Off + Kurt.Layout.Field_Offset (SN, FN),
                                 Sizeof (Kurt.Layout.Field_Type (SN, FN)));
                              --  §8.8.2 a transferred field source is not
                              --  dropped at its own scope exit.
                              Note_Move (F, ST, FI.Val);
                           end;
                        end loop;

                        --  §5.5.3: fill each omitted field from its
                        --  default-value expression, evaluated here at the
                        --  point of construction.
                        for K in 1 .. Kurt.Layout.Struct_Field_Count (SN) loop
                           declare
                              FN  : constant String :=
                                Kurt.Layout.Struct_Field_Name (SN, K);
                              Dfl : constant Expr_Access :=
                                Kurt.Layout.Field_Default (SN, FN);
                              Supplied : Boolean := False;
                           begin
                              for I in S.L_Init.SL_Fields.First_Index ..
                                       S.L_Init.SL_Fields.Last_Index
                              loop
                                 if SU.To_String
                                      (S.L_Init.SL_Fields.Element (I).Name)
                                      = FN
                                 then
                                    Supplied := True;
                                 end if;
                              end loop;
                              if not Supplied and then Dfl /= null then
                                 Lower_Expr_Into_Reg (F, Dfl, 9, ST);
                                 Store_Sized
                                   (Off + Kurt.Layout.Field_Offset (SN, FN),
                                    Sizeof
                                      (Kurt.Layout.Field_Type (SN, FN)));
                              end if;
                           end;
                        end loop;
                     end;
                  elsif S.L_Init.Kind = E_Range then
                     --  §4.8 range literal: store `start` at offset 0 and
                     --  `end` at size(T), the two T-typed fields in place.
                     declare
                        Elem_Sz : constant Natural :=
                          (if Ty.Rng_Elem /= null
                           then Sizeof (Ty.Rng_Elem) else 8);
                        Is_FP   : constant Boolean := Is_Float (Ty.Rng_Elem);
                     begin
                        if Is_FP then
                           Lower_Float_Into_D (F, S.L_Init.Rg_Lo, 0, ST);
                           IO.Put_Line (F, "    str     "
                             & (if Elem_Sz = 4 then "s0" else "d0")
                             & ", [x29, #" & Img (Off) & "]");
                           Lower_Float_Into_D (F, S.L_Init.Rg_Hi, 0, ST);
                           IO.Put_Line (F, "    str     "
                             & (if Elem_Sz = 4 then "s0" else "d0")
                             & ", [x29, #" & Img (Off + Elem_Sz) & "]");
                        else
                           Lower_Expr_Into_Reg (F, S.L_Init.Rg_Lo, 9, ST);
                           Store_Sized (Off, Elem_Sz);
                           Lower_Expr_Into_Reg (F, S.L_Init.Rg_Hi, 9, ST);
                           Store_Sized (Off + Elem_Sz, Elem_Sz);
                        end if;
                     end;
                   elsif S.L_Init.Kind = E_Variant_New then
                      Zero_Fill (Off, Sizeof (Ty));
                      --  Discriminant at the slot start, then payload.
                      declare
                        EN : constant String :=
                          (if S.L_Init.Sem_Ty /= null
                           then SU.To_String (S.L_Init.Sem_Ty.Name)
                           else SU.To_String (S.L_Init.VN_Enum));
                        VN : constant String :=
                          SU.To_String (S.L_Init.VN_Variant);
                     begin
                        --  A void discriminant (§4.11.3) stores nothing.
                        if Kurt.Layout.Enum_Disc_Size (EN) > 0 then
                           Lower_Imm (F, 9,
                             Kurt.Layout.Variant_Value (EN, VN), False);
                           Store_Sized
                             (Off, Kurt.Layout.Enum_Disc_Size (EN));
                        end if;
                        for I in S.L_Init.VN_Fields.First_Index ..
                                 S.L_Init.VN_Fields.Last_Index
                        loop
                           declare
                              FI : constant Field_Init :=
                                S.L_Init.VN_Fields.Element (I);
                              FN : constant String := SU.To_String (FI.Name);
                              --  §4.5: an intrinsic verdict instance carries
                              --  its element types in Sem_Ty's args, so pass
                              --  the type when available (handles verdict and,
                              --  via delegation, every declared enum too).
                              ST_T : constant Type_Access := S.L_Init.Sem_Ty;
                              FO : constant Integer :=
                                (if ST_T /= null
                                 then Kurt.Layout.Variant_Field_Offset_By_Name
                                        (ST_T, VN, FN)
                                 else Kurt.Layout.Variant_Field_Offset_By_Name
                                        (EN, VN, FN));
                              FT : constant Type_Access :=
                                (if ST_T /= null
                                 then Kurt.Layout.Variant_Field_Type_By_Name
                                        (ST_T, VN, FN)
                                 else Kurt.Layout.Variant_Field_Type_By_Name
                                        (EN, VN, FN));
                           begin
                              Lower_Expr_Into_Reg (F, FI.Val, 9, ST);
                              Store_Sized (Off + Natural (FO), Sizeof (FT));
                              --  §8.8.2 a transferred payload source is not
                              --  dropped at its own scope exit.
                              Note_Move (F, ST, FI.Val);
                           end;
                        end loop;
                     end;
                  elsif Ty.Kind = T_Array
                    and then S.L_Init.Kind = E_Array_Lit
                  then
                     --  §6.1.6 array / repeat literal, element-wise into
                     --  the slot at the element stride.
                     declare
                        ESz   : constant Natural := Sizeof (Ty.Elem);
                        Is_FP : constant Boolean := Is_Float (Ty.Elem);
                        --  §9.5: an array of `&dyn Trait` (or `&[T]`) holds
                        --  16-byte fat references; each element coerces via
                        --  an E_Dyn_Cast / E_Slice_Cast.
                        Is_Fat_E : constant Boolean :=
                          Is_Dyn_Ref (Ty.Elem) or else Is_Slice_Ref (Ty.Elem);

                        procedure Store_Fat (EO : Natural; Elem : Expr_Access)
                        is
                        begin
                           if Elem.Kind = E_Dyn_Cast then
                              Lower_Expr_Into_Reg (F, Elem.DC_Inner, 9, ST);
                              IO.Put_Line (F, "    str     x9, [x29, #"
                                              & Img (EO) & "]");
                              declare
                                 Lbl : constant String := "_Ldtable_"
                                   & SU.To_String (Elem.DC_Conc) & "_"
                                   & SU.To_String (Elem.DC_Trait);
                              begin
                                 IO.Put_Line (F, "    adrp    x9, " & Lbl
                                                 & "@PAGE");
                                 IO.Put_Line (F, "    add     x9, x9, "
                                                 & Lbl & "@PAGEOFF");
                                 IO.Put_Line (F, "    str     x9, [x29, #"
                                                 & Img (EO + 8) & "]");
                              end;
                           elsif Elem.Kind = E_Slice_Cast then
                              Lower_Expr_Into_Reg (F, Elem.SC_Inner, 9, ST);
                              IO.Put_Line (F, "    str     x9, [x29, #"
                                              & Img (EO) & "]");
                              Lower_Imm (F, 9,
                                Long_Long_Integer (Elem.SC_Len), True);
                              IO.Put_Line (F, "    str     x9, [x29, #"
                                              & Img (EO + 8) & "]");
                           else
                              raise Program_Error with
                                "codegen: fat-ref array element must be a "
                                & "&dyn / slice coercion";
                           end if;
                        end Store_Fat;

                        procedure Store_Elem_At (EO : Natural) is
                        begin
                           if Is_FP then
                              IO.Put_Line
                                (F, "    str     "
                                    & (if ESz = 4 then "s0" else "d0")
                                    & ", [x29, #" & Img (EO) & "]");
                           else
                              Store_Sized (EO, ESz);
                           end if;
                        end Store_Elem_At;
                     begin
                        if Is_Fat_E then
                           --  16-byte fat-ref elements (no repeat form: a
                           --  fat ref is not trivially copyable here).
                           for I in S.L_Init.AL_Elems.First_Index ..
                                    S.L_Init.AL_Elems.Last_Index
                           loop
                              Store_Fat
                                (Off + (I - S.L_Init.AL_Elems.First_Index)
                                       * ESz,
                                 S.L_Init.AL_Elems.Element (I));
                           end loop;
                           goto Fat_Done;
                        end if;
                        if S.L_Init.AL_Repeat > 0 then
                           --  `[v; N]`: evaluate v once, store N times.
                           if Is_FP then
                              Lower_Float_Into_D
                                (F, S.L_Init.AL_Elems.First_Element, 0, ST);
                           else
                              Lower_Expr_Into_Reg
                                (F, S.L_Init.AL_Elems.First_Element, 9, ST);
                           end if;
                           for I in 0 .. S.L_Init.AL_Repeat - 1 loop
                              Store_Elem_At (Off + I * ESz);
                           end loop;
                        else
                           for I in S.L_Init.AL_Elems.First_Index ..
                                    S.L_Init.AL_Elems.Last_Index
                           loop
                              if Is_FP then
                                 Lower_Float_Into_D
                                   (F, S.L_Init.AL_Elems.Element (I), 0, ST);
                              else
                                 Lower_Expr_Into_Reg
                                   (F, S.L_Init.AL_Elems.Element (I), 9, ST);
                              end if;
                              Store_Elem_At
                                (Off
                                 + (I - S.L_Init.AL_Elems.First_Index)
                                   * ESz);
                           end loop;
                        end if;
                        <<Fat_Done>>
                     end;
                  elsif Ty.Kind = T_Tuple then
                     --  §4.7 tuple literal or §6.4.3 widening result.
                     Store_Tuple_Init (Off, Ty, S.L_Init);
                  elsif S.L_Init.Kind = E_Path
                    and then Natural (S.L_Init.Segments.Length) = 1
                    and then Find_Binding
                      (ST, SU.To_String (S.L_Init.Segments.Last_Element))
                        /= 0
                  then
                     --  §8.8.1 aggregate copy init: `let a: T = b;`.
                     Emit_Mem_Copy
                       (F, "x29",
                        ST.Bindings.Element
                          (Find_Binding
                             (ST, SU.To_String
                                (S.L_Init.Segments.Last_Element))).Offset,
                        "x29", Off, Sizeof (Ty));
                  elsif S.L_Init.Kind = E_Path then
                     --  Unit enum variant: store its discriminant. A
                     --  void discriminant (§4.11.3) stores nothing.
                     if Kurt.Layout.Enum_Disc_Size
                          (SU.To_String (Ty.Name)) > 0
                     then
                        Lower_Expr_Into_Reg (F, S.L_Init, 9, ST);
                        Store_Sized
                          (Off, Kurt.Layout.Enum_Disc_Size
                                  (SU.To_String (Ty.Name)));
                     end if;
                  elsif S.L_Init.Kind = E_Call then
                     --  AAPCS64 aggregate return: ≤8B in x0, 9–16B in
                     --  x0+x1, >16B written directly into the binding's
                     --  slot through x8 (sret, via Pending_Sret).
                     case Classify_Agg (Ty) is
                        when One_Reg =>
                           Lower_Expr_Into_Reg (F, S.L_Init, 0, ST);
                           IO.Put_Line (F, "    mov     x9, x0");
                           Store_Sized (Off, Sizeof (Ty));
                        when Two_Regs =>
                           Lower_Expr_Into_Reg (F, S.L_Init, 0, ST);
                           IO.Put_Line (F, "    str     x0, [x29, #"
                                           & Img (Off) & "]");
                           IO.Put_Line (F, "    str     x1, [x29, #"
                                           & Img (Off + 8) & "]");
                        when Indirect =>
                           ST.Pending_Sret := Integer (Off);
                           Lower_Expr_Into_Reg (F, S.L_Init, 0, ST);
                        when Not_Agg =>
                           raise Program_Error with
                             "codegen: aggregate let with scalar call";
                     end case;
                  elsif (S.L_Init.Kind = E_CAS
                         or else S.L_Init.Kind = E_Unary)
                    and then Sizeof (Ty) <= 8
                  then
                     --  ≤8-byte aggregates that Lower_Expr_Into_Reg packs
                     --  into a single register: §8.7 CAS verdicts and
                     --  §7.2.1 polarity-inverted contract values.
                     Lower_Expr_Into_Reg (F, S.L_Init, 9, ST);
                     Store_Sized (Off, Sizeof (Ty));
                  else
                     raise Program_Error with
                       "codegen: aggregate copy initialiser not yet supported";
                  end if;

               elsif S.L_Init /= null then
                  if Is_Float (Ty) then
                     --  Float initialiser: compute in d0/s0, store to slot.
                     Lower_Float_Into_D (F, S.L_Init, 0, ST);
                     IO.Put_Line
                       (F, "    str     "
                           & (if Sizeof (Ty) = 4 then "s0" else "d0")
                           & ", [x29, #" & Img (Off) & "]");
                  else
                     --  Scalar initialiser.
                     Lower_Expr_Into_Reg (F, S.L_Init, 9, ST);
                     Store_Sized (Off, Sizeof (Ty));
                  end if;
               end if;

               if not S.L_Tuple_Names.Is_Empty then
                  --  §4.7 destructuring: bind each name to its field slot.
                  for I in S.L_Tuple_Names.First_Index ..
                           S.L_Tuple_Names.Last_Index
                  loop
                     declare
                        Idx : constant Natural :=
                          I - S.L_Tuple_Names.First_Index;
                     begin
                        ST.Bindings.Append
                          ((Name   => S.L_Tuple_Names.Element (I),
                            Offset =>
                              Off + Kurt.Layout.Tuple_Field_Offset (Ty, Idx),
                            Ty     =>
                              Kurt.Layout.Tuple_Field_Type (Ty, Idx)));
                     end;
                  end loop;
               else
                  ST.Bindings.Append
                    ((Name => S.L_Name, Offset => Off, Ty => Ty));
                  --  §8.11 arm the runtime drop flag of an owned destruct
                  --  binding: 1 = live (destroy at scope exit). A later
                  --  transfer / destruct / undestruct clears it at runtime.
                  if Ty /= null and then Ty.Kind = T_Named
                    and then Type_Has_Drop (SU.To_String (Ty.Name))
                  then
                     declare
                        Flag : constant Natural := ST.Next_Offset;
                     begin
                        ST.Next_Offset := ST.Next_Offset + 8;
                        IO.Put_Line (F, "    mov     w9, #1");
                        IO.Put_Line (F, "    strb    w9, [x29, #"
                                        & Img (Flag) & "]");
                        ST.Drop_Flags.Append
                          ((Bind_Off => Off, Flag_Off => Flag));
                     end;
                  end if;
               end if;
            end;
         end;

      when S_Assign =>
         --  §6.1.8: `place = uninit;` stores nothing (the object keeps its
         --  current, uninitialized contents).
         if S.Asn_Rhs.Kind = E_Uninit then
            return;
         end if;
         --  §8.8.2: assigning a binding transfers it (skip its drop).
         Note_Move (F, ST, S.Asn_Rhs);
         --  Bootstrap lvalue forms: single-segment path, or `*expr`.
         if S.Asn_Lhs.Kind = E_Path
           and then Natural (S.Asn_Lhs.Segments.Length) = 1
         then
            declare
               Name : constant String :=
                 SU.To_String (S.Asn_Lhs.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  --  §5.4: store to a `static mut` binding.
                  declare
                     SI : constant Natural := Find_Static (Name);
                  begin
                     if SI = 0 then
                        raise Program_Error with
                          "codegen: assignment to unknown binding '"
                          & Name & "'";
                     end if;
                     declare
                        Sz  : constant Natural :=
                          Sizeof (Unit_Statics.Element (SI).Ty);
                        Lbl : constant String := "_Kst_" & Name;
                     begin
                        Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                        IO.Put_Line (F, "    adrp    x10, "
                                        & Lbl & "@PAGE");
                        IO.Put_Line (F, "    add     x10, x10, "
                                        & Lbl & "@PAGEOFF");
                        if Sz >= 8 then
                           IO.Put_Line (F, "    str     x9, [x10]");
                        elsif Sz = 4 then
                           IO.Put_Line (F, "    str     w9, [x10]");
                        elsif Sz = 2 then
                           IO.Put_Line (F, "    strh    w9, [x10]");
                        else
                           IO.Put_Line (F, "    strb    w9, [x10]");
                        end if;
                        return;
                     end;
                  end;
               end if;
               declare
                  B  : constant Binding := ST.Bindings.Element (Idx);
                  Sz : constant Natural := Sizeof (B.Ty);
               begin
                  Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                  if Is_Ref (B.Ty) or else Sz > 4 then
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (B.Offset) & "]");
                  else
                     IO.Put_Line (F, "    str     w9, [x29, #"
                                     & Img (B.Offset) & "]");
                  end if;
               end;
            end;
         elsif S.Asn_Lhs.Kind = E_Deref then
            declare
               Inner_Ty : constant Type_Access :=
                 Type_Of_Expr (S.Asn_Lhs.D_Inner, ST);
               Sz       : Natural := 8;
               Is_Atom  : Boolean := False;   --  &atomic / &guard target
               Acq      : Boolean := False;   --  &guard (fully ordered)
            begin
               if Is_Ref (Inner_Ty) then
                  Sz      := Sizeof (Inner_Ty.Target);
                  Is_Atom := Inner_Ty.R_Store in RS_Atomic | RS_Guard;
                  Acq     := Inner_Ty.R_Store = RS_Guard;
               end if;

               --  §8.5.2 atomic read-modify-write: the compound desugar
               --  `*p op= v` shares the place node between Asn_Lhs and
               --  Asn_Rhs.B_Lhs, which identifies the fetch-and-op form.
               --  Lower it as one exclusive load/store loop so the RMW is
               --  indivisible (a separate load + store would not be).
               if Is_Atom
                 and then S.Asn_Rhs.Kind = E_Binary
                 and then S.Asn_Rhs.B_Lhs = S.Asn_Lhs
                 and then S.Asn_Rhs.B_Op in
                   B_Add | B_Sub | B_And | B_Or | B_Xor
               then
                  declare
                     FN    : constant String  := SU.To_String (ST.Fn_Name);
                     Idx   : constant Natural := ST.If_Idx;
                     L_Top : constant String  :=
                       "Lrmw_" & FN & "_" & Img (Idx);
                     Lx : constant String :=
                       (if Sz = 1 then (if Acq then "ldaxrb" else "ldxrb")
                        elsif Sz = 2 then (if Acq then "ldaxrh" else "ldxrh")
                        else (if Acq then "ldaxr" else "ldxr"));
                     Sx : constant String :=
                       (if Sz = 1 then (if Acq then "stlxrb" else "stxrb")
                        elsif Sz = 2 then (if Acq then "stlxrh" else "stxrh")
                        else (if Acq then "stlxr" else "stxr"));
                     VR : constant String := (if Sz >= 8 then "x11" else "w11");
                     OR_R : constant String :=
                       (if Sz >= 8 then "x10" else "w10");
                     Mn : constant String :=
                       (case S.Asn_Rhs.B_Op is
                           when B_Add => "add ",
                           when B_Sub => "sub ",
                           when B_And => "and ",
                           when B_Or  => "orr ",
                           when others => "eor ");
                  begin
                     ST.If_Idx := ST.If_Idx + 1;
                     --  address -> x9 (spilled), operand -> x10.
                     Lower_Expr_Into_Reg (F, S.Asn_Lhs.D_Inner, 9, ST);
                     IO.Put_Line (F, "    sub     sp, sp, #16");
                     IO.Put_Line (F, "    str     x9, [sp]");
                     Lower_Expr_Into_Reg (F, S.Asn_Rhs.B_Rhs, 10, ST);
                     IO.Put_Line (F, "    ldr     x9, [sp]");
                     IO.Put_Line (F, "    add     sp, sp, #16");
                     IO.Put_Line (F, L_Top & ":");
                     IO.Put_Line (F, "    " & Lx & "   " & VR & ", [x9]");
                     IO.Put_Line (F, "    " & Mn & "    " & VR & ", "
                                     & VR & ", " & OR_R);
                     IO.Put_Line (F, "    " & Sx & "  w12, " & VR
                                     & ", [x9]");
                     IO.Put_Line (F, "    cbnz    w12, " & L_Top);
                  end;
               else
                  --  Compute the destination address, then spill it
                  --  across the value evaluation — the rhs may itself
                  --  recompute the same place (e.g. `*p = *p + 1`) and
                  --  clobber the address register.
                  Lower_Expr_Into_Reg (F, S.Asn_Lhs.D_Inner, 10, ST);
                  IO.Put_Line (F, "    sub     sp, sp, #16");
                  IO.Put_Line (F, "    str     x10, [sp]");
                  Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                  IO.Put_Line (F, "    ldr     x10, [sp]");
                  IO.Put_Line (F, "    add     sp, sp, #16");
                  if Acq then
                     --  §8.5: `guard` store is fully ordered
                     --  (store-release).
                     if Sz >= 8 then
                        IO.Put_Line (F, "    stlr    x9, [x10]");
                     elsif Sz = 4 then
                        IO.Put_Line (F, "    stlr    w9, [x10]");
                     elsif Sz = 2 then
                        IO.Put_Line (F, "    stlrh   w9, [x10]");
                     else
                        IO.Put_Line (F, "    stlrb   w9, [x10]");
                     end if;
                  elsif Sz >= 8 then
                     IO.Put_Line (F, "    str     x9, [x10]");
                  elsif Sz = 4 then
                     IO.Put_Line (F, "    str     w9, [x10]");
                  elsif Sz = 2 then
                     IO.Put_Line (F, "    strh    w9, [x10]");
                  else
                     IO.Put_Line (F, "    strb    w9, [x10]");
                  end if;
               end if;
            end;
         elsif S.Asn_Lhs.Kind = E_Field
           and then S.Asn_Lhs.F_Recv.Kind = E_Path
           and then Natural (S.Asn_Lhs.F_Recv.Segments.Length) = 1
         then
            --  Struct field store: place is [x29, slot_off + field_off].
            declare
               Name : constant String :=
                 SU.To_String (S.Asn_Lhs.F_Recv.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  raise Program_Error with
                    "codegen: assignment to unknown binding '" & Name & "'";
               end if;
               declare
                  B : constant Binding := ST.Bindings.Element (Idx);
                  --  §6.2.5: a reference binding stores through the
                  --  referent (`self.f = v`); a direct struct binding
                  --  stores into its own frame slot.
                  Via_Ref : constant Boolean :=
                    B.Ty /= null and then B.Ty.Kind = T_Ref;
                  SName : constant String :=
                    (if Via_Ref then SU.To_String (B.Ty.Target.Name)
                     else SU.To_String (B.Ty.Name));
                  FName : constant String  := SU.To_String (S.Asn_Lhs.F_Name);
                  FOff  : constant Natural :=
                    Kurt.Layout.Field_Offset (SName, FName);
                  FT    : constant Type_Access :=
                    Kurt.Layout.Field_Type (SName, FName);
                  Sz    : constant Natural := Sizeof (FT);
                  Loc   : constant String :=
                    (if Via_Ref then ", [x10, #" & Img (FOff) & "]"
                     else ", [x29, #" & Img (B.Offset + FOff) & "]");
               begin
                  Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                  if Via_Ref then
                     IO.Put_Line (F, "    ldr     x10, [x29, #"
                                     & Img (B.Offset) & "]");
                  end if;
                  if Is_Ref (FT) or else Sz >= 8 then
                     IO.Put_Line (F, "    str     x9" & Loc);
                  elsif Sz = 4 then
                     IO.Put_Line (F, "    str     w9" & Loc);
                  elsif Sz = 2 then
                     IO.Put_Line (F, "    strh    w9" & Loc);
                  else
                     IO.Put_Line (F, "    strb    w9" & Loc);
                  end if;
               end;
            end;
         else
            raise Program_Error with
              "codegen: unsupported lvalue form in assignment "
              & "(bootstrap accepts IDENT or *EXPR)";
         end if;

      when S_While =>
         declare
            FN    : constant String  := SU.To_String (ST.Fn_Name);
            Idx   : constant Natural := ST.Loop_Idx;
            L_Top : constant String  := "Lwhile_" & FN & "_top_" & Img (Idx);
            L_Thn : constant String  := "Lwhile_" & FN & "_thn_" & Img (Idx);
            L_End : constant String  := "Lwhile_" & FN & "_end_" & Img (Idx);
            Has_Then : constant Boolean := not S.W_Then.Is_Empty;
         begin
            ST.Loop_Idx := ST.Loop_Idx + 1;
            --  §7.5.3: `continue` targets the `then` block when present;
            --  `break` always exits the loop without running it.
            ST.Loops.Append
              ((Cont_Lbl  => SU.To_Unbounded_String
                               (if Has_Then then L_Thn else L_Top),
                Break_Lbl => SU.To_Unbounded_String (L_End),
                Name      => S.W_Label,
                Body_Entry => Natural (ST.Bindings.Length)));
            IO.Put_Line (F, L_Top & ":");
            Lower_Expr_Into_Reg (F, S.W_Cond, 10, ST);
            IO.Put_Line (F, "    cbz     w10, " & L_End);
            --  §8.4: each iteration's body locals are destroyed at the body's
            --  end (before the loop-back), so every pass cleans up its own.
            Lower_Scoped (S.W_Body);
            if Has_Then then
               IO.Put_Line (F, L_Thn & ":");
               Lower_Scoped (S.W_Then);
            end if;
            IO.Put_Line (F, "    b       " & L_Top);
            IO.Put_Line (F, L_End & ":");
            ST.Loops.Delete_Last;
         end;

      when S_If =>
         declare
            FN     : constant String  := SU.To_String (ST.Fn_Name);
            Idx    : constant Natural := ST.If_Idx;
            L_Else : constant String  := "Lselse_" & FN & "_" & Img (Idx);
            L_End  : constant String  := "Lsendif_" & FN & "_" & Img (Idx);
         begin
            ST.If_Idx := ST.If_Idx + 1;

            if S.SI_Is_Let then
               --  §7.3.3 `if let Enum::Variant { binds } = e`. The bootstrap
               --  requires e to be a binding (a place); compare its
               --  discriminant against the pattern variant and, on a match,
               --  alias the positional payload fields in the then-block.
               declare
                  CName : constant String :=
                    (if S.SI_Cond.Kind = E_Path
                        and then Natural (S.SI_Cond.Segments.Length) = 1
                     then SU.To_String (S.SI_Cond.Segments.Last_Element)
                     else "");
                  Bi : constant Natural :=
                    (if CName /= "" then Find_Binding (ST, CName) else 0);
               begin
                  if Bi = 0 then
                     raise Program_Error with
                       "codegen: `if let` scrutinee must be a binding";
                  end if;
                  declare
                     B    : constant Binding := ST.Bindings.Element (Bi);
                     EN   : constant String := SU.To_String (B.Ty.Name);
                     VN   : constant String :=
                       SU.To_String (S.SI_Let_Pat.Path.Last_Element);
                     DSz  : constant Natural := Kurt.Layout.Enum_Disc_Size (EN);
                     Loc  : constant String :=
                       ", [x29, #" & Img (B.Offset) & "]";
                     Saved : Natural;
                  begin
                     --  A void discriminant (single-variant enum) matches
                     --  unconditionally; otherwise compare in place.
                     if DSz > 0 then
                        if DSz >= 4 then
                           IO.Put_Line (F, "    ldr     w10" & Loc);
                        elsif DSz = 2 then
                           IO.Put_Line (F, "    ldrh    w10" & Loc);
                        else
                           IO.Put_Line (F, "    ldrb    w10" & Loc);
                        end if;
                        Lower_Imm (F, 11,
                          Kurt.Layout.Variant_Value (EN, VN), False);
                        IO.Put_Line (F, "    cmp     w10, w11");
                        IO.Put_Line (F, "    b.ne    " & L_Else);
                     end if;
                     --  then: bind payload fields as slot+offset aliases.
                     Saved := Natural (ST.Bindings.Length);
                     for K in 1 .. Natural (S.SI_Let_Pat.Bindings.Length) loop
                        ST.Bindings.Append
                          ((Name   => S.SI_Let_Pat.Bindings.Element (K),
                            Offset => B.Offset
                              + Kurt.Layout.Variant_Field_Offset (B.Ty, VN, K),
                            Ty     => Kurt.Layout.Variant_Field_Type
                                        (B.Ty, VN, K)));
                     end loop;
                     declare
                        --  §8.4 destroy the then-block's OWN destruct locals
                        --  at block end — but never the payload aliases, which
                        --  project into the scrutinee's storage (destroying
                        --  them would double-free with the scrutinee).
                        After_Payload : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        for I in S.SI_Then.First_Index .. S.SI_Then.Last_Index
                        loop
                           Lower_Stmt (F, S.SI_Then.Element (I), ST);
                        end loop;
                        Emit_Binding_Drops
                          (F, ST, Keep => After_Payload,
                           Preserve_Ret => False);
                     end;
                     while Natural (ST.Bindings.Length) > Saved loop
                        ST.Bindings.Delete_Last;
                     end loop;
                     IO.Put_Line (F, "    b       " & L_End);
                     IO.Put_Line (F, L_Else & ":");
                     Lower_Scoped (S.SI_Else);
                     IO.Put_Line (F, L_End & ":");
                  end;
               end;

            elsif S.SI_Is_Contract then
               --  Contract-binding `if e -> v | err`. The scrutinee is a
               --  contract-enum binding; branch on its discriminant and
               --  alias each side's payload to the bound name.
               declare
                  CName : constant String :=
                    SU.To_String (S.SI_Cond.Segments.Last_Element);
                  Bi    : constant Natural := Find_Binding (ST, CName);
               begin
                  if Bi = 0 or else S.SI_Cond.Kind /= E_Path then
                     raise Program_Error with
                       "codegen: `->` cond must be a contract-enum binding";
                  end if;
                  declare
                     B      : constant Binding := ST.Bindings.Element (Bi);
                     EN     : constant String := SU.To_String (B.Ty.Name);
                     Succ_V : constant String :=
                       Kurt.Layout.Contract_Success_Variant (EN);
                     Fail_V : constant String :=
                       Kurt.Layout.Contract_Fail_Variant (EN);
                     DSz    : constant Natural :=
                       Kurt.Layout.Enum_Disc_Size (EN);
                     Loc    : constant String :=
                       ", [x29, #" & Img (B.Offset) & "]";
                     Saved  : Natural;
                  begin
                     --  Load discriminant into w10.
                     if DSz >= 4 then
                        IO.Put_Line (F, "    ldr     w10" & Loc);
                     elsif DSz = 2 then
                        IO.Put_Line (F, "    ldrh    w10" & Loc);
                     else
                        IO.Put_Line (F, "    ldrb    w10" & Loc);
                     end if;
                     Lower_Imm (F, 11,
                       Kurt.Layout.Variant_Value (EN, Succ_V), False);
                     IO.Put_Line (F, "    cmp     w10, w11");
                     IO.Put_Line (F, "    b.ne    " & L_Else);

                     --  then: bind the success payload (slot+offset alias).
                     Saved := Natural (ST.Bindings.Length);
                     ST.Bindings.Append
                       ((Name   => S.SI_Succ_Bind,
                         Offset => B.Offset
                           + Kurt.Layout.Variant_Field_Offset
                               (B.Ty, Succ_V, 1),
                         Ty     => Kurt.Layout.Variant_Field_Type
                                     (B.Ty, Succ_V, 1)));
                     declare
                        --  §8.4 drop only the block's own locals at block end;
                        --  the payload alias projects into the scrutinee.
                        After_Payload : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        for I in S.SI_Then.First_Index .. S.SI_Then.Last_Index
                        loop
                           Lower_Stmt (F, S.SI_Then.Element (I), ST);
                        end loop;
                        Emit_Binding_Drops
                          (F, ST, Keep => After_Payload,
                           Preserve_Ret => False);
                     end;
                     while Natural (ST.Bindings.Length) > Saved loop
                        ST.Bindings.Delete_Last;
                     end loop;
                     IO.Put_Line (F, "    b       " & L_End);

                     --  else: bind the failure payload if requested.
                     IO.Put_Line (F, L_Else & ":");
                     Saved := Natural (ST.Bindings.Length);
                     if SU.Length (S.SI_Fail_Bind) > 0 then
                        ST.Bindings.Append
                          ((Name   => S.SI_Fail_Bind,
                            Offset => B.Offset
                              + Kurt.Layout.Variant_Field_Offset
                                  (B.Ty, Fail_V, 1),
                            Ty     => Kurt.Layout.Variant_Field_Type
                                        (B.Ty, Fail_V, 1)));
                     end if;
                     declare
                        After_Payload : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        for I in S.SI_Else.First_Index .. S.SI_Else.Last_Index
                        loop
                           Lower_Stmt (F, S.SI_Else.Element (I), ST);
                        end loop;
                        Emit_Binding_Drops
                          (F, ST, Keep => After_Payload,
                           Preserve_Ret => False);
                     end;
                     while Natural (ST.Bindings.Length) > Saved loop
                        ST.Bindings.Delete_Last;
                     end loop;
                     IO.Put_Line (F, L_End & ":");
                  end;
               end;
            else
               Lower_Expr_Into_Reg (F, S.SI_Cond, 10, ST);
               IO.Put_Line (F, "    cbz     w10, " & L_Else);
               Lower_Scoped (S.SI_Then);
               IO.Put_Line (F, "    b       " & L_End);
               IO.Put_Line (F, L_Else & ":");
               Lower_Scoped (S.SI_Else);
               IO.Put_Line (F, L_End & ":");
            end if;
         end;

      when S_Extract =>
         --  §7: `let v <- e else err { … }`. Branch on e's discriminant;
         --  on failure bind err and run the (diverging) else block, on
         --  success bind v as a slot+offset alias for the rest of scope.
         declare
            FN     : constant String  := SU.To_String (ST.Fn_Name);
            Idx    : constant Natural := ST.If_Idx;
            L_Succ : constant String := "Lextr_" & FN & "_ok_" & Img (Idx);
            CName  : constant String :=
              (if S.X_Expr.Kind = E_Path
                  and then Natural (S.X_Expr.Segments.Length) = 1
               then SU.To_String (S.X_Expr.Segments.Last_Element) else "");
            Bi     : constant Natural :=
              (if CName /= "" then Find_Binding (ST, CName) else 0);
         begin
            ST.If_Idx := ST.If_Idx + 1;
            if Bi = 0 then
               raise Program_Error with
                 "codegen: `<-` source must be a contract-enum binding";
            end if;
            declare
               B      : constant Binding := ST.Bindings.Element (Bi);
               EN     : constant String := SU.To_String (B.Ty.Name);
               Succ_V : constant String :=
                 Kurt.Layout.Contract_Success_Variant (EN);
               Fail_V : constant String :=
                 Kurt.Layout.Contract_Fail_Variant (EN);
               DSz    : constant Natural := Kurt.Layout.Enum_Disc_Size (EN);
               Loc    : constant String :=
                 ", [x29, #" & Img (B.Offset) & "]";
               Saved  : Natural;
            begin
               if DSz >= 4 then
                  IO.Put_Line (F, "    ldr     w10" & Loc);
               elsif DSz = 2 then
                  IO.Put_Line (F, "    ldrh    w10" & Loc);
               else
                  IO.Put_Line (F, "    ldrb    w10" & Loc);
               end if;
               Lower_Imm (F, 11,
                 Kurt.Layout.Variant_Value (EN, Succ_V), False);
               IO.Put_Line (F, "    cmp     w10, w11");
               IO.Put_Line (F, "    b.eq    " & L_Succ);

               --  Failure path: bind err, run the diverging else block.
               Saved := Natural (ST.Bindings.Length);
               if SU.Length (S.X_Err) > 0 then
                  ST.Bindings.Append
                    ((Name   => S.X_Err,
                      Offset => B.Offset
                        + Kurt.Layout.Variant_Field_Offset (B.Ty, Fail_V, 1),
                      Ty     => Kurt.Layout.Variant_Field_Type
                                  (B.Ty, Fail_V, 1)));
               end if;
               for I in S.X_Else.First_Index .. S.X_Else.Last_Index loop
                  Lower_Stmt (F, S.X_Else.Element (I), ST);
               end loop;
               while Natural (ST.Bindings.Length) > Saved loop
                  ST.Bindings.Delete_Last;
               end loop;

               --  Success: bind v permanently for the rest of the block.
               IO.Put_Line (F, L_Succ & ":");
               ST.Bindings.Append
                 ((Name   => S.X_Bind,
                   Offset => B.Offset
                     + Kurt.Layout.Variant_Field_Offset (B.Ty, Succ_V, 1),
                   Ty     => Kurt.Layout.Variant_Field_Type (B.Ty, Succ_V, 1)));
            end;
         end;

      when S_Break =>
         if ST.Loops.Is_Empty then
            raise Program_Error with "codegen: 'break' outside a loop";
         end if;
         if S.Brk_Val /= null then
            --  §7.7 value form: evaluate for effect. Loop values are not
            --  yet propagated in the bootstrap; the value is discarded.
            Lower_Expr_Into_Reg (F, S.Brk_Val, 9, ST);
         end if;
         --  §8.4 destroy every body local live at this jump, across all
         --  scopes down to the targeted loop's body (it leaves the loop).
         Emit_Binding_Drops
           (F, ST, Keep => Target_Loop (ST, S.Brk_Label).Body_Entry,
            Preserve_Ret => False);
         IO.Put_Line (F, "    b       "
                         & SU.To_String
                             (Target_Loop (ST, S.Brk_Label).Break_Lbl));

      when S_Continue =>
         if ST.Loops.Is_Empty then
            raise Program_Error with "codegen: 'continue' outside a loop";
         end if;
         --  §8.4 destroy the body locals live at this jump before re-testing
         --  the condition (the current iteration's scope ends here).
         Emit_Binding_Drops
           (F, ST, Keep => Target_Loop (ST, S.Cont_Label).Body_Entry,
            Preserve_Ret => False);
         IO.Put_Line (F, "    b       "
                         & SU.To_String
                             (Target_Loop (ST, S.Cont_Label).Cont_Lbl));

      when S_Express =>
         --  §7.8 block exit-with-value. Full block-expression support is
         --  deferred; for now evaluate the value for effect (works as a
         --  no-op in the trailing-position case).
         Lower_Expr_Into_Reg (F, S.Xp_Val, 9, ST);

      when S_Fence =>
         --  §8.5.3 ordering fences. The bootstrap emits in program order
         --  and performs no reordering, so a @volatile (translation) fence
         --  needs no instruction. @guard additionally constrains the
         --  execution environment: emit a full barrier for every form
         --  (`dmb ish` is stronger than the directional forms require,
         --  which is conforming).
         if S.Fn_Guard then
            IO.Put_Line (F, "    dmb     ish"
              & (case S.Fn_Form is
                    when FF_Full  => "     // @guard",
                    when FF_Start => "     // @guard.start",
                    when FF_End   => "     // @guard.end"));
         else
            IO.Put_Line (F, "    // @volatile"
              & (case S.Fn_Form is
                    when FF_Full  => "",
                    when FF_Start => ".start",
                    when FF_End   => ".end")
              & " translation fence (no instruction)");
         end if;

      when S_Trap =>
         --  §7.10: `@trap;` diverges. With a handler declared, branch into
         --  it; `@trap` is reentrant, so the handler may itself `@trap;`
         --  (another `bl` re-invokes it). The handler shall diverge, but
         --  should it fall through, the default divergence below still
         --  terminates. Default divergence is the implementation-defined
         --  behaviour: an undefined-instruction trap. It is self-contained
         --  (no external symbol or stack discipline), cannot return, and
         --  does not unwind — matching §7.10's "terminates without
         --  unwinding".
         if Unit_Has_Trap_Handler then
            IO.Put_Line (F, "    bl      _kurt_trap_handler");
         end if;
         IO.Put_Line (F, "    udf     #0         // @trap default divergence");
   end case;
end Lower_Stmt;
