separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_Let is
   begin
         if S.L_Is_Refut then
            --  §5.2.1 refutable let-else. Like `if let` the scrutinee is a
            --  binding; compare its discriminant against the pattern variant.
            --  On a match, jump past the (diverging) else and register the
            --  payload aliases so they PERSIST for the rest of the enclosing
            --  scope; on a mismatch, fall into the else block.
            declare
               FN    : constant String  := SU.To_String (ST.Fn_Name);
               Idx   : constant Natural := ST.If_Idx;
               L_Ok  : constant String  := "Lletok_" & FN & "_" & Img (Idx);
               CName : constant String :=
                 (if S.L_Init.Kind = E_Path
                     and then Natural (S.L_Init.Segments.Length) = 1
                  then SU.To_String (S.L_Init.Segments.Last_Element) else "");
               Bi : constant Natural :=
                 (if CName /= "" then Find_Binding (ST, CName) else 0);
            begin
               ST.If_Idx := ST.If_Idx + 1;
               if Bi = 0 then
                  raise Program_Error with
                    "codegen: refutable `let` scrutinee must be a binding";
               end if;
               declare
                  B    : constant Binding := ST.Bindings.Element (Bi);
                  EN   : constant String := SU.To_String (B.Ty.Name);
                  VN   : constant String :=
                    SU.To_String (S.L_Refut_Pat.Path.Last_Element);
                  DSz  : constant Natural := Kurt.Layout.Enum_Disc_Size (EN);
                  Loc  : constant String :=
                    ", [x29, #" & Img (B.Offset) & "]";
               begin
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
                     IO.Put_Line (F, "    b.eq    " & L_Ok);
                     --  mismatch: the else block runs and diverges.
                     Lower_Scoped (S.L_Else);
                  end if;
                  IO.Put_Line (F, L_Ok & ":");
                  --  Register payload aliases; they persist (no pop) so the
                  --  rest of the enclosing block can use them.
                  for K in 1 .. Natural (S.L_Refut_Pat.Bindings.Length) loop
                     ST.Bindings.Append
                       ((Name   => S.L_Refut_Pat.Bindings.Element (K),
                         Offset => B.Offset
                           + Pat_Field_Off (S.L_Refut_Pat, B.Ty, VN, K),
                         Ty     => Pat_Field_Ty
                                        (S.L_Refut_Pat, B.Ty, VN, K)));
                  end loop;
               end;
            end;
            return;
         end if;
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
               --  §2.2.3 automatic objects are laid out contiguously in
               --  declaration order, each at its natural alignment — not
               --  rounded to a uniform 8-byte slot. This keeps a `&raw`
               --  cursor's arithmetic across adjacent locals well-defined
               --  while preserving natural alignment for aarch64 loads/stores.
               Slot : constant Natural :=
                 (if Is_Fat then 16 else Natural'Max (Sizeof (Ty), 1));
               Aln  : constant Natural :=
                 (if Is_Fat then 8
                  else Natural'Max (Kurt.Layout.Align_Of (Ty), 1));
               Off  : constant Natural :=
                 ((ST.Next_Offset + Aln - 1) / Aln) * Aln;
            begin
               ST.Next_Offset := Off + Slot;

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
                              FI  : constant Field_Init :=
                                S.L_Init.SL_Fields.Element (I);
                              FN  : constant String := SU.To_String (FI.Name);
                              FT  : constant Type_Access :=
                                Kurt.Layout.Field_Type (SN, FN);
                              FOf : constant Natural :=
                                Off + Kurt.Layout.Field_Offset (SN, FN);
                              BI  : constant Natural :=
                                (if FI.Val.Kind = E_Path
                                   and then Natural (FI.Val.Segments.Length) = 1
                                 then Find_Binding
                                        (ST, SU.To_String
                                           (FI.Val.Segments.Last_Element))
                                 else 0);
                           begin
                              if Is_Aggregate_Type (FT) and then BI /= 0 then
                                 --  §8.8.1 an aggregate field (struct / array /
                                 --  tuple) copied from a binding cannot travel
                                 --  in a register: copy its full width.
                                 Emit_Mem_Copy
                                   (F, "x29", ST.Bindings.Element (BI).Offset,
                                    "x29", FOf, Sizeof (FT));
                              else
                                 Lower_Expr_Into_Reg (F, FI.Val, 9, ST);
                                 Store_Sized (FOf, Sizeof (FT));
                              end if;
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
                  elsif S.L_Init.Kind = E_Closure then
                     --  §9.9.3 capturing closure: the binding holds the
                     --  anonymous env struct. Materialise it by copying each
                     --  captured binding's current value into its field
                     --  (capture by copy), exactly like a struct literal.
                     Zero_Fill (Off, Sizeof (Ty));
                     declare
                        SN : constant String := SU.To_String (Ty.Name);
                     begin
                        for C of S.L_Init.Clo_Caps loop
                           declare
                              CN  : constant String := SU.To_String (C.Name);
                              FT  : constant Type_Access :=
                                Kurt.Layout.Field_Type (SN, CN);
                              FOf : constant Natural :=
                                Off + Kurt.Layout.Field_Offset (SN, CN);
                              P   : constant Expr_Access :=
                                new Expr_Node (Kind => E_Path);
                              BI  : constant Natural := Find_Binding (ST, CN);
                           begin
                              P.Segments.Append (C.Name);
                              if Is_Aggregate_Type (FT) and then BI /= 0 then
                                 --  An aggregate capture is copied by memory
                                 --  from its frame slot (it cannot live in a
                                 --  register).
                                 Emit_Mem_Copy
                                   (F, "x29", ST.Bindings.Element (BI).Offset,
                                    "x29", FOf, Sizeof (FT));
                              else
                                 Lower_Expr_Into_Reg (F, P, 9, ST);
                                 Store_Sized (FOf, Sizeof (FT));
                              end if;
                              --  §9.9.3 a `with destruct` capture is *moved*
                              --  into the env: clear the source binding's
                              --  drop flag so it is destroyed once — by the
                              --  env's destructor at scope exit, not here.
                              --  (A copyable capture is duplicated, not moved.)
                              if Kurt.Layout.Satisfies_Destruct (FT) then
                                 P.P_Is_Move := True;
                                 Note_Move (F, ST, P);
                              end if;
                           end;
                        end loop;
                     end;
                  elsif S.L_Init.Kind = E_Field
                    and then S.L_Init.F_Recv.Kind = E_Path
                    and then Natural (S.L_Init.F_Recv.Segments.Length) = 1
                  then
                     --  Aggregate copy from a struct field — including a field
                     --  reached through a reference, e.g. a capturing closure's
                     --  `let cap = self.cap;` (self is `&env`). Copy Sizeof(Ty)
                     --  bytes from the field's address into the binding's slot.
                     declare
                        RN : constant String := SU.To_String
                          (S.L_Init.F_Recv.Segments.Last_Element);
                        FN : constant String := SU.To_String (S.L_Init.F_Name);
                        RI : constant Natural := Find_Binding (ST, RN);
                     begin
                        if RI = 0 then
                           raise Program_Error with
                             "codegen: unknown binding '" & RN & "'";
                        end if;
                        declare
                           RB : constant Binding := ST.Bindings.Element (RI);
                        begin
                           if RB.Ty /= null and then RB.Ty.Kind = T_Ref
                             and then RB.Ty.Target /= null
                             and then RB.Ty.Target.Kind = T_Named
                           then
                              declare
                                 SN  : constant String :=
                                   SU.To_String (RB.Ty.Target.Name);
                              begin
                                 IO.Put_Line (F, "    ldr     x10, [x29, #"
                                                 & Img (RB.Offset) & "]");
                                 Emit_Mem_Copy
                                   (F, "x10",
                                    Kurt.Layout.Field_Offset (SN, FN),
                                    "x29", Off, Sizeof (Ty));
                              end;
                           else
                              declare
                                 SN : constant String :=
                                   SU.To_String (RB.Ty.Name);
                              begin
                                 Emit_Mem_Copy
                                   (F, "x29",
                                    RB.Offset
                                      + Kurt.Layout.Field_Offset (SN, FN),
                                    "x29", Off, Sizeof (Ty));
                              end;
                           end if;
                        end;
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
                             (if VN = "#wild#"
                              then Kurt.Layout.Implicit_Wild_Value (EN)
                              else Kurt.Layout.Variant_Value (EN, VN)),
                             False);
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
                              --  §8.8.2 a destruct-typed element supplied by a
                              --  binding is transferred: clear the source's
                              --  drop flag so it is not also destroyed.
                              Note_Move (F, ST, S.L_Init.AL_Elems.Element (I));
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
                  elsif S.L_Init.Kind = E_Deref then
                     --  §8.8.1 aggregate copy from a dereferenced pointer
                     --  (`let a: T = *p;`): materialise the source address in
                     --  a scratch register and copy T's bytes into the slot.
                     Lower_Expr_Into_Reg (F, S.L_Init.D_Inner, 10, ST);
                     Emit_Mem_Copy (F, "x10", 0, "x29", Off, Sizeof (Ty));
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
                  --  Covers a named destruct type and an array whose element
                  --  type has a destructor.
                  if Ty /= null
                    and then ((Ty.Kind = T_Named
                                 and then Type_Has_Drop
                                            (SU.To_String (Ty.Name)))
                              or else (Ty.Kind = T_Array
                                       and then Ty.Elem /= null
                                       and then Ty.Elem.Kind = T_Named
                                       and then Type_Has_Drop
                                                  (SU.To_String
                                                     (Ty.Elem.Name))))
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

   end Lower_Let;
