--  Expression lowering (subunit of Kurt.Codegen).
--  Computes the value of E into x<Target_Reg>. Sees all of the parent
--  body's declarations (helpers, Lower_State, Lower_Imm, Lower_Stmt ...).

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
     (Src_Sz : Cell_Count; Src_Signed : Boolean; Tgt_Sz : Cell_Count)
   is separate;

   ------------------------------------------------------------------
   --  Call lowering. Arguments are evaluated to stack scratch slots in
   --  source order (§2.7.1), then fixed args are loaded into x0..x7.
   --  Variadic args (Apple aarch64 ABI) sit at the bottom of the frame.
   ------------------------------------------------------------------
   procedure Lower_Call (E : Expr_Access) is separate;

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
   procedure Lower_Sat (Op : Binary_Op; Ty : Type_Access) is separate;

   ------------------------------------------------------------------
   --  §9.5 dynamic dispatch: `recv.method(args)` where recv is a
   --  `&dyn Trait` binding. The fat reference holds the value pointer
   --  (slot+0) and the dispatch-table pointer (slot+8). The method's
   --  subroutine pointer is loaded from dtable field `3 + k` and invoked
   --  indirectly; the value pointer is passed as the erased self.
   --  Bootstrap: extra arguments are scalar/reference (≤8 bytes).
   ------------------------------------------------------------------
   procedure Lower_Dyn_Call (E : Expr_Access) is separate;

   ------------------------------------------------------------------
   procedure Lower_Binary (E : Expr_Access) is separate;

   ------------------------------------------------------------------
   --  If-expression lowering (cbz on the materialised condition).
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   --  Match lowering: evaluate the scrutinee once onto the stack, then
   --  test each arm in order with cmp/b.ne; the matched arm's body lands
   --  in x<target>. A #wild# arm always matches.
   ------------------------------------------------------------------
   --  Load a value of Sz cells from [x29, #Off] into w9 (zero-extended).
   procedure Load_From_Frame (Off, Sz : Cell_Count) is
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

   procedure Lower_Match (E : Expr_Access) is separate;

   procedure Lower_If (E : Expr_Access) is separate;

   ------------------------------------------------------------------
   --  §7.2.3 `contract e else fallback` lowering: materialise e's
   --  (possibly polarity-inverted) value in a fresh stack temp, branch on
   --  its discriminant, and land the success payload or the fallback's
   --  value in Target_Reg.
   ------------------------------------------------------------------
   procedure Lower_Extract (E : Expr_Access) is separate;

   procedure Lower_Cast is separate;
   procedure Lower_CAS is separate;
   procedure Lower_Path is separate;
   procedure Lower_Field is separate;
begin
   case E.Kind is
      when E_Uninit =>
         --  §6.1.8: an uninitialized value. Valid `uninit` positions
         --  (let/mut/assign) are intercepted earlier and store nothing;
         --  if one reaches here the target register simply keeps its
         --  current (indeterminate) contents — no instruction is emitted.
         null;

      when E_Closure =>
         --  §9.9 a non-capturing closure is its lifted subroutine's address
         --  (a subroutine pointer) — the same value a bare `fn` name yields.
         declare
            Lbl : constant String :=
              "_" & SU.To_String (E.Clo_Fn_Name);
         begin
            IO.Put_Line (F, "    adrp    " & Xreg & ", " & Lbl & "@PAGE");
            IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                            & ", " & Lbl & "@PAGEOFF");
         end;

      when E_Airside_Blk =>
         --  §6.9/§7.8 block expression (airside or plain): run the body as
         --  a lexical scope (mirrors Lower_Scoped); its value is yielded by
         --  `express` — anywhere in the block, not only in trailing
         --  position. The block gets a frame result slot and an end label;
         --  every `express` targeting it (see S_Express in Lower_Stmt)
         --  stores to the slot, runs the intervening destructors, and
         --  branches to the end label. Falling off the end means no
         --  `express` executed — the block is `void` on that path and the
         --  slot's (indeterminate) value is never used.
         declare
            Entry_Len : constant Natural := Natural (ST.Bindings.Length);
            FN        : constant String  := SU.To_String (ST.Fn_Name);
            Idx       : constant Natural := ST.If_Idx;
            L_End     : constant String  := "Lblk_" & FN & "_" & Img (Idx);
            Res_Off   : constant Cell_Count := ST.Next_Offset;
         begin
            ST.If_Idx := ST.If_Idx + 1;
            ST.Next_Offset := ST.Next_Offset + 8;   --  result slot
            ST.Expr_Blocks.Append
              ((End_Lbl    => SU.To_Unbounded_String (L_End),
                Result_Off => Res_Off,
                Body_Entry => Entry_Len,
                Name       => E.AB_Label));   --  §7.9 label; empty = none
            for I in E.AB_Stmts.First_Index .. E.AB_Stmts.Last_Index loop
               Lower_Stmt (F, E.AB_Stmts.Element (I), ST);
            end loop;
            ST.Expr_Blocks.Delete_Last;
            --  Fall-through path (no `express` executed): scope exit.
            Emit_Binding_Drops
              (F, ST, Keep => Entry_Len, Preserve_Ret => False);
            while Natural (ST.Bindings.Length) > Entry_Len loop
               ST.Bindings.Delete_Last;
            end loop;
            IO.Put_Line (F, L_End & ":");
            IO.Put_Line (F, "    ldr     " & Xreg
                            & ", [x29, #" & Img (Res_Off) & "]");
         end;

      when E_Loop =>
         --  §7.7 `loop { … }` as an expression: an unconditional loop whose
         --  value is written by every `break expr` targeting it into a frame
         --  result slot, loaded into the target register once the loop exits.
         declare
            FN      : constant String  := SU.To_String (ST.Fn_Name);
            Idx     : constant Natural := ST.Loop_Idx;
            L_Top   : constant String  := "Lloop_" & FN & "_top_" & Img (Idx);
            L_End   : constant String  := "Lloop_" & FN & "_end_" & Img (Idx);
            Res_Off : constant Cell_Count := ST.Next_Offset;
            Entry_Len : constant Natural := Natural (ST.Bindings.Length);
         begin
            ST.Loop_Idx := ST.Loop_Idx + 1;
            ST.Next_Offset := ST.Next_Offset + 8;   --  result slot
            ST.Loops.Append
              ((Cont_Lbl   => SU.To_Unbounded_String (L_Top),
                Break_Lbl  => SU.To_Unbounded_String (L_End),
                Name       => SU.Null_Unbounded_String,
                Body_Entry => Entry_Len,
                Result_Off => Res_Off));
            IO.Put_Line (F, L_Top & ":");
            for I in E.Loop_Body.First_Index .. E.Loop_Body.Last_Index loop
               Lower_Stmt (F, E.Loop_Body.Element (I), ST);
            end loop;
            --  §8.4 drop this iteration's body locals before looping back.
            Emit_Binding_Drops
              (F, ST, Keep => Entry_Len, Preserve_Ret => False);
            while Natural (ST.Bindings.Length) > Entry_Len loop
               ST.Bindings.Delete_Last;
            end loop;
            IO.Put_Line (F, "    b       " & L_Top);
            IO.Put_Line (F, L_End & ":");
            ST.Loops.Delete_Last;
            IO.Put_Line (F, "    ldr     " & Xreg
                            & ", [x29, #" & Img (Res_Off) & "]");
         end;

      when E_Destruct =>
         --  §8.4/§8.11: `destruct(g)` runs g's destructor immediately;
         --  `undestruct(g)` reclaims g's storage without running it. Either
         --  way g is consumed, so its scope-exit drop is suppressed
         --  (Note_Move records the offset; sema set P_Is_Move on the inner).
         declare
            Inner : constant Expr_Access := E.DT_Inner;
            Idx   : constant Natural :=
              (if Inner /= null and then Inner.Kind = E_Path
                 and then Natural (Inner.Segments.Length) = 1
               then Find_Binding
                      (ST, SU.To_String (Inner.Segments.Last_Element))
               else 0);
         begin
            if Idx /= 0 and then not E.DT_Undo then
               declare
                  B : constant Binding := ST.Bindings.Element (Idx);
               begin
                  if B.Ty /= null and then B.Ty.Kind = T_Named
                    and then Type_Has_Drop (SU.To_String (B.Ty.Name))
                  then
                     IO.Put_Line (F, "    add     x0, x29, #"
                                     & Img (B.Offset));
                     IO.Put_Line (F, "    bl      _"
                                     & SU.To_String (B.Ty.Name) & "$drop");
                  end if;
               end;
            end if;
            Note_Move (F, ST, Inner);
         end;

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
         Lower_Field;
      when E_Struct_Lit | E_Variant_New | E_Tuple_Lit | E_Array_Lit =>
         if E.Kind = E_Variant_New
           and then SU.To_String (E.VN_Variant) = "#wild#"
         then
            --  §6.1.5 `Enum::#wild#` is a scalar discriminant value (like a
            --  unit variant); load the implicit-wild discriminant.
            declare
               EN : constant String :=
                 (if E.Sem_Ty /= null then SU.To_String (E.Sem_Ty.Name)
                  else SU.To_String (E.VN_Enum));
            begin
               Lower_Imm (F, Target_Reg,
                 Kurt.Layout.Implicit_Wild_Value (EN),
                 Sizeof (E.Sem_Ty) > 4);
            end;
         elsif E.Kind = E_Variant_New
           and then not Kurt.Layout.Enum_Has_Payload
                          (if E.Sem_Ty /= null then SU.To_String (E.Sem_Ty.Name)
                           else SU.To_String (E.VN_Enum))
         then
            --  A unit (payload-free) variant is a bare discriminant value,
            --  same as the `#wild#` case above -- no temporary needed.
            declare
               EN : constant String :=
                 (if E.Sem_Ty /= null then SU.To_String (E.Sem_Ty.Name)
                  else SU.To_String (E.VN_Enum));
               VN : constant String := SU.To_String (E.VN_Variant);
            begin
               if Kurt.Layout.Enum_Disc_Size (EN) > 0 then
                  Lower_Imm (F, Target_Reg,
                    Kurt.Layout.Variant_Value (EN, VN),
                    Sizeof (E.Sem_Ty) > 4);
               end if;
            end;
         else
            declare
               Lit_Ty : constant Type_Access := Type_Of_Expr (E, ST);
            begin
               if Classify_Agg (Lit_Ty) = One_Reg then
                  --  §2.1.4: materialise into a hidden stack temporary and
                  --  load its value — the shape a composite literal takes
                  --  in a "value in a register" position (call argument,
                  --  `return`, match scrutinee). Every one of those
                  --  positions transfers the value onward per §8.8.2, so
                  --  no drop is owed on the temporary; this is not a
                  --  general temporary-drop mechanism.
                  declare
                     Off : constant Cell_Count :=
                       Materialize_Composite (F, ST, Lit_Ty, E);
                     Sz  : constant Cell_Count := Sizeof (Lit_Ty);
                  begin
                     if Sz > 4 then
                        IO.Put_Line (F, "    ldr     " & Xreg & ", [x29, #"
                                        & Img (Off) & "]");
                     elsif Sz = 2 then
                        IO.Put_Line (F, "    ldrh    " & Wreg & ", [x29, #"
                                        & Img (Off) & "]");
                     elsif Sz = 1 then
                        IO.Put_Line (F, "    ldrb    " & Wreg & ", [x29, #"
                                        & Img (Off) & "]");
                     else
                        IO.Put_Line (F, "    ldr     " & Wreg & ", [x29, #"
                                        & Img (Off) & "]");
                     end if;
                  end;
               else
                  raise Codegen_Error with
                    "not yet supported: a struct/variant/tuple/array "
                    & "literal wider than 8 bytes outside a let/mut "
                    & "initialiser (bootstrap)";
               end if;
            end;
         end if;


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
         --  §9.9 a capturing-closure call: invoke the lifted subroutine
         --  `$clo_N` directly, passing the address of the closure binding
         --  (its env struct) as the hidden first `self` argument. Reuse the
         --  normal call machinery by synthesising that prepended argument.
         if SU.Length (E.C_Clo_Lift) > 0 then
            declare
               E2  : constant Expr_Access := new Expr_Node (Kind => E_Call);
               LP  : constant Expr_Access := new Expr_Node (Kind => E_Path);
               Env : constant Expr_Access := new Expr_Node (Kind => E_Ref);
               ETy : constant Type_Access := new AST_Type (Kind => T_Ref);
            begin
               LP.Segments.Append (E.C_Clo_Lift);
               ETy.Sigil  := R_Raw;
               ETy.Target := Type_Of_Expr (E.C_Callee, ST);
               Env.Rf_Sigil := R_Raw;
               Env.Rf_Place := E.C_Callee;
               Env.Sem_Ty   := ETy;
               E2.C_Callee := LP;
               E2.C_Args.Append (Env);
               for K in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  E2.C_Args.Append (E.C_Args.Element (K));
               end loop;
               Lower_Call (E2);
               if Target_Reg /= 0 then
                  IO.Put_Line (F, "    mov     " & Xreg & ", x0");
               end if;
               return;
            end;
         end if;
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
         Lower_Path;
      when E_If =>
         Lower_If (E);

      when E_Extract =>
         Lower_Extract (E);

      when E_Match =>
         Lower_Match (E);

      when E_Binary =>
         Lower_Binary (E);

      when E_Deref =>
         Lower_Expr_Into_Reg (F, E.D_Inner, Target_Reg, ST);
         declare
            Inner_Ty : constant Type_Access := Type_Of_Expr (E.D_Inner, ST);
            Sz       : Cell_Count := 8;
            Guarded  : Boolean := False;
         begin
            if Is_Ref (Inner_Ty) then
               Sz := Sizeof (Inner_Ty.Target);
               --  §8.5: a `guard` load is fully ordered (load-acquire).
               --  An `atomic` load needs no extra instruction — aligned
               --  loads up to 8 bytes are single-copy atomic on aarch64.
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
                  Off   : Cell_Count;
               begin
                  if B.Ty /= null and then B.Ty.Kind = T_Ref
                    and then B.Ty.Target /= null
                    and then B.Ty.Target.Kind = T_Named
                  then
                     --  §6.2.5 field through a reference (e.g. a closure's
                     --  `&self.cap`): the field address is the loaded
                     --  reference plus the field offset.
                     IO.Put_Line (F, "    ldr     " & Xreg & ", [x29, #"
                                     & Img (B.Offset) & "]");
                     IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                                     & ", #" & Img (Kurt.Layout.Field_Offset
                                       (SU.To_String (B.Ty.Target.Name),
                                        FName)));
                  else
                     if B.Ty /= null and then B.Ty.Kind = T_Tuple then
                        Off := B.Offset + Kurt.Layout.Tuple_Field_Offset
                          (B.Ty, Natural'Value (FName));
                     else
                        Off := B.Offset + Kurt.Layout.Field_Offset
                          (SU.To_String (B.Ty.Name), FName);
                     end if;
                     IO.Put_Line (F, "    add     " & Xreg & ", x29, #"
                                     & Img (Off));
                  end if;
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
         Lower_CAS;
      when E_Cast =>
         Lower_Cast;
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
            DS  : constant Cell_Count := Kurt.Layout.Enum_Disc_Size (EN);
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
            Pay_Off : constant Cell_Count :=
              B.Offset + Kurt.Layout.Variant_Field_Offset
                           (Inner_Ty, Succ_V, 1);
            Pay_Ty  : constant Type_Access :=
              Kurt.Layout.Variant_Field_Type (Inner_Ty, Succ_V, 1);
            Pay_Sz  : constant Cell_Count := Sizeof (Pay_Ty);
            Whole_Sz : constant Cell_Count := Sizeof (Inner_Ty);
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
               --  §7.2.1: exchange the success/failure variants. The
               --  result type (Inv_T) is OT itself for the self-inverse
               --  case (bool, or any contract enum with no declared
               --  inverted pair) and the declared pair's type otherwise
               --  (Kurt.Sema.Check.Infer already resolved E.Sem_Ty) --
               --  either way, the payload cross-match sema enforces means
               --  the payload bits are preserved unchanged; only the
               --  discriminant is rewritten, to Inv_T's OWN corresponding
               --  variant's discriminant value (spec 7.2.1).
               declare
                  Inv_T : constant Type_Access :=
                    (if E.Sem_Ty /= null then E.Sem_Ty else OT);
                  Is_Bool : constant Boolean :=
                    SU.To_String (OT.Name) = "bool";
                  Has_Pay : constant Boolean :=
                    not Is_Bool and then Kurt.Layout.Enum_Has_Payload
                      (SU.To_String (OT.Name));
                  DSz : constant Cell_Count :=
                    (if Is_Bool then 1
                     else Kurt.Layout.Enum_Disc_Size
                       (SU.To_String (OT.Name)));
               begin
                  if Has_Pay then
                     --  Whole ≤8B aggregate in the register: test the
                     --  masked discriminant against OT's success value,
                     --  then bfi in Inv_T's corresponding (fail/success)
                     --  discriminant.
                     IO.Put_Line (F, "    and     x12, " & Xreg & ", #0x"
                       & (case DSz is
                             when 1 => "ff", when 2 => "ffff",
                             when others => "ffffffff"));
                     Lower_Imm (F, 13, Contract_Succ_Val (OT), True);
                     IO.Put_Line (F, "    cmp     x12, x13");
                     Lower_Imm (F, 12, Contract_Fail_Val (Inv_T), True);
                     Lower_Imm (F, 13, Contract_Succ_Val (Inv_T), True);
                     IO.Put_Line (F, "    csel    x12, x12, x13, eq");
                     IO.Put_Line (F, "    bfi     " & Xreg
                                     & ", x12, #0, #" & Img (8 * DSz));
                  else
                     --  Scalar discriminant: select the opposite value.
                     Lower_Imm (F, 12, Contract_Succ_Val (OT), True);
                     IO.Put_Line (F, "    cmp     " & Xreg & ", x12");
                     Lower_Imm (F, 12, Contract_Fail_Val (Inv_T), True);
                     Lower_Imm (F, 13, Contract_Succ_Val (Inv_T), True);
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
