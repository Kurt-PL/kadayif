separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_Assign is
   begin
         --  §6.1.8: `place = uninit;` stores nothing (the object keeps its
         --  current, uninitialized contents), but (spec 6.1.8) the
         --  assignment still establishes the §5.2 initialization
         --  determination -- so a deferred binding's drop flag, if any,
         --  is armed here exactly as a real store would arm it below.
         if S.Asn_Rhs.Kind = E_Uninit then
            if S.Asn_Lhs.Kind = E_Path
              and then Natural (S.Asn_Lhs.Segments.Length) = 1
            then
               declare
                  Idx : constant Natural := Find_Binding
                    (ST, SU.To_String (S.Asn_Lhs.Segments.Last_Element));
               begin
                  if Idx /= 0 then
                     declare
                        FOff : constant Long_Long_Integer :=
                          Flag_Off_Of (ST, ST.Bindings.Element (Idx).Offset);
                     begin
                        if FOff >= 0 then
                           IO.Put_Line (F, "    mov     w9, #1");
                           IO.Put_Line (F, "    strb    w9, [x29, #"
                                           & Img (FOff) & "]");
                        end if;
                     end;
                  end if;
               end;
            end if;
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
                        Sz  : constant Cell_Count :=
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
                  Sz : constant Cell_Count := Sizeof (B.Ty);
               begin
                  Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                  if Is_Ref (B.Ty) or else Sz > 4 then
                     IO.Put_Line (F, "    str     x9, [x29, #"
                                     & Img (B.Offset) & "]");
                  else
                     IO.Put_Line (F, "    str     w9, [x29, #"
                                     & Img (B.Offset) & "]");
                  end if;
                  --  §5.2/§8.11: this store reaches the binding's whole
                  --  object -- if it owns a runtime drop flag (its type
                  --  satisfies `destruct`), arm it. Covers both an
                  --  ordinary re-assignment and the first assignment that
                  --  completes a deferred (`let x: T;` / `mut x: T;`)
                  --  binding's initialization, which Lower_Let leaves
                  --  disarmed until now.
                  declare
                     FOff : constant Long_Long_Integer :=
                       Flag_Off_Of (ST, B.Offset);
                  begin
                     if FOff >= 0 then
                        IO.Put_Line (F, "    mov     w9, #1");
                        IO.Put_Line (F, "    strb    w9, [x29, #"
                                        & Img (FOff) & "]");
                     end if;
                  end;
               end;
            end;
         elsif S.Asn_Lhs.Kind = E_Deref then
            declare
               Inner_Ty : constant Type_Access :=
                 Type_Of_Expr (S.Asn_Lhs.D_Inner, ST);
               Sz       : Cell_Count := 8;
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
                  --
                  --  §8.9: a store through a tracked reference to a
                  --  referent type satisfying §8.11 `destruct` must run
                  --  the OLD value's destructor before the new value is
                  --  stored, or the old value leaks. Both the address and
                  --  the rhs are evaluated first (§2.7 place-before-value),
                  --  then the old value is destroyed, then stored — so the
                  --  address (needed by the destructor call, and again by
                  --  the store) and the rhs (which the destructor's `bl`
                  --  would otherwise clobber) are spilled to frame slots
                  --  that survive the call, not just the sp scratch used
                  --  for a plain scalar store.
                  declare
                     Referent_Ty : constant Type_Access :=
                       (if Is_Ref (Inner_Ty) then Inner_Ty.Target else null);
                     Needs_Drop  : constant Boolean :=
                       not Is_Atom
                         and then Kurt.Layout.Satisfies_Destruct
                                    (Referent_Ty);
                  begin
                     if Needs_Drop then
                        declare
                           Addr_Slot : constant Cell_Count := ST.Next_Offset;
                           Rhs_Slot  : constant Cell_Count :=
                             ST.Next_Offset + 8;
                        begin
                           ST.Next_Offset := ST.Next_Offset + 16;
                           Lower_Expr_Into_Reg (F, S.Asn_Lhs.D_Inner, 10, ST);
                           IO.Put_Line (F, "    str     x10, [x29, #"
                                           & Img (Addr_Slot) & "]");
                           Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                           IO.Put_Line (F, "    str     x9, [x29, #"
                                           & Img (Rhs_Slot) & "]");
                           Emit_Drop_At (F, Addr_Slot, 0, Referent_Ty);
                           IO.Put_Line (F, "    ldr     x10, [x29, #"
                                           & Img (Addr_Slot) & "]");
                           IO.Put_Line (F, "    ldr     x9, [x29, #"
                                           & Img (Rhs_Slot) & "]");
                        end;
                     else
                        Lower_Expr_Into_Reg (F, S.Asn_Lhs.D_Inner, 10, ST);
                        IO.Put_Line (F, "    sub     sp, sp, #16");
                        IO.Put_Line (F, "    str     x10, [sp]");
                        Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                        IO.Put_Line (F, "    ldr     x10, [sp]");
                        IO.Put_Line (F, "    add     sp, sp, #16");
                     end if;
                  end;
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
           and then (SU.To_String (S.Asn_Lhs.F_Name) = "ptr"
                     or else SU.To_String (S.Asn_Lhs.F_Name) = "len")
         then
            --  §8.1.4: a store to the materialized `.ptr`/`.len` fields of
            --  an array/slice REFERENCE binding -- legal per
            --  Kurt.Sema.Check's storability matrix (a `mut`-bound
            --  reference landside, or either binding kind in `airside`).
            --  An array VALUE's `.ptr`/`.len` is a projection and
            --  Kurt.Sema.Check already rejects any store to it (spec
            --  8.1.4), so that shape cannot legally reach here; guard it
            --  with a clean diagnostic rather than the CONSTRAINT_ERROR
            --  that reading a T_Array type's absent `.Name` discriminant
            --  used to raise.
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
                  B      : constant Binding := ST.Bindings.Element (Idx);
                  Is_Len : constant Boolean :=
                    SU.To_String (S.Asn_Lhs.F_Name) = "len";
               begin
                  if B.Ty = null or else B.Ty.Kind /= T_Ref
                    or else B.Ty.Target = null
                    or else B.Ty.Target.Kind /= T_Array
                  then
                     raise Codegen_Error with
                       "not yet supported: store to '."
                       & SU.To_String (S.Asn_Lhs.F_Name)
                       & "' of an array value's fat-reference view "
                       & "(bootstrap; spec 8.1.4 makes this a translation "
                       & "failure in Kurt.Sema.Check, so this should be "
                       & "unreachable)";
                  end if;
                  --  §8.1.4 stored representation: ptr at offset 0, len
                  --  at offset (%T)@size -- 8 bytes on this target.
                  Lower_Expr_Into_Reg (F, S.Asn_Rhs, 9, ST);
                  IO.Put_Line (F, "    str     x9, [x29, #"
                                  & Img (B.Offset
                                         + (if Is_Len then 8 else 0))
                                  & "]");
               end;
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
                  FOff  : constant Cell_Count :=
                    Kurt.Layout.Field_Offset (SName, FName);
                  FT    : constant Type_Access :=
                    Kurt.Layout.Field_Type (SName, FName);
                  Sz    : constant Cell_Count := Sizeof (FT);
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

   end Lower_Assign;
