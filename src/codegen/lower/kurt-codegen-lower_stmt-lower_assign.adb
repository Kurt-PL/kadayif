separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_Assign is
   begin
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

   end Lower_Assign;
