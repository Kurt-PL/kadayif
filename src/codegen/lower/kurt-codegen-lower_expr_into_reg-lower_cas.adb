separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_CAS is
   begin
         --  §8.7 compare-and-swap via an exclusive load/store loop.
         --  Result: the verdict.<T, T> aggregate (≤ 8 bytes) built in
         --  x<Target_Reg> with the discriminant at bit 0 and the payload
         --  (old value on success, actual on failure) at its field offset.
         declare
            Tgt_Ty : constant Type_Access := Type_Of_Expr (E.CAS_Tgt, ST);
            Ref_T  : constant Type_Access :=
              (if Is_Ref (Tgt_Ty) then Tgt_Ty.Target else null);
            Sz     : constant Cell_Count := Sizeof (Ref_T);
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
               PO : constant Cell_Count := Kurt.Layout.Variant_Field_Offset
                 (E.Sem_Ty, Kurt.Layout.Contract_Success_Variant (EN), 1);
            begin
               IO.Put_Line (F, "    lsl     " & Xreg & ", x13, #"
                               & Img (8 * PO));
               IO.Put_Line (F, "    orr     " & Xreg & ", " & Xreg
                               & ", x12");
            end;
         end;

   end Lower_CAS;
