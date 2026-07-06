separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Extract (E : Expr_Access) is
      FN     : constant String  := SU.To_String (ST.Fn_Name);
      Idx    : constant Natural := ST.If_Idx;
      L_Fail : constant String  := "Lextr_" & FN & "_fail_" & Img (Idx);
      L_End  : constant String  := "Lextr_" & FN & "_end_" & Img (Idx);
   begin
      ST.If_Idx := ST.If_Idx + 1;
      declare
         --  §7.2.1: when E.Ex_Inner is itself a polarity inversion (`!cv`),
         --  Kurt.Sema.Check.Infer already resolved its Sem_Ty to the
         --  inverted enum -- IT names the type whose success/failure
         --  variants apply here, regardless of which form Ex_Inner takes.
         IT   : constant Type_Access := Type_Of_Expr (E.Ex_Inner, ST);
         EN   : constant String := SU.To_String (IT.Name);
         Succ_V : constant String := Kurt.Layout.Contract_Success_Variant (EN);
         Fail_V : constant String := Kurt.Layout.Contract_Fail_Variant (EN);
         DSz    : constant Cell_Count := Kurt.Layout.Enum_Disc_Size (EN);
         Whole_Sz : constant Cell_Count := Sizeof (IT);
      begin
         if Whole_Sz > 8 then
            raise Codegen_Error with
              "not yet supported: a `contract` operand wider than 8 "
              & "bytes (bootstrap, spec 7.2.3)";
         end if;
         --  Materialise E.Ex_Inner's value (evaluated generally -- a
         --  binding, a polarity inversion, a call, ... anything
         --  Lower_Expr_Into_Reg produces a register value for) in a fresh
         --  stack temp, so its discriminant and payload can be addressed
         --  by offset exactly like any other frame-resident enum value.
         declare
            Off : constant Cell_Count := ST.Next_Offset;
            Loc : constant String := ", [x29, #" & Img (Off) & "]";
         begin
            ST.Next_Offset := ST.Next_Offset + 8;
            Lower_Expr_Into_Reg (F, E.Ex_Inner, 9, ST);
            IO.Put_Line (F, "    str     x9" & Loc);

            if DSz >= 4 then
               IO.Put_Line (F, "    ldr     w10" & Loc);
            elsif DSz = 2 then
               IO.Put_Line (F, "    ldrh    w10" & Loc);
            else
               IO.Put_Line (F, "    ldrb    w10" & Loc);
            end if;
            Lower_Imm (F, 11, Kurt.Layout.Variant_Value (EN, Succ_V), False);
            IO.Put_Line (F, "    cmp     w10, w11");
            IO.Put_Line (F, "    b.ne    " & L_Fail);

            --  Success: the payload (if any) becomes this expression's
            --  value; a void payload leaves Target_Reg untouched.
            declare
               Succ_Ty : constant Type_Access :=
                 Kurt.Layout.Variant_Field_Type (IT, Succ_V, 1);
               Sz      : constant Cell_Count := Sizeof (Succ_Ty);
               POff    : constant Cell_Count :=
                 Off + Kurt.Layout.Variant_Field_Offset (IT, Succ_V, 1);
            begin
               if Sz >= 8 then
                  IO.Put_Line (F, "    ldr     " & Xreg & ", [x29, #"
                                  & Img (POff) & "]");
               elsif Sz = 4 then
                  IO.Put_Line (F, "    ldr     " & Wreg & ", [x29, #"
                                  & Img (POff) & "]");
               elsif Sz = 2 then
                  IO.Put_Line (F, "    ldrh    " & Wreg & ", [x29, #"
                                  & Img (POff) & "]");
               elsif Sz = 1 then
                  IO.Put_Line (F, "    ldrb    " & Wreg & ", [x29, #"
                                  & Img (POff) & "]");
               end if;   --  Sz = 0 (void): nothing to load
            end;
            IO.Put_Line (F, "    b       " & L_End);

            --  Failure: bind `.id` to the failure payload (if named), in
            --  scope only for `fallback` -- its value (or its divergence)
            --  becomes this expression's result.
            IO.Put_Line (F, L_Fail & ":");
            declare
               Saved : constant Natural := Natural (ST.Bindings.Length);
            begin
               if SU.Length (E.Ex_Err) > 0 then
                  ST.Bindings.Append
                    ((Name   => E.Ex_Err,
                      Offset => Off
                        + Kurt.Layout.Variant_Field_Offset (IT, Fail_V, 1),
                      Ty     => Kurt.Layout.Variant_Field_Type
                                  (IT, Fail_V, 1)));
               end if;
               Lower_Expr_Into_Reg (F, E.Ex_Fallback, Target_Reg, ST);
               while Natural (ST.Bindings.Length) > Saved loop
                  ST.Bindings.Delete_Last;
               end loop;
            end;
            IO.Put_Line (F, L_End & ":");
         end;
      end;
   end Lower_Extract;
