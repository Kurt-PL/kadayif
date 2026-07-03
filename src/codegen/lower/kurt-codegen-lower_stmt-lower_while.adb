separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_While is
   begin
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
                Body_Entry => Natural (ST.Bindings.Length),
                Result_Off => -1));
            IO.Put_Line (F, L_Top & ":");
            if S.W_Is_Let then
               --  §7.5.1 `while let Enum::Variant { binds } = e`. Like
               --  `if let`, the bootstrap requires e to be a binding (a
               --  place); each iteration re-reads its discriminant, exits on
               --  a mismatch, and otherwise aliases the payload fields into
               --  the body. The body makes progress by reassigning the
               --  binding (which flips its discriminant).
               declare
                  CName : constant String :=
                    (if S.W_Cond.Kind = E_Path
                        and then Natural (S.W_Cond.Segments.Length) = 1
                     then SU.To_String (S.W_Cond.Segments.Last_Element)
                     else "");
                  Bi : constant Natural :=
                    (if CName /= "" then Find_Binding (ST, CName) else 0);
               begin
                  if Bi = 0 then
                     raise Program_Error with
                       "codegen: `while let` scrutinee must be a binding";
                  end if;
                  declare
                     B    : constant Binding := ST.Bindings.Element (Bi);
                     EN   : constant String := SU.To_String (B.Ty.Name);
                     VN   : constant String :=
                       SU.To_String (S.W_Let_Pat.Path.Last_Element);
                     DSz  : constant Natural := Kurt.Layout.Enum_Disc_Size (EN);
                     Loc  : constant String :=
                       ", [x29, #" & Img (B.Offset) & "]";
                     Saved : Natural;
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
                        IO.Put_Line (F, "    b.ne    " & L_End);
                     end if;
                     --  Bind payload fields as slot+offset aliases for the
                     --  body. Appended below the body scope so Lower_Scoped
                     --  keeps them (they project into the scrutinee's storage
                     --  — dropping them would double-free).
                     Saved := Natural (ST.Bindings.Length);
                     for K in 1 .. Natural (S.W_Let_Pat.Bindings.Length) loop
                        ST.Bindings.Append
                          ((Name   => S.W_Let_Pat.Bindings.Element (K),
                            Offset => B.Offset
                              + Pat_Field_Off (S.W_Let_Pat, B.Ty, VN, K),
                            Ty     => Pat_Field_Ty
                                        (S.W_Let_Pat, B.Ty, VN, K)));
                     end loop;
                     Lower_Scoped (S.W_Body);
                     while Natural (ST.Bindings.Length) > Saved loop
                        ST.Bindings.Delete_Last;
                     end loop;
                  end;
               end;
            elsif S.W_Is_Contract then
               --  §7.5.1 `while cond -> v`. Like `if e -> v`, the bootstrap
               --  requires cond to be a contract-enum binding; each iteration
               --  re-reads its discriminant, exits on the failure variant,
               --  and otherwise aliases the success payload to `v`.
               declare
                  CName : constant String :=
                    (if S.W_Cond.Kind = E_Path
                        and then Natural (S.W_Cond.Segments.Length) = 1
                     then SU.To_String (S.W_Cond.Segments.Last_Element)
                     else "");
                  Bi : constant Natural :=
                    (if CName /= "" then Find_Binding (ST, CName) else 0);
               begin
                  if Bi = 0 then
                     raise Program_Error with
                       "codegen: `while ->` cond must be a contract binding";
                  end if;
                  declare
                     B      : constant Binding := ST.Bindings.Element (Bi);
                     EN     : constant String := SU.To_String (B.Ty.Name);
                     Succ_V : constant String :=
                       Kurt.Layout.Contract_Success_Variant (EN);
                     DSz    : constant Natural :=
                       Kurt.Layout.Enum_Disc_Size (EN);
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
                     IO.Put_Line (F, "    b.ne    " & L_End);
                     Saved := Natural (ST.Bindings.Length);
                     ST.Bindings.Append
                       ((Name   => S.W_Succ_Bind,
                         Offset => B.Offset
                           + Kurt.Layout.Variant_Field_Offset (B.Ty, Succ_V, 1),
                         Ty     => Kurt.Layout.Variant_Field_Type
                                     (B.Ty, Succ_V, 1)));
                     Lower_Scoped (S.W_Body);
                     while Natural (ST.Bindings.Length) > Saved loop
                        ST.Bindings.Delete_Last;
                     end loop;
                  end;
               end;
            else
               Lower_Expr_Into_Reg (F, S.W_Cond, 10, ST);
               IO.Put_Line (F, "    cbz     w10, " & L_End);
               --  §8.4: each iteration's body locals are destroyed at the
               --  body's end (before the loop-back), so every pass cleans up
               --  its own.
               Lower_Scoped (S.W_Body);
            end if;
            if Has_Then then
               IO.Put_Line (F, L_Thn & ":");
               Lower_Scoped (S.W_Then);
            end if;
            IO.Put_Line (F, "    b       " & L_Top);
            IO.Put_Line (F, L_End & ":");
            ST.Loops.Delete_Last;
         end;

   end Lower_While;
