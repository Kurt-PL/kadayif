separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_If is
   begin
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
                              + Pat_Field_Off (S.SI_Let_Pat, B.Ty, VN, K),
                            Ty     => Pat_Field_Ty
                                        (S.SI_Let_Pat, B.Ty, VN, K)));
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

   end Lower_If;
