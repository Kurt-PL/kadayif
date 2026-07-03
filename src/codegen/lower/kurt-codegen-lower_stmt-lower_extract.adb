separate (Kurt.Codegen.Lower_Stmt)
   procedure Lower_Extract is
   begin
         --  §7: `let v <- e else err { ... }`. Branch on e's discriminant;
         --  on failure bind err and run the (diverging) else block, on
         --  success bind v as a slot+offset alias for the rest of scope.
         declare
            FN     : constant String  := SU.To_String (ST.Fn_Name);
            Idx    : constant Natural := ST.If_Idx;
            L_Succ : constant String := "Lextr_" & FN & "_ok_" & Img (Idx);
            L_XEnd : constant String := "Lextr_" & FN & "_end_" & Img (Idx);
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
               --  §7.2.3: in the place form the else may fall through (the
               --  place keeps its prior value); skip the success copy. (For
               --  the `let` form the else diverges, so this is dead.)
               IO.Put_Line (F, "    b       " & L_XEnd);

               IO.Put_Line (F, L_Succ & ":");
               if S.X_Is_Place then
                  --  §7.2.3 copy the success payload into the existing place.
                  declare
                     PBi : constant Natural :=
                       Find_Binding (ST, SU.To_String (S.X_Bind));
                     Pay_Off : constant Natural := B.Offset
                       + Kurt.Layout.Variant_Field_Offset (B.Ty, Succ_V, 1);
                     Sz : constant Natural := Sizeof
                       (Kurt.Layout.Variant_Field_Type (B.Ty, Succ_V, 1));
                     POff : constant Natural :=
                       ST.Bindings.Element (PBi).Offset;
                     Ld : constant String :=
                       (if Sz >= 8 then "ldr     x9" elsif Sz >= 4
                        then "ldr     w9" elsif Sz = 2 then "ldrh    w9"
                        else "ldrb    w9");
                     St : constant String :=
                       (if Sz >= 8 then "str     x9" elsif Sz >= 4
                        then "str     w9" elsif Sz = 2 then "strh    w9"
                        else "strb    w9");
                  begin
                     IO.Put_Line (F, "    " & Ld & ", [x29, #"
                                     & Img (Pay_Off) & "]");
                     IO.Put_Line (F, "    " & St & ", [x29, #"
                                     & Img (POff) & "]");
                  end;
               else
                  --  Success: bind v permanently for the rest of the block.
                  ST.Bindings.Append
                    ((Name   => S.X_Bind,
                      Offset => B.Offset
                        + Kurt.Layout.Variant_Field_Offset (B.Ty, Succ_V, 1),
                      Ty     => Kurt.Layout.Variant_Field_Type
                                  (B.Ty, Succ_V, 1)));
               end if;
               IO.Put_Line (F, L_XEnd & ":");
            end;
         end;

   end Lower_Extract;
