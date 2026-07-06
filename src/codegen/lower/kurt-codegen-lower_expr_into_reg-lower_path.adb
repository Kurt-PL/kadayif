separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Path is
   begin
         --  §9.3.2 associated-const access resolved by sema to a value.
         if E.P_Assoc_Val /= null then
            Lower_Expr_Into_Reg (F, E.P_Assoc_Val, Target_Reg, ST);
            return;
         end if;
         --  §4.10: a bare subroutine name used as a value — load its
         --  address (the subroutine pointer).
         if E.P_Is_Fn_Ptr then
            declare
               --  §5.15: an `@symbol` override on the referenced fn applies
               --  here too — the pointer value must be the same address a
               --  direct call to it would branch to.
               Nm  : constant String :=
                 SU.To_String (E.Segments.Last_Element);
               Sym : constant String := Fn_Symbol_Of (ST, Nm);
               Lbl : constant String := "_" & (if Sym /= "" then Sym else Nm);
            begin
               IO.Put_Line (F, "    adrp    " & Xreg & ", " & Lbl & "@PAGE");
               IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                               & ", " & Lbl & "@PAGEOFF");
               return;
            end;
         end if;
         if Natural (E.Segments.Length) = 1 then
            declare
               Name : constant String :=
                 SU.To_String (E.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  --  §5.4: fall back to a static binding (global label).
                  declare
                     SI : constant Natural := Find_Static (Name);
                  begin
                     if SI = 0 then
                        raise Program_Error with
                          "codegen: unknown binding '" & Name & "'";
                     end if;
                     declare
                        Sz  : constant Cell_Count :=
                          Sizeof (Unit_Statics.Element (SI).Ty);
                        Lbl : constant String := "_Kst_" & Name;
                     begin
                        IO.Put_Line (F, "    adrp    " & Xreg & ", "
                                        & Lbl & "@PAGE");
                        IO.Put_Line (F, "    add     " & Xreg & ", "
                                        & Xreg & ", " & Lbl & "@PAGEOFF");
                        if Sz >= 8 then
                           IO.Put_Line (F, "    ldr     " & Xreg
                                           & ", [" & Xreg & "]");
                        elsif Sz = 4 then
                           IO.Put_Line (F, "    ldr     " & Wreg
                                           & ", [" & Xreg & "]");
                        elsif Sz = 2 then
                           IO.Put_Line (F, "    ldrh    " & Wreg
                                           & ", [" & Xreg & "]");
                        else
                           IO.Put_Line (F, "    ldrb    " & Wreg
                                           & ", [" & Xreg & "]");
                        end if;
                        return;
                     end;
                  end;
               end if;
               declare
                  B   : constant Binding := ST.Bindings.Element (Idx);
                  Sz  : constant Cell_Count := Sizeof (B.Ty);
                  Loc : constant String :=
                    ", [x29, #" & Img (B.Offset) & "]";
               begin
                  --  Load width matches the store width (see Store_Sized) so
                  --  e.g. a 1-cell enum discriminant round-trips. Scalars are
                  --  always a power-of-two size (1/2/4/8); an odd width (3, 5,
                  --  6, 7) only occurs for a small aggregate passed by value
                  --  in a single register (§8.8.1), where the covering wider
                  --  load gathers all the payload bytes — the high junk bytes
                  --  above the type width are ignored by the callee.
                  if Is_Ref (B.Ty) or else Sz >= 5 then
                     IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                  elsif Sz >= 3 then
                     IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                  elsif Sz = 2 then
                     IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                  else
                     IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                  end if;
               end;
            end;
         elsif Natural (E.Segments.Length) = 2 then
            --  Enum variant: materialise its discriminant value. The
            --  concrete enum is taken from Sem_Ty (so generic instances
            --  resolve to e.g. Opt$si4), falling back to the written name.
            declare
               EN : constant String :=
                 (if E.Sem_Ty /= null and then E.Sem_Ty.Kind = T_Named
                  then SU.To_String (E.Sem_Ty.Name)
                  else SU.To_String (E.Segments.First_Element));
               VN : constant String :=
                 SU.To_String (E.Segments.Last_Element);
            begin
               if Kurt.Layout.Is_Enum (EN)
                 and then Kurt.Layout.Has_Variant (EN, VN)
               then
                  Lower_Imm (F, Target_Reg,
                    Kurt.Layout.Variant_Value (EN, VN),
                    Sizeof (E.Sem_Ty) > 4);
               else
                  raise Program_Error with
                    "codegen: '" & EN & "::" & VN
                    & "' is not a known enum variant";
               end if;
            end;
         else
            raise Program_Error with
              "codegen: multi-segment path as value not supported "
              & "(only enum variants or call callees)";
         end if;

   end Lower_Path;
