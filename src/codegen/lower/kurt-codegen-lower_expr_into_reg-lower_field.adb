separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Field is
   begin
         if E.F_Recv.Kind = E_String_Lit
           and then SU.To_String (E.F_Name) = "ptr"
         then
            declare
               Label : constant String := "Lstr" & Img (ST.Next_Str_Idx);
            begin
               ST.Next_Str_Idx := ST.Next_Str_Idx + 1;
               IO.Put_Line (F, "    adrp    " & Xreg & ", " & Label
                               & "@PAGE");
               IO.Put_Line (F, "    add     " & Xreg & ", " & Xreg
                               & ", " & Label & "@PAGEOFF");
            end;
         elsif E.F_Recv.Kind = E_Path
           and then Natural (E.F_Recv.Segments.Length) = 1
         then
            --  Struct field load: the struct lives inline in its stack
            --  slot, so the field is at [x29, slot_off + field_off].
            declare
               Name : constant String :=
                 SU.To_String (E.F_Recv.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  raise Program_Error with
                    "codegen: unknown binding '" & Name & "'";
               end if;
               declare
                  B     : constant Binding := ST.Bindings.Element (Idx);
                  FName : constant String  := SU.To_String (E.F_Name);
                  Off   : Cell_Count;
                  FT    : Type_Access;
               begin
                  if B.Ty /= null and then B.Ty.Kind = T_Ref
                    and then B.Ty.Target /= null
                    and then B.Ty.Target.Kind = T_Named
                    and then Kurt.Layout.Is_Struct
                      (SU.To_String (B.Ty.Target.Name))
                  then
                     --  §6.2.5 reference transparency: `self.f` — load the
                     --  reference, then the field through it.
                     declare
                        SName : constant String :=
                          SU.To_String (B.Ty.Target.Name);
                        FOff  : constant Cell_Count :=
                          Kurt.Layout.Field_Offset (SName, FName);
                        FT2   : constant Type_Access :=
                          Kurt.Layout.Field_Type (SName, FName);
                        Sz    : constant Cell_Count := Sizeof (FT2);
                        Loc   : constant String :=
                          ", [x10, #" & Img (FOff) & "]";
                     begin
                        IO.Put_Line (F, "    ldr     x10, [x29, #"
                                        & Img (B.Offset) & "]");
                        if Is_Ref (FT2) or else Sz >= 8 then
                           IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                        elsif Sz = 4 then
                           IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                        elsif Sz = 2 then
                           IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                        else
                           IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                        end if;
                     end;
                     return;
                  end if;
                  if Is_Slice_Ref (B.Ty) then
                     --  §8.1.4 materialised slice view: load `.ptr` from
                     --  the fat reference's first field, `.len` from the
                     --  second.
                     if FName = "ptr" then
                        IO.Put_Line (F, "    ldr     " & Xreg
                          & ", [x29, #" & Img (B.Offset) & "]");
                     elsif FName = "len" then
                        IO.Put_Line (F, "    ldr     " & Xreg
                          & ", [x29, #" & Img (B.Offset + 8) & "]");
                     else
                        raise Program_Error with
                          "codegen: slice has no field '" & FName & "'";
                     end if;
                     return;
                  end if;
                  if B.Ty /= null and then B.Ty.Kind = T_Array then
                     --  §8.1.4 array views: `.ptr` is the first element's
                     --  address, `.len` the (static) element count.
                     if FName = "ptr" then
                        IO.Put_Line (F, "    add     " & Xreg & ", x29, #"
                                        & Img (B.Offset));
                     elsif FName = "len" then
                        Lower_Imm (F, Target_Reg,
                          Long_Long_Integer (B.Ty.Len), True);
                     else
                        raise Program_Error with
                          "codegen: array has no field '" & FName & "'";
                     end if;
                     return;
                  end if;
                  if B.Ty /= null and then B.Ty.Kind = T_Tuple then
                     --  §6.2.2 tuple field by index `.N`.
                     declare
                        TI : constant Natural := Natural'Value (FName);
                     begin
                        Off := B.Offset
                          + Kurt.Layout.Tuple_Field_Offset (B.Ty, TI);
                        FT  := Kurt.Layout.Tuple_Field_Type (B.Ty, TI);
                     end;
                  else
                     declare
                        SName : constant String := SU.To_String (B.Ty.Name);
                     begin
                        Off := B.Offset
                          + Kurt.Layout.Field_Offset (SName, FName);
                        FT  := Kurt.Layout.Field_Type (SName, FName);
                     end;
                  end if;
                  declare
                     Sz  : constant Cell_Count := Sizeof (FT);
                     Loc : constant String  :=
                       ", [x29, #" & Img (Off) & "]";
                  begin
                     if Is_Ref (FT) or else Sz >= 8 then
                        IO.Put_Line (F, "    ldr     " & Xreg & Loc);
                     elsif Sz = 4 then
                        IO.Put_Line (F, "    ldr     " & Wreg & Loc);
                     elsif Sz = 2 then
                        IO.Put_Line (F, "    ldrh    " & Wreg & Loc);
                     else
                        IO.Put_Line (F, "    ldrb    " & Wreg & Loc);
                     end if;
                  end;
               end;
            end;
         else
            raise Program_Error with
              "codegen: unsupported field access form";
         end if;

   end Lower_Field;
