separate (Kurt.Codegen)
   procedure Emit_Binding_Drops
     (F : IO.File_Type; ST : in out Lower_State;
      Keep : Natural; Preserve_Ret : Boolean)
   is
      To_Drop : Binding_Pkg.Vector;
   begin
      for I in reverse (Keep + 1) .. Natural (ST.Bindings.Length) loop
         declare
            B : constant Binding := ST.Bindings.Element (I);
         begin
            if B.Ty /= null and then B.Ty.Kind = T_Named
              and then Type_Has_Drop (SU.To_String (B.Ty.Name))
            then
               To_Drop.Append (B);
            --  §8.11.1 an array local whose element type has a destructor:
            --  each element is destroyed at scope exit.
            elsif B.Ty /= null and then B.Ty.Kind = T_Array
              and then B.Ty.Elem /= null and then B.Ty.Elem.Kind = T_Named
              and then Type_Has_Drop (SU.To_String (B.Ty.Elem.Name))
            then
               To_Drop.Append (B);
            end if;
         end;
      end loop;

      if To_Drop.Is_Empty then
         return;
      end if;
      if Preserve_Ret then
         IO.Put_Line (F, "    str     x0, [x29, #"
                         & Img (ST.Ret_Scratch) & "]");
         IO.Put_Line (F, "    str     x1, [x29, #"
                         & Img (ST.Ret_Scratch + 8) & "]");
      end if;
      for B of To_Drop loop
         declare
            FOff : constant Integer := Flag_Off_Of (ST, B.Offset);

            --  Emit the destructor call(s) for one binding: a single call for
            --  a `T_Named`, or one per element (index order, §8.11.1) for an
            --  array of destructor-bearing elements.
            procedure Emit_Calls is
            begin
               if B.Ty.Kind = T_Array then
                  declare
                     ES : constant Natural :=
                       Kurt.Layout.Size_Of (B.Ty.Elem);
                     DN : constant String := SU.To_String (B.Ty.Elem.Name);
                  begin
                     for K in 0 .. B.Ty.Len - 1 loop
                        IO.Put_Line (F, "    add     x0, x29, #"
                                        & Img (B.Offset + K * ES));
                        IO.Put_Line (F, "    bl      _" & DN & "$drop");
                     end loop;
                  end;
               else
                  IO.Put_Line (F, "    add     x0, x29, #" & Img (B.Offset));
                  IO.Put_Line (F, "    bl      _"
                                  & SU.To_String (B.Ty.Name) & "$drop");
               end if;
            end Emit_Calls;
         begin
            if FOff >= 0 then
               declare
                  Lbl : constant String := "Ldrop_"
                    & SU.To_String (ST.Fn_Name) & "_" & Img (ST.Flag_Lbl);
               begin
                  ST.Flag_Lbl := ST.Flag_Lbl + 1;
                  IO.Put_Line (F, "    ldrb    w9, [x29, #"
                                  & Img (FOff) & "]");
                  IO.Put_Line (F, "    cbz     w9, " & Lbl);
                  Emit_Calls;
                  IO.Put_Line (F, Lbl & ":");
               end;
            else
               Emit_Calls;
            end if;
         end;
      end loop;
      if Preserve_Ret then
         IO.Put_Line (F, "    ldr     x0, [x29, #"
                         & Img (ST.Ret_Scratch) & "]");
         IO.Put_Line (F, "    ldr     x1, [x29, #"
                         & Img (ST.Ret_Scratch + 8) & "]");
      end if;
   end Emit_Binding_Drops;
