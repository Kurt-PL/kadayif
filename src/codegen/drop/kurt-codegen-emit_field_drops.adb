separate (Kurt.Codegen)
   procedure Emit_Field_Drops
     (F : IO.File_Type; Tn : String; Self_Off : Natural)
   is
   begin
      if Kurt.Layout.Is_Struct (Tn) then
         --  §8.11/§8.4.3 fields are destroyed per Struct_Destroy_Order:
         --  reverse declaration order by default, reordered where a
         --  `with lifetime` chain requires it (shorter-lived first).
         for I of Kurt.Layout.Struct_Destroy_Order (Tn) loop
            declare
               FN : constant String := Kurt.Layout.Struct_Field_Name (Tn, I);
               FT : constant Kurt.Parser.Type_Access :=
                      Kurt.Layout.Field_Type (Tn, FN);
            begin
               if Kurt.Layout.Satisfies_Destruct (FT) then
                  Emit_Drop_At (F, Self_Off,
                                Kurt.Layout.Field_Offset (Tn, FN), FT);
               end if;
            end;
         end loop;
      elsif Kurt.Layout.Is_Enum (Tn) then
         declare
            Disc_Size : constant Natural := Kurt.Layout.Enum_Disc_Size (Tn);
            End_Lbl   : constant String  := "L" & Tn & "$drop_end";
         begin
            if Disc_Size = 0 then
               return;   --  void discriminant: at most one (empty) variant
            end if;
            IO.Put_Line (F, "    ldr     x9, [x29, #" & Img (Self_Off) & "]");
            case Disc_Size is
               when 1      => IO.Put_Line (F, "    ldrb    w10, [x9]");
               when 2      => IO.Put_Line (F, "    ldrh    w10, [x9]");
               when others => IO.Put_Line (F, "    ldr     w10, [x9]");
            end case;
            for V in 1 .. Kurt.Layout.Variant_Count (Tn) loop
               declare
                  VNm : constant String := Kurt.Layout.Variant_Name (Tn, V);
                  Has : Boolean := False;
               begin
                  for FNo in 1 .. Kurt.Layout.Variant_Field_Count (Tn, VNm)
                  loop
                     if Kurt.Layout.Satisfies_Destruct
                          (Kurt.Layout.Variant_Field_Type (Tn, VNm, FNo))
                     then
                        Has := True;
                     end if;
                  end loop;
                  if Has then
                     declare
                        VVal : constant Long_Long_Integer :=
                          Kurt.Layout.Variant_Value (Tn, VNm);
                        Skip : constant String :=
                          "L" & Tn & "$drop_v" & Img (V);
                     begin
                        IO.Put_Line (F, "    mov     w11, #" & Img (VVal));
                        IO.Put_Line (F, "    cmp     w10, w11");
                        IO.Put_Line (F, "    b.ne    " & Skip);
                        --  §8.11/§8.4.3 see Struct_Destroy_Order above.
                        for FNo of
                          Kurt.Layout.Variant_Destroy_Order (Tn, VNm)
                        loop
                           declare
                              FT2 : constant Kurt.Parser.Type_Access :=
                                Kurt.Layout.Variant_Field_Type (Tn, VNm, FNo);
                           begin
                              if Kurt.Layout.Satisfies_Destruct (FT2) then
                                 Emit_Drop_At
                                   (F, Self_Off,
                                    Kurt.Layout.Variant_Field_Offset
                                      (Tn, VNm, FNo), FT2);
                              end if;
                           end;
                        end loop;
                        IO.Put_Line (F, "    b       " & End_Lbl);
                        IO.Put_Line (F, Skip & ":");
                     end;
                  end if;
               end;
            end loop;
            IO.Put_Line (F, End_Lbl & ":");
         end;
      end if;
   end Emit_Field_Drops;
