separate (Kurt.Codegen)
   procedure Emit_Truthify
     (F : IO.File_Type; Reg : Natural; Ty : Type_Access)
   is
      XR  : constant String := "x" & Img (Reg);
      WR  : constant String := "w" & Img (Reg);
      DSz : constant Natural :=
        (if SU.To_String (Ty.Name) = "bool" then 1
         else Kurt.Layout.Enum_Disc_Size (SU.To_String (Ty.Name)));
      Src : constant String := (if DSz < 8 then "x12" else XR);
   begin
      if DSz < 8 then
         IO.Put_Line (F, "    and     x12, " & XR & ", #0x"
           & (case DSz is
                 when 1 => "ff", when 2 => "ffff",
                 when others => "ffffffff"));
      end if;
      Lower_Imm (F, 13, Contract_Succ_Val (Ty), True);
      IO.Put_Line (F, "    cmp     " & Src & ", x13");
      IO.Put_Line (F, "    cset    " & WR & ", eq");
   end Emit_Truthify;
