separate (Kurt.Codegen)
   procedure Emit_Mem_Copy
     (F        : IO.File_Type;
      Src_Base : String; Src_Off : Cell_Count;
      Dst_Base : String; Dst_Off : Cell_Count;
      Sz       : Cell_Count)
   is
      Done : Cell_Count := 0;
   begin
      while Sz - Done >= 8 loop
         IO.Put_Line (F, "    ldr     x9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    str     x9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 8;
      end loop;
      if Sz - Done >= 4 then
         IO.Put_Line (F, "    ldr     w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    str     w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 4;
      end if;
      if Sz - Done >= 2 then
         IO.Put_Line (F, "    ldrh    w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    strh    w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 2;
      end if;
      if Sz - Done >= 1 then
         IO.Put_Line (F, "    ldrb    w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    strb    w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
      end if;
   end Emit_Mem_Copy;
