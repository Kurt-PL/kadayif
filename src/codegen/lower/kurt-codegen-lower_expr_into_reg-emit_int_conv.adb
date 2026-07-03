separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Emit_Int_Conv
     (Src_Sz : Natural; Src_Signed : Boolean; Tgt_Sz : Natural) is
   begin
      if Tgt_Sz = Src_Sz then
         return;  --  identity / reinterpret
      elsif Tgt_Sz > Src_Sz then
         if Src_Signed then
            case Src_Sz is
               when 1 =>
                  IO.Put_Line (F, "    sxtb    "
                    & (if Tgt_Sz >= 8 then Xreg else Wreg) & ", " & Wreg);
               when 2 =>
                  IO.Put_Line (F, "    sxth    "
                    & (if Tgt_Sz >= 8 then Xreg else Wreg) & ", " & Wreg);
               when others =>  --  4 -> 8
                  IO.Put_Line (F, "    sxtw    " & Xreg & ", " & Wreg);
            end case;
         else
            case Src_Sz is
               when 1 => IO.Put_Line (F, "    uxtb    " & Wreg & ", " & Wreg);
               when 2 => IO.Put_Line (F, "    uxth    " & Wreg & ", " & Wreg);
               when others =>  --  4 -> 8: writing Wreg zeroes the upper 32
                  IO.Put_Line (F, "    mov     " & Wreg & ", " & Wreg);
            end case;
         end if;
      else  --  Tgt_Sz < Src_Sz : truncate to the low bytes
         case Tgt_Sz is
            when 1 => IO.Put_Line (F, "    uxtb    " & Wreg & ", " & Wreg);
            when 2 => IO.Put_Line (F, "    uxth    " & Wreg & ", " & Wreg);
            when others =>  --  -> 4: writing Wreg zeroes the upper 32
               IO.Put_Line (F, "    mov     " & Wreg & ", " & Wreg);
         end case;
      end if;
   end Emit_Int_Conv;
