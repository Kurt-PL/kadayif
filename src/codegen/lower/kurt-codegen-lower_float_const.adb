separate (Kurt.Codegen)
   procedure Lower_Float_Const
     (F : IO.File_Type; D_Reg : Natural; Value : Long_Float; Bytes : Natural)
   is
      use Interfaces;
      function To_U64 is new Ada.Unchecked_Conversion (Long_Float, Unsigned_64);
      function To_U32 is new Ada.Unchecked_Conversion (Float, Unsigned_32);
   begin
      if Bytes = 4 then
         Lower_Bits_64
           (F, 12, Unsigned_64 (To_U32 (Float (Value))));
         IO.Put_Line (F, "    fmov    s" & Img (D_Reg) & ", w12");
      else
         Lower_Bits_64 (F, 12, To_U64 (Value));
         IO.Put_Line (F, "    fmov    d" & Img (D_Reg) & ", x12");
      end if;
   end Lower_Float_Const;
