separate (Kurt.Layout)
   function Variant_Field_Offset
     (Enum_Name, Variant : String; Field_No : Positive) return Natural
   is
      V   : Enum_Variant;
      Off : Natural := 0;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         raise Layout_Error with
           "unknown variant '" & Variant & "' of '" & Enum_Name & "'";
      end if;
      for K in V.Payload.First_Index .. V.Payload.Last_Index loop
         declare
            FT : constant Kurt.Parser.Type_Access := V.Payload.Element (K).Ty;
         begin
            Off := Ceil (Off, Align_Of (FT));
            if K = V.Payload.First_Index + (Field_No - 1) then
               return Payload_Region_Offset (Enum_Name) + Off;
            end if;
            Off := Off + Size_Of (FT);
         end;
      end loop;
      raise Layout_Error with "payload field index out of range";
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Variant_Field_Offset;
