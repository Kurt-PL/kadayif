separate (Kurt.Layout)
   function Variant_Field_Offset
     (Enum_Name, Variant : String; Field_No : Positive) return Cell_Count
   is
      D      : Enum_Decl;
      V      : Enum_Variant;
      Off    : Cell_Count := 0;
      Packed : Boolean := False;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         raise Layout_Error with
           "unknown variant '" & Variant & "' of '" & Enum_Name & "'";
      end if;
      if Find_Enum (Enum_Name, D) then
         Packed := D.Repr_Packed;
      end if;
      for K in V.Payload.First_Index .. V.Payload.Last_Index loop
         declare
            FT : constant Kurt.Parser.Type_Access := V.Payload.Element (K).Ty;
         begin
            --  §4.11.3 `with repr(packed)`: no inter-field padding.
            if not Packed then
               Off := Ceil (Off, Align_Of (FT));
            end if;
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
