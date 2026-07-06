separate (Kurt.Layout)
   function Payload_Region_Offset (Name : String) return Cell_Count is
   begin
      return Ceil (Enum_Disc_Size (Name), Enum_Align (Name));
   end Payload_Region_Offset;
