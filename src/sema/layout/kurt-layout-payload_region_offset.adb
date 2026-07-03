separate (Kurt.Layout)
   function Payload_Region_Offset (Name : String) return Natural is
   begin
      return Ceil (Enum_Disc_Size (Name), Enum_Align (Name));
   end Payload_Region_Offset;
