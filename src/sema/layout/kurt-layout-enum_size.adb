separate (Kurt.Layout)
   function Enum_Size (Name : String) return Natural is
      D      : Enum_Decl;
      Max_PL : Natural := 0;
   begin
      if Find_Enum (Name, D) then
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            Max_PL := Natural'Max
              (Max_PL, Group_Size (D.Variants.Element (I).Payload));
         end loop;
      end if;
      if Max_PL = 0 then
         return Enum_Disc_Size (Name);
      end if;
      return Ceil (Payload_Region_Offset (Name) + Max_PL, Enum_Align (Name));
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Enum_Size;
