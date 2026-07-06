separate (Kurt.Layout)
   function Group_Size
     (Fields : Kurt.Parser.Struct_Field_Vectors.Vector;
      Packed : Boolean := False) return Natural
   is
      Off : Natural := 0;
      Aln : Natural := 1;
   begin
      for I in Fields.First_Index .. Fields.Last_Index loop
         declare
            FT : constant Kurt.Parser.Type_Access := Fields.Element (I).Ty;
         begin
            --  §4.11.3 `with repr(packed)`: no inter-field padding and
            --  align 1 — every field sits at the next cell, unrounded.
            if not Packed then
               Off := Ceil (Off, Align_Of (FT));
            end if;
            Off := Off + Size_Of (FT);
            if not Packed then
               Aln := Natural'Max (Aln, Align_Of (FT));
            end if;
         end;
      end loop;
      if Off = 0 then
         return 0;
      end if;
      return Ceil (Off, Aln);
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Group_Size;
