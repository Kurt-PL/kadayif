separate (Kurt.Layout)
   function Enum_Disc_Size (Name : String) return Natural is
      D   : Enum_Decl;
      Min : Long_Long_Integer := 0;
      Max : Long_Long_Integer := 0;
   begin
      if not Find_Enum (Name, D) then
         return 1;
      end if;
      if D.Discrim_Ty /= null then
         return Size_Of (D.Discrim_Ty);
      end if;
      declare
         Has_Canon : Boolean := False;
      begin
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            if D.Variants.Element (I).Wild_Canon then
               Has_Canon := True;
            end if;
         end loop;
         --  §4.11.2: void only when <= 1 variant, no `#wild#(V)` canonical
         --  value, no explicit discriminant value, and no `with discrim(T)`
         --  (the discrim(T) case returned above).
         if Natural (D.Variants.Length) <= 1
           and then not Has_Canon
           and then not D.Any_Explicit
         then
            return 0;
         end if;
      end;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         Min := Long_Long_Integer'Min (Min, D.Variants.Element (I).Value);
         Max := Long_Long_Integer'Max (Max, D.Variants.Element (I).Value);
      end loop;
      if Min < 0 then
         if Min >= -128 and then Max <= 127 then
            return 1;
         elsif Min >= -32768 and then Max <= 32767 then
            return 2;
         elsif Min >= -(2 ** 31) and then Max <= 2 ** 31 - 1 then
            return 4;
         else
            return 8;
         end if;
      elsif Max <= 255 then
         return 1;
      elsif Max <= 65535 then
         return 2;
      elsif Max <= 4294967295 then
         return 4;
      else
         return 8;
      end if;
   end Enum_Disc_Size;
