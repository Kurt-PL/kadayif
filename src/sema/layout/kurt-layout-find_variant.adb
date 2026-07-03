separate (Kurt.Layout)
   function Find_Variant
     (Enum_Name, Variant : String; Found : out Enum_Variant) return Boolean
   is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            Found := D.Variants.Element (I);
            return True;
         end if;
      end loop;
      return False;
   end Find_Variant;
