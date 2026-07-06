separate (Kurt.Layout)
   function Variant_Value
     (Enum_Name, Variant : String) return Long_Long_Integer
   is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            --  The result is the *stored* discriminant bit pattern,
            --  zero-extended to 64 bits: every consumer (construction
            --  stores, match/contract compares) operates on the
            --  discriminant width with zero-extended loads, so negative
            --  values are masked here once (§4.11.3).
            declare
               DS : constant Cell_Count := Enum_Disc_Size (Enum_Name);
               V  : constant Long_Long_Integer :=
                 D.Variants.Element (I).Value;
            begin
               case DS is
                  when 0      => return 0;
                  when 1 | 2 | 4 =>
                     return V mod (2 ** Natural (8 * DS));
                  when others => return V;
               end case;
            end;
         end if;
      end loop;
      raise Layout_Error with
        "enum '" & Enum_Name & "' has no variant '" & Variant & "'";
   end Variant_Value;
