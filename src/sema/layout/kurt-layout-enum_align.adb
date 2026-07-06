separate (Kurt.Layout)
   function Enum_Align (Name : String) return Natural is
      D : Enum_Decl;
      --  A void discriminant (width 0) contributes no alignment.
      A : Natural := Natural'Max (1, Enum_Disc_Size (Name));
   begin
      if Find_Enum (Name, D) then
         --  §4.11/§4.11.3: `with repr(packed)` forces the payload region's
         --  own alignment to 1, so it contributes nothing beyond the
         --  discriminant's alignment already in the baseline above.
         if not D.Repr_Packed then
            for I in D.Variants.First_Index .. D.Variants.Last_Index loop
               declare
                  P : constant Kurt.Parser.Struct_Field_Vectors.Vector :=
                    D.Variants.Element (I).Payload;
               begin
                  for J in P.First_Index .. P.Last_Index loop
                     A := Natural'Max (A, Align_Of (P.Element (J).Ty));
                  end loop;
               end;
            end loop;
         end if;
      end if;
      return A;
   end Enum_Align;
