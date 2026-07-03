separate (Kurt.Layout)
   function Enum_Align (Name : String) return Natural is
      D : Enum_Decl;
      --  A void discriminant (width 0) contributes no alignment.
      A : Natural := Natural'Max (1, Enum_Disc_Size (Name));
   begin
      if Find_Enum (Name, D) then
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
      return A;
   end Enum_Align;
