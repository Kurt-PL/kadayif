separate (Kurt.Layout)
   function Implicit_Wild_Value
     (Enum_Name : String) return Long_Long_Integer
   is
      D : Enum_Decl;
      Candidate : Long_Long_Integer := 0;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      --  Smallest non-negative value not used by a declared variant.
      loop
         declare
            Used : Boolean := False;
         begin
            for I in D.Variants.First_Index .. D.Variants.Last_Index loop
               if D.Variants.Element (I).Value = Candidate then
                  Used := True;
               end if;
            end loop;
            exit when not Used;
            Candidate := Candidate + 1;
         end;
      end loop;
      return Candidate;
   end Implicit_Wild_Value;
