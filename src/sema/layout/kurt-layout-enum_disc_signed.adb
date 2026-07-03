separate (Kurt.Layout)
   function Enum_Disc_Signed (Name : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Name, D) then
         return False;
      end if;
      if D.Discrim_Ty /= null then
         if D.Discrim_Ty.Kind = T_Named then
            declare
               N : constant String := SU.To_String (D.Discrim_Ty.Name);
            begin
               return (N'Length >= 2
                         and then N (N'First) = 's'
                         and then N (N'First + 1) = 'i')
                   or else N = "saddr";
            end;
         end if;
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Value < 0 then
            return True;
         end if;
      end loop;
      return False;
   end Enum_Disc_Signed;
