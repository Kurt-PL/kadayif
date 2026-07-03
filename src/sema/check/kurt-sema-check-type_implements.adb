separate (Kurt.Sema.Check)
   function Type_Implements (Ty_Name, Tr_Name : String) return Boolean is
   begin
      for I in U.Trait_Impls.First_Index ..
               U.Trait_Impls.Last_Index
      loop
         if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
           and then SU.To_String
             (U.Trait_Impls.Element (I).Trait_Name) = Tr_Name
         then
            return True;
         end if;
      end loop;
      return False;
   end Type_Implements;
