separate (Kurt.Sema.Check)
   function Is_Trait_Name (Nm : String) return Boolean is
   begin
      for I in U.Traits.First_Index .. U.Traits.Last_Index loop
         if SU.To_String (U.Traits.Element (I).Name) = Nm then
            return True;
         end if;
      end loop;
      return False;
   end Is_Trait_Name;
