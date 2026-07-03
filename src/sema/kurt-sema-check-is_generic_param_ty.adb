separate (Kurt.Sema.Check)
   function Is_Generic_Param_Ty (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
         if SU.To_String (Cur_Generics.Element (I).Name)
              = SU.To_String (T.Name)
         then
            return True;
         end if;
      end loop;
      return False;
   end Is_Generic_Param_Ty;
