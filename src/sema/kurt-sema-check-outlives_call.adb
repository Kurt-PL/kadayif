separate (Kurt.Sema.Check)
   function Outlives_Call (Place : String) return Boolean is
      Dummy : Boolean;
   begin
      if Find_Static_Decl (Place, Dummy) then
         return True;
      end if;
      for I in U.Consts.First_Index .. U.Consts.Last_Index loop
         if SU.To_String (U.Consts.Element (I).Name) = Place then
            return True;
         end if;
      end loop;
      return False;
   end Outlives_Call;
