separate (Kurt.Sema.Check)
   function Init_Lookup
     (Name : String; Idx : out Natural) return Boolean
   is
   begin
      for I in reverse Init_States.First_Index .. Init_States.Last_Index
      loop
         if SU.To_String (Init_States.Element (I).Name) = Name then
            Idx := I;
            return True;
         end if;
      end loop;
      Idx := 0;
      return False;
   end Init_Lookup;
