separate (Kurt.Sema.Check)
   function Find_Static_Decl
     (Name : String; Is_Mut : out Boolean) return Boolean is
   begin
      for I in U.Statics.First_Index .. U.Statics.Last_Index loop
         if SU.To_String (U.Statics.Element (I).Name) = Name then
            Is_Mut := U.Statics.Element (I).Is_Mut;
            return True;
         end if;
      end loop;
      Is_Mut := False;
      return False;
   end Find_Static_Decl;
