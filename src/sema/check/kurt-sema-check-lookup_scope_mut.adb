separate (Kurt.Sema.Check)
   function Lookup_Scope_Mut
     (Name : String; Found : out Boolean) return Boolean is
   begin
      for I in reverse Scope.First_Index .. Scope.Last_Index loop
         if SU.To_String (Scope.Element (I).Name) = Name then
            Found := True;
            return Scope.Element (I).Is_Mut;
         end if;
      end loop;
      Found := False;
      return False;
   end Lookup_Scope_Mut;
