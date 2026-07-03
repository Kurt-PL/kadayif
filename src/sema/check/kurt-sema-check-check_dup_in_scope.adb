separate (Kurt.Sema.Check)
   procedure Check_Dup_In_Scope (Name : SU.Unbounded_String) is
   begin
      for I in Block_Base + 1 .. Natural (Scope.Length) loop
         if SU.To_String (Scope.Element (I).Name) = SU.To_String (Name) then
            Error ("'" & SU.To_String (Name) & "' is already declared in "
                   & "this scope (spec 5.17)");
            return;
         end if;
      end loop;
   end Check_Dup_In_Scope;
