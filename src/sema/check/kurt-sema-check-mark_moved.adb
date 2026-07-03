separate (Kurt.Sema.Check)
   procedure Mark_Moved (Name : String) is
   begin
      if not Is_Moved (Name) then
         Moved.Append
           ((Name  => SU.To_Unbounded_String (Name),
             Depth => Natural (Scope.Length)));
      end if;
   end Mark_Moved;
