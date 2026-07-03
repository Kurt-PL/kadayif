separate (Kurt.Sema.Check)
   procedure Register_Borrow (Name : String; Init : Expr_Access) is
   begin
      if Init = null or else Init.Kind /= E_Ref
        or else Init.Rf_Place.Kind /= E_Path
        or else Natural (Init.Rf_Place.Segments.Length) /= 1
      then
         return;
      end if;
      declare
         Place : constant String :=
           SU.To_String (Init.Rf_Place.Segments.Last_Element);
         St    : Kurt.Borrow.Perm_State;
         Tr    : Boolean;
      begin
         Borrow_State (Init.Rf_Sigil, Init.Rf_Store, St, Tr);
         if not Tr then
            return;
         end if;
         --  §8.3 Constraint: a new reference to a place already held by a
         --  `$T` at Assert_Excl provably aliases the exclusive reference.
         if Kurt.Borrow.Has_Asserted_Excl (Borrows, Place) then
            Error ("reference to '" & Place & "' aliases an exclusive "
                   & "'$' reference that has asserted exclusivity "
                   & "(spec 8.3)");
         end if;
         declare
            Ignore : constant Kurt.Borrow.Node_Id :=
              Kurt.Borrow.Create
                (Borrows, Referent => Place, Bound_To => Name,
                 State => St, Scope_Len => Natural (Scope.Length));
            pragma Unreferenced (Ignore);
         begin
            null;
         end;
      end;
   end Register_Borrow;
