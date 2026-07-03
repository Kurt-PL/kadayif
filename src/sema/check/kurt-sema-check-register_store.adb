separate (Kurt.Sema.Check)
   procedure Register_Store (Lhs : Expr_Access) is
   begin
      if Lhs.Kind /= E_Deref
        or else Lhs.D_Inner.Kind /= E_Path
        or else Natural (Lhs.D_Inner.Segments.Length) /= 1
      then
         return;
      end if;
      declare
         Name : constant String :=
           SU.To_String (Lhs.D_Inner.Segments.Last_Element);
         N    : constant Kurt.Borrow.Node_Id :=
           Kurt.Borrow.Of_Binding (Borrows, Name);
      begin
         if N = Kurt.Borrow.No_Node then
            return;
         end if;
         Kurt.Borrow.Record_Store (Borrows, N);
         if Kurt.Borrow.Is_Exclusive
              (Kurt.Borrow.State_Of (Borrows, N))
           and then Kurt.Borrow.Has_Live_Alias (Borrows, N)
         then
            Error ("store through exclusive '$' reference '" & Name
                   & "' whose referent is aliased by a live reference "
                   & "(spec 8.3)");
         end if;
         --  §8.3 the store is a foreign event for every other reference to
         --  the same place: apply the permission-state transition (after
         --  the alias check above, which is the mandatory diagnostic).
         --  An atomic store goes through an `atomic`/`guard` reference.
         Kurt.Borrow.Apply_Foreign_Store
           (Borrows, N,
            Atomic => Kurt.Borrow.State_Of (Borrows, N) =
                      Kurt.Borrow.Atomic_Ref);
      end;
   end Register_Store;
