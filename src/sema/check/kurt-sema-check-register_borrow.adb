separate (Kurt.Sema.Check)
   procedure Register_Borrow (Name : String; Init : Expr_Access) is
      --  §8.3: the canonical dotted path of a place expression -- a bare
      --  root binding ("p"), or a field-projection chain rooted at one
      --  ("p.a", "p.a.b", ...). Returns "" for any other place shape (a
      --  deref, an indexed/computed place, etc.) -- out of scope here (no
      --  reborrow trees, no cast tracking); the caller bails on "".
      function Canonical_Place (E : Expr_Access) return String is
      begin
         if E = null then
            return "";
         elsif E.Kind = E_Path and then Natural (E.Segments.Length) = 1 then
            return SU.To_String (E.Segments.Last_Element);
         elsif E.Kind = E_Field then
            declare
               Base : constant String := Canonical_Place (E.F_Recv);
            begin
               if Base = "" then
                  return "";
               end if;
               return Base & "." & SU.To_String (E.F_Name);
            end;
         else
            return "";
         end if;
      end Canonical_Place;
   begin
      if Init = null or else Init.Kind /= E_Ref then
         return;
      end if;
      declare
         Place : constant String := Canonical_Place (Init.Rf_Place);
         St    : Kurt.Borrow.Perm_State;
         Tr    : Boolean;
      begin
         if Place = "" then
            return;
         end if;
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
