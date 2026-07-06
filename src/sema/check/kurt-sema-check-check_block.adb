separate (Kurt.Sema.Check)
   procedure Check_Block (Stmts : Stmt_Vectors.Vector) is
      Entry_Len  : constant Natural := Natural (Scope.Length);
      --  §5.17: this block opens a fresh scope. Names already in Scope
      --  (params, outer-block locals, and any pattern bindings appended
      --  just before this call) belong to enclosing scopes and may be
      --  shadowed; only declarations made within this block collide.
      Saved_Base : constant Natural := Block_Base;
   begin
      Block_Base := Entry_Len;
      for I in Stmts.First_Index .. Stmts.Last_Index loop
         Check_Stmt (Stmts.Element (I));
      end loop;
      Block_Base := Saved_Base;
      --  §8.2 liveness: references bound inside this block lapse at its
      --  end (their bindings leave scope).
      Kurt.Borrow.Kill_Above (Borrows, Entry_Len);
      --  §8.8.2: moved-binding records for this block's bindings lapse too.
      for I in reverse 1 .. Natural (Moved.Length) loop
         if Moved.Element (I).Depth > Entry_Len then
            Moved.Delete (I);
         end if;
      end loop;
      --  §5.2/§8.4: a deferred-init binding scoped to this block is going
      --  out of scope. Uninit is fine (destructor statically skipped, if
      --  any); Init is fine (destructor runs normally). Maybe -- assigned
      --  on some but not all live paths -- is a problem only when the
      --  type has a destructor: the obligation to run it, or not, cannot
      --  be proven either way -- the spec's "proof failure" model (spec
      --  5.2's destruction-obligation clause). The tracking entry cannot
      --  escape past this block either way.
      for I in reverse 1 .. Natural (Init_States.Length) loop
         if Init_States.Element (I).Depth > Entry_Len then
            if Init_States.Element (I).State = St_Maybe
              and then Satisfies_Destruct (Init_States.Element (I).Ty)
            then
               Error ("binding '"
                      & SU.To_String (Init_States.Element (I).Name)
                      & "' is initialized on some but not all paths "
                      & "reaching the end of its scope, and its type has "
                      & "a destructor -- the destruction obligation "
                      & "cannot be proven either way (spec 5.2/8.4)");
            end if;
            Init_States.Delete (I);
         end if;
      end loop;
   end Check_Block;
