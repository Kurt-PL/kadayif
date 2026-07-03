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
   end Check_Block;
