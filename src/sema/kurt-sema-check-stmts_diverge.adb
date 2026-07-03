separate (Kurt.Sema.Check)
   function Stmts_Diverge (V : Stmt_Vectors.Vector) return Boolean is
   begin
      --  Once a statement diverges, the rest of the list is
      --  unreachable, so the list diverges from that point.
      for I in V.First_Index .. V.Last_Index loop
         if Stmt_Diverges (V.Element (I)) then
            return True;
         end if;
      end loop;
      return False;
   end Stmts_Diverge;
