separate (Kurt.Parser)
   procedure Parse_Lifetime_Clause (C : in out Cursor) is
      --  §8.4.3 subroutine form: chains are validated for shape only; a
      --  subroutine's lifetimes are erased (no run-time representation)
      --  and outlives-checking is out of scope for the bootstrap.
      Discard : Lifetime_Chain_Vectors.Vector;
   begin
      Advance (C);   --  'with'
      Advance (C);   --  'lifetime'
      Parse_Lifetime_Body (C, Discard);
   end Parse_Lifetime_Clause;
