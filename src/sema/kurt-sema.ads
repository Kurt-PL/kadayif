--  Kadaif semantic analysis (bootstrap).
--
--  Implements the two-phase model of §10.2:
--    Phase 1 — collect every fn / @dyn-prototype signature.
--    Phase 2 — walk each fn body, infer a type for every expression,
--              attach it to Expr_Node.Sem_Ty, and check the constraints
--              this bootstrap understands.
--
--  Type inference is light bidirectional checking: a synthesised type
--  flows up, while an "expected" type flows down so that unsuffixed
--  integer literals (§3.4.1) take the surrounding type, falling back to
--  `saddr` when no integer context constrains them.
--
--  Checks performed:
--    * if-expression branches must have the same type (§7.1)
--    * `*` operand must be a reference (§6 dereference)
--    * calls must name a known subroutine
--    * identifiers must resolve to a binding in scope
--
--  Deferred: full assignability, generics, traits, contract flow,
--  borrow/lifetime, airside permission checking.

with Kurt.Parser;

package Kurt.Sema is

   --  Analyse the unit in place, attaching Sem_Ty to expressions.
   --  Diagnostics are written to standard error; Error_Count returns the
   --  number of constraint violations found (0 == success).
   procedure Check
     (U           : in out Kurt.Parser.Translation_Unit;
      Error_Count : out Natural);

end Kurt.Sema;
