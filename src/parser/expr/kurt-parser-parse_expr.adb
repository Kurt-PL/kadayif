separate (Kurt.Parser)
   function Parse_Expr (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Binary (C, 0);
   begin
      --  §3.7: `..`/`..=` are pattern-only tokens — no value-level range
      --  type exists, so a range in expression position is ill-formed.
      if C.Cur.Kind = Op_DotDot or else C.Cur.Kind = Op_DotDotEq then
         raise Syntax_Error with
           "`..`/`..=` form patterns only; no range value exists (§3.7) "
           & "at line" & Positive'Image (C.Cur.Line);
      end if;
      if C.Cur.Kind = Op_EqCas or else C.Cur.Kind = Op_NeCas then
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_CAS);
         begin
            Next.CAS_Ne := C.Cur.Kind = Op_NeCas;
            Advance (C);
            Next.CAS_Tgt := E;
            Next.CAS_Exp := Parse_Binary (C, 0);
            Expect (C, Kw_Then, "'then' in compare-and-swap (spec 8.7)");
            Next.CAS_New := Parse_Binary (C, 0);
            E := Next;
         end;
      end if;
      return E;
   end Parse_Expr;
