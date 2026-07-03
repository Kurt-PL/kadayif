separate (Kurt.Parser)
   function Parse_Cond (C : in out Cursor) return Expr_Access is
      Saved : constant Boolean := C.No_Struct_Lit;
      R     : Expr_Access;
   begin
      C.No_Struct_Lit := True;
      R := Parse_Expr (C);
      C.No_Struct_Lit := Saved;
      return R;
   end Parse_Cond;
