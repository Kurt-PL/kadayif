separate (Kurt.Parser)
   function Parse_Const_Decl (C : in out Cursor) return Const_Decl is
      D : Const_Decl;
   begin
      Expect (C, Kw_Const, "'const'");
      D.Name := Take_Ident (C, "const name");
      Expect (C, Punct_Colon, "':' (const type annotation is mandatory, "
              & "spec 5.3)");
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      --  §6.10.2: a `const` initializer is implicitly `xlatime` -- the same
      --  operations are permitted as in an explicit `xlatime { ... }` block.
      --  Nested `if xlatime`/`if !xlatime` therefore see `xlatime` as true
      --  here, exactly as within an explicit block.
      C.Xlatime_Depth := C.Xlatime_Depth + 1;
      D.Init := Parse_Expr (C);
      C.Xlatime_Depth := C.Xlatime_Depth - 1;
      Expect (C, Punct_Semi, "';' after const declaration");
      return D;
   end Parse_Const_Decl;
