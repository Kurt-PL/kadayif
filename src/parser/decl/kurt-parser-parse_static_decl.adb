separate (Kurt.Parser)
   function Parse_Static_Decl (C : in out Cursor) return Static_Decl is
      D : Static_Decl;
   begin
      Advance (C);   --  consume the `static` identifier-word
      if C.Cur.Kind = Kw_Mut then
         D.Is_Mut := True;
         Advance (C);
      end if;
      D.Name := Take_Ident (C, "static name");
      Expect (C, Punct_Colon, "':' (static type annotation)");
      --  §4.12: a `?` annotation is equivalent to an omitted one -- the
      --  type is synthesised from the initialiser.
      if C.Cur.Kind = Op_Question then
         Advance (C);
      else
         D.Ty := Parse_Type (C);
      end if;
      Expect (C, Punct_Eq, "'='");
      --  §6.10.2: a `static`/`static mut` initializer is implicitly
      --  `xlatime`, exactly like a `const` initializer -- see
      --  Parse_Const_Decl.
      C.Xlatime_Depth := C.Xlatime_Depth + 1;
      D.Init := Parse_Expr (C);
      C.Xlatime_Depth := C.Xlatime_Depth - 1;
      Expect (C, Punct_Semi, "';' after static declaration");
      return D;
   end Parse_Static_Decl;
