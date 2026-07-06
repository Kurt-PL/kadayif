separate (Kurt.Parser.Parse_Stmt)
   function Stmt_Const return Stmt_Access is
   begin
            --  §5.3 `const NAME: T = expr;` in statement position. Unlike
            --  `let`, the type annotation is mandatory (spec 5.3: "The
            --  type annotation is mandatory") and there is no
            --  destructuring / refutable-pattern / bare-`?`-inferred form.
            Advance (C);   --  'const'
            S := new Stmt_Node (Kind => S_Let);
            S.L_Is_Const := True;
            S.L_Name := Take_Ident (C, "const name");
            Expect (C, Punct_Colon,
              "':' (const type annotation is mandatory, spec 5.3)");
            S.L_Ty := Parse_Type (C);
            Expect (C, Punct_Eq, "'='");
            --  §6.10.2: a `const` initializer is implicitly `xlatime`,
            --  exactly like a top-level `const` (Kurt.Parser.Parse_Const_Decl)
            --  -- nested `if xlatime`/`if !xlatime` see `xlatime` as true.
            C.Xlatime_Depth := C.Xlatime_Depth + 1;
            S.L_Init := Parse_Expr (C);
            C.Xlatime_Depth := C.Xlatime_Depth - 1;
            Expect (C, Punct_Semi, "';' after const declaration");
            return S;

   end Stmt_Const;
