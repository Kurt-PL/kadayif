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
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      D.Init := Parse_Expr (C);
      Expect (C, Punct_Semi, "';' after static declaration");
      return D;
   end Parse_Static_Decl;
