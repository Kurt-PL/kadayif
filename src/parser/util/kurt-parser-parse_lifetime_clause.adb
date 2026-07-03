separate (Kurt.Parser)
   procedure Parse_Lifetime_Clause (C : in out Cursor) is
      procedure Parse_Chain is
      begin
         if C.Cur.Kind /= Tok_Label then
            raise Syntax_Error with
              "expected a lifetime ('name) in a 'with lifetime' chain at "
              & "line" & Positive'Image (C.Cur.Line);
         end if;
         while C.Cur.Kind = Tok_Label loop
            Advance (C);
         end loop;
      end Parse_Chain;
   begin
      Advance (C);   --  'with'
      Advance (C);   --  'lifetime'
      if C.Cur.Kind = Punct_LBrace then
         Advance (C);
         loop
            Parse_Chain;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);                            --  ','
            exit when C.Cur.Kind = Punct_RBrace;    --  trailing comma
         end loop;
         Expect (C, Punct_RBrace, "'}' to close 'with lifetime'");
      else
         Parse_Chain;
      end if;
   end Parse_Lifetime_Clause;
