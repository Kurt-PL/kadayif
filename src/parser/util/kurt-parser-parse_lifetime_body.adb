separate (Kurt.Parser)
   procedure Parse_Lifetime_Body
     (C : in out Cursor; Chains : in out Lifetime_Chain_Vectors.Vector)
   is
      procedure Parse_Chain is
         Seg : Path_Segments.Vector;
      begin
         if C.Cur.Kind /= Tok_Label then
            raise Syntax_Error with
              "expected a lifetime ('name) in a 'with lifetime' chain at "
              & "line" & Positive'Image (C.Cur.Line);
         end if;
         while C.Cur.Kind = Tok_Label loop
            Seg.Append (C.Cur.Lexeme);
            Advance (C);
         end loop;
         Chains.Append (Seg);
      end Parse_Chain;
   begin
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
   end Parse_Lifetime_Body;
