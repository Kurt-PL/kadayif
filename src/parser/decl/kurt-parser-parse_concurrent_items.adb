separate (Kurt.Parser)
   procedure Parse_Concurrent_Items
     (C : in out Cursor;
      Transfer, No_Transfer, Reference, No_Reference : in out Boolean)
   is
      procedure One_Item is
         Neg : Boolean := False;
      begin
         if C.Cur.Kind = Op_Bang then
            Neg := True;
            Advance (C);
         end if;
         if C.Cur.Kind /= Tok_Ident then
            raise Syntax_Error with
              "expected 'transfer' or 'reference' in a 'with concurrent' "
              & "clause at line" & Positive'Image (C.Cur.Line);
         end if;
         declare
            Item : constant String := SU.To_String (C.Cur.Lexeme);
         begin
            Advance (C);
            if Item = "transfer" then
               if Neg then No_Transfer := True; else Transfer := True; end if;
            elsif Item = "reference" then
               if Neg then No_Reference := True; else Reference := True; end if;
            else
               raise Syntax_Error with
                 "a 'with concurrent' item shall be 'transfer' or "
                 & "'reference' (spec 8.10) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
         end;
      end One_Item;
   begin
      if C.Cur.Kind = Punct_LBrace then
         Advance (C);
         loop
            One_Item;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);                            --  ','
            exit when C.Cur.Kind = Punct_RBrace;    --  trailing comma
         end loop;
         Expect (C, Punct_RBrace, "'}' to close 'with concurrent'");
      else
         One_Item;
      end if;
      --  §8.10.1: a positive and its own negation shall not both appear.
      if Transfer and then No_Transfer then
         raise Syntax_Error with
           "'with concurrent' declares both 'transfer' and '!transfer' "
           & "(spec 8.10.1) at line" & Positive'Image (C.Cur.Line);
      end if;
      if Reference and then No_Reference then
         raise Syntax_Error with
           "'with concurrent' declares both 'reference' and '!reference' "
           & "(spec 8.10.1) at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Concurrent_Items;
