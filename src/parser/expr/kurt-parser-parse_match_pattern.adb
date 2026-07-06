separate (Kurt.Parser)
   function Parse_Match_Pattern (C : in out Cursor) return Pattern is
      --  §5.10 parse a single pattern (no `|`). A leading integer literal
      --  may continue into a range `lo..hi` / `lo..=hi`. Recurses (via
      --  Parse_Payload_Binds) for item(a) nested payload sub-patterns
      --  (spec 7.4) and for the top-level `name # sub` binding form.
      P : Pattern;
   begin
      case C.Cur.Kind is
         when Tok_Hash_Wild =>
            P.Kind := Pat_Wild;
            Advance (C);
            --  §5.10.1 `#wild#(name)`: bind the raw representation of the
            --  matched value to `name` as a `&[ui1]` cell slice (the bare
            --  form discards it).
            if C.Cur.Kind = Punct_LParen then
               Advance (C);
               P.Wild_Bind := Take_Ident (C, "#wild#(name) binding");
               Expect (C, Punct_RParen, "')' to close #wild#(name)");
            end if;
         when Punct_Dot =>
            --  §5.10.1 anonymous-struct (tuple) pattern `.{ p0, p1, ... }`:
            --  positional decomposition; `...` is not permitted. Each
            --  position is a plain binding, a `name # sub` binding, or a
            --  full nested sub-pattern.
            P.Kind := Pat_Tuple;
            Advance (C);   --  '.'
            Expect (C, Punct_LBrace, "'{' of tuple pattern");
            if C.Cur.Kind /= Punct_RBrace then
               loop
                  if C.Cur.Kind = Op_Ellipsis then
                     raise Syntax_Error with
                       "`...` is not permitted in a tuple pattern "
                       & "(spec 5.10.1) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  if C.Cur.Kind = Tok_Ident
                    and then Peek_Tok (C).Kind = Tok_Hash
                  then
                     --  `name # sub`: bind and test.
                     P.Bindings.Append (C.Cur.Lexeme);
                     P.Bind_Fields.Append (SU.Null_Unbounded_String);
                     Advance (C);   --  name
                     Advance (C);   --  '#'
                     P.Sub_Pats.Append
                       (new Pattern'(Parse_Match_Pattern (C)));
                  elsif C.Cur.Kind = Tok_Ident
                    and then Peek_Tok (C).Kind /= Punct_ColonColon
                    and then Peek_Tok (C).Kind /= Punct_LBrace
                  then
                     --  Plain positional binding.
                     P.Bindings.Append (C.Cur.Lexeme);
                     P.Bind_Fields.Append (SU.Null_Unbounded_String);
                     P.Sub_Pats.Append (null);
                     Advance (C);
                  else
                     --  Full nested sub-pattern in this position.
                     P.Bindings.Append (SU.Null_Unbounded_String);
                     P.Bind_Fields.Append (SU.Null_Unbounded_String);
                     P.Sub_Pats.Append
                       (new Pattern'(Parse_Match_Pattern (C)));
                  end if;
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;
               end loop;
            end if;
            Expect (C, Punct_RBrace, "'}' to close tuple pattern");
         when Tok_String_Lit =>
            --  §7.4.2 a string literal pattern `"abc"` is shorthand for the
            --  fixed-length slice pattern `[0x61, 0x62, 0x63]` (one `ui1`
            --  cell per byte); expand it here, no execution-time comparison.
            P.Kind := Pat_Slice;
            P.From_String := True;
            declare
               B : constant String := SU.To_String (C.Cur.Str_Bytes);
            begin
               for I in B'Range loop
                  P.Slice_Elems.Append
                    ((Kind  => SE_Int,
                      Int_V => Character'Pos (B (I)),
                      others => <>));
               end loop;
            end;
            Advance (C);
         when Punct_LBracket =>
            --  §7.4.2 slice pattern `[e0, e1, ...]`.
            P.Kind := Pat_Slice;
            Advance (C);
            if C.Cur.Kind /= Punct_RBracket then
               loop
                  declare
                     SE : Slice_Elem;
                  begin
                     if C.Cur.Kind = Op_Ellipsis then
                        SE.Kind := SE_Rest;
                        Advance (C);
                     elsif C.Cur.Kind = Tok_Hash_Wild then
                        SE.Kind := SE_Wild;
                        Advance (C);
                     elsif C.Cur.Kind = Tok_Int_Lit then
                        SE.Kind  := SE_Int;
                        SE.Int_V := C.Cur.Int_V;
                        Advance (C);
                     elsif C.Cur.Kind = Tok_Ident then
                        SE.Kind := SE_Bind;
                        SE.Name := C.Cur.Lexeme;
                        Advance (C);
                     else
                        raise Syntax_Error with
                          "bad slice-pattern element at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                     P.Slice_Elems.Append (SE);
                  end;
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBracket;
               end loop;
            end if;
            Expect (C, Punct_RBracket, "']' to close slice pattern");
         when Tok_Int_Lit =>
            P.Int_V := C.Cur.Int_V;
            Advance (C);
            if C.Cur.Kind = Op_DotDot or else C.Cur.Kind = Op_DotDotEq then
               --  §5.10 range pattern.
               P.Kind := Pat_Range;
               P.Range_Incl := C.Cur.Kind = Op_DotDotEq;
               Advance (C);
               if C.Cur.Kind /= Tok_Int_Lit then
                  raise Syntax_Error with
                    "range pattern needs an integer upper bound at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               P.Range_Hi := C.Cur.Int_V;
               Advance (C);
            else
               P.Kind := Pat_Int;
            end if;
         when Tok_Ident =>
            --  §5.10 binding pattern `name # sub`: bind the value to
            --  `name`, then match `sub`. The binding name rides on the
            --  sub-pattern.
            if Peek_Tok (C).Kind = Tok_Hash then
               declare
                  Nm : constant SU.Unbounded_String := C.Cur.Lexeme;
               begin
                  Advance (C);   --  name
                  Advance (C);   --  '#'
                  P := Parse_Match_Pattern (C);
                  P.Bind_Name := Nm;
                  return P;
               end;
            end if;
            P.Kind := Pat_Variant;
            P.Path.Append (C.Cur.Lexeme);
            Advance (C);
            while C.Cur.Kind = Punct_ColonColon loop
               Advance (C);
               P.Path.Append (Take_Ident (C, "variant name"));
            end loop;
            --  Optional payload destructuring: bare positional `{ a, b }`
            --  or named `field = binding` rename.
            if C.Cur.Kind = Punct_LBrace then
               Parse_Payload_Binds (C, P);
            end if;
         when others =>
            raise Syntax_Error with
              "expected match pattern, got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
      end case;
      return P;
   end Parse_Match_Pattern;
