separate (Kurt.Parser.Parse_Primary)
   function Prim_Match return Expr_Access is
   begin
            --  §7: match scrut { pattern = expr, ... }
            --  Bootstrap: expression-bodied arms only.
            Advance (C);
            E := new Expr_Node (Kind => E_Match);
            --  Suppress struct-literal parsing so the following '{' opens
            --  the match body, not a struct literal.
            declare
               Saved : constant Boolean := C.No_Struct_Lit;
            begin
               C.No_Struct_Lit := True;
               E.M_Scrut := Parse_Expr (C);
               C.No_Struct_Lit := Saved;
            end;
            Expect (C, Punct_LBrace, "'{'");
            while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF
            loop
               declare
                  --  §5.10 parse a single pattern (no `|`). A leading integer
                  --  literal may continue into a range `lo..hi` / `lo..=hi`.
                  function Parse_One_Pattern return Pattern is
                     P : Pattern;
                  begin
                     case C.Cur.Kind is
                        when Tok_Hash_Wild =>
                           P.Kind := Pat_Wild;
                           Advance (C);
                        when Tok_String_Lit =>
                           --  §7.4.2 a string literal pattern `"abc"` is
                           --  shorthand for the fixed-length slice pattern
                           --  `[0x61, 0x62, 0x63]` (one `ui1` cell per byte);
                           --  expand it here, no execution-time comparison.
                           P.Kind := Pat_Slice;
                           declare
                              B : constant String :=
                                SU.To_String (C.Cur.Str_Bytes);
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
                           Expect (C, Punct_RBracket, "']' to close slice "
                                   & "pattern");
                        when Tok_Int_Lit =>
                           P.Int_V := C.Cur.Int_V;
                           Advance (C);
                           if C.Cur.Kind = Op_DotDot
                             or else C.Cur.Kind = Op_DotDotEq
                           then
                              --  §5.10 range pattern.
                              P.Kind := Pat_Range;
                              P.Range_Incl := C.Cur.Kind = Op_DotDotEq;
                              Advance (C);
                              if C.Cur.Kind /= Tok_Int_Lit then
                                 raise Syntax_Error with
                                   "range pattern needs an integer upper "
                                   & "bound at line"
                                   & Positive'Image (C.Cur.Line);
                              end if;
                              P.Range_Hi := C.Cur.Int_V;
                              Advance (C);
                           else
                              P.Kind := Pat_Int;
                           end if;
                        when Tok_Ident =>
                           --  §5.10 binding pattern `name # sub`: bind the
                           --  value to `name`, then match `sub`. The binding
                           --  name rides on the sub-pattern.
                           if Peek_Tok (C).Kind = Tok_Hash then
                              declare
                                 Nm : constant SU.Unbounded_String :=
                                   C.Cur.Lexeme;
                              begin
                                 Advance (C);   --  name
                                 Advance (C);   --  '#'
                                 P := Parse_One_Pattern;
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
                           --  Optional payload destructuring: bare positional
                           --  `{ a, b }` or named `field = binding` rename.
                           if C.Cur.Kind = Punct_LBrace then
                              Parse_Payload_Binds (C, P);
                           end if;
                        when others =>
                           raise Syntax_Error with
                             "expected match pattern, got " & Image (C.Cur)
                             & " at line" & Positive'Image (C.Cur.Line);
                     end case;
                     return P;
                  end Parse_One_Pattern;

                  --  §5.10 or-pattern `p | q | r`: collect the alternatives;
                  --  one arm is emitted per alternative below, all sharing the
                  --  same guard and body.
                  Alts  : Pattern_Vectors.Vector;
                  Guard : Expr_Access := null;
                  Body_E : Expr_Access;
               begin
                  Alts.Append (Parse_One_Pattern);
                  while C.Cur.Kind = Op_Bar loop
                     Advance (C);
                     Alts.Append (Parse_One_Pattern);
                  end loop;
                  --  §7.4 optional guard clause: `pattern if expr = body`.
                  if C.Cur.Kind = Kw_If then
                     Advance (C);
                     Guard := Parse_Expr (C);
                  end if;
                  Expect (C, Punct_Eq, "'=' in match arm");
                  Body_E := Parse_Expr (C);
                  for I in Alts.First_Index .. Alts.Last_Index loop
                     E.M_Arms.Append
                       ((Pat      => Alts.Element (I),
                         Guard    => Guard,
                         Arm_Body => Body_E));
                  end loop;
                  --  §3.2: comma separates expression-bodied arms.
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
               end;
            end loop;
            Expect (C, Punct_RBrace, "'}'");
            return E;

   end Prim_Match;
