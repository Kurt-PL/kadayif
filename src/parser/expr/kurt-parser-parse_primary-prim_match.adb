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
                  --  §5.10 or-pattern `p | q | r`: collect the alternatives;
                  --  one arm is emitted per alternative below, all sharing the
                  --  same guard and body.
                  Alts  : Pattern_Vectors.Vector;
                  Guard : Expr_Access := null;
                  Body_E : Expr_Access;
                  Is_Block_Body : Boolean;
               begin
                  Alts.Append (Parse_Match_Pattern (C));
                  while C.Cur.Kind = Op_Bar loop
                     Advance (C);
                     Alts.Append (Parse_Match_Pattern (C));
                  end loop;
                  --  §7.4 optional guard clause: `pattern if expr = body`.
                  if C.Cur.Kind = Kw_If then
                     Advance (C);
                     Guard := Parse_Expr (C);
                  end if;
                  Expect (C, Punct_Eq, "'=' in match arm");
                  --  §7.4: the grammar distinguishes `expression | block` for
                  --  the arm body; a bare `{` opening the body is the block
                  --  form (Parse_Primary routes an initial '{' to a block
                  --  expression), regardless of what it desugars to.
                  Is_Block_Body := C.Cur.Kind = Punct_LBrace;
                  Body_E := Parse_Expr (C);
                  for I in Alts.First_Index .. Alts.Last_Index loop
                     E.M_Arms.Append
                       ((Pat      => Alts.Element (I),
                         Guard    => Guard,
                         Arm_Body => Body_E));
                  end loop;
                  --  §7.4: a trailing comma after the last arm is always
                  --  optional. Between non-final arms, the comma is
                  --  mandatory when the arm body is an expression and
                  --  optional when the arm body is a block.
                  if C.Cur.Kind = Punct_Comma then
                     Advance (C);
                  elsif C.Cur.Kind = Punct_RBrace
                    or else C.Cur.Kind = Tok_EOF
                  then
                     null;   --  last arm: no comma required.
                  elsif not Is_Block_Body then
                     raise Syntax_Error with
                       "expected ',' between match arms (an "
                       & "expression-bodied arm requires a separating "
                       & "comma) (spec 7.4) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end;
            end loop;
            Expect (C, Punct_RBrace, "'}'");
            return E;

   end Prim_Match;
