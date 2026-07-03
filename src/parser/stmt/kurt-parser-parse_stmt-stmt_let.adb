separate (Kurt.Parser.Parse_Stmt)
   function Stmt_Let return Stmt_Access is
   begin
            --  §5.2 binding  OR  §7 contract extraction  OR  §4.7 tuple
            --  destructuring:
            --      let v = expr ;
            --      let v <- expr else [err] { ... } ;
            --      let .{ a, b } = expr ;
            Advance (C);
            if C.Cur.Kind = Punct_Dot then
               Advance (C);
               Expect (C, Punct_LBrace, "'{' after '.' in destructuring let");
               S := new Stmt_Node (Kind => S_Let);
               loop
                  S.L_Tuple_Names.Append
                    (Take_Ident (C, "destructuring binding name"));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
               end loop;
               Expect (C, Punct_RBrace, "'}' to close destructuring pattern");
               Expect (C, Punct_Eq, "'='");
               S.L_Init := Parse_Expr (C);
               Expect (C, Punct_Semi, "';'");
               return S;
            end if;
            --  §5.2.1 refutable let-else: a variant pattern (the head ident
            --  is followed by `::` or `{`) destructured against a scrutinee,
            --  with a diverging `else` on mismatch.
            if C.Cur.Kind = Tok_Ident
              and then (Peek_Tok (C).Kind = Punct_ColonColon
                        or else Peek_Tok (C).Kind = Punct_LBrace)
            then
               S := new Stmt_Node (Kind => S_Let);
               S.L_Is_Refut := True;
               S.L_Refut_Pat.Kind := Pat_Variant;
               S.L_Refut_Pat.Path.Append
                 (Take_Ident (C, "enum name in let-else pattern"));
               while C.Cur.Kind = Punct_ColonColon loop
                  Advance (C);
                  S.L_Refut_Pat.Path.Append (Take_Ident (C, "variant name"));
               end loop;
               if C.Cur.Kind = Punct_LBrace then
                  Parse_Payload_Binds (C, S.L_Refut_Pat);
               end if;
               Expect (C, Punct_Eq, "'=' in let-else");
               S.L_Init := Parse_Expr (C);
               Expect (C, Kw_Else, "'else' in refutable let (spec 5.2.1)");
               Parse_Block_Stmts (C, S.L_Else);
               Expect (C, Punct_Semi, "';'");
               return S;
            end if;
            declare
               Name : constant SU.Unbounded_String :=
                 Take_Ident (C, "let binding name");
            begin
               if C.Cur.Kind = Punct_LArrow then
                  --  Extraction: bind the success payload to `v`, or run
                  --  the (diverging) else block with the failure payload.
                  Advance (C);
                  S := new Stmt_Node (Kind => S_Extract);
                  S.X_Bind := Name;
                  S.X_Expr := Parse_Expr (C);
                  Expect (C, Kw_Else, "'else'");
                  if C.Cur.Kind = Tok_Ident then
                     S.X_Err := Take_Ident (C, "failure binding");
                  end if;
                  Parse_Block_Stmts (C, S.X_Else);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               else
                  S := new Stmt_Node (Kind => S_Let);
                  S.L_Name := Name;
                  if C.Cur.Kind = Punct_Colon then
                     Advance (C);
                     --  §4.12: a `?` annotation is equivalent to an omitted
                     --  one — the type is synthesised from the initializer.
                     if C.Cur.Kind = Op_Question then
                        Advance (C);
                     else
                        S.L_Ty := Parse_Type (C);
                     end if;
                  end if;
                  Expect (C, Punct_Eq, "'='");
                  S.L_Init := Parse_Expr (C);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               end if;
            end;

   end Stmt_Let;
