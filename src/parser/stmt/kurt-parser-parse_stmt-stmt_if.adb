separate (Kurt.Parser.Parse_Stmt)
   function Stmt_If return Stmt_Access is
   begin
            --  Two surface forms share the `if` keyword:
            --    block-form statement   if cond { ... } [else { ... } | else if ...]
            --    inline expression      if cond then a else b      (as a stmt)
            --  Disambiguate after the condition: '{' => statement.
            Advance (C);

            --  §6.10 `if xlatime { } [else { }]` / `if !xlatime ...`. The
            --  condition is statically `false` in execution-time code, so the
            --  selected branch (else for `xlatime`, then for `!xlatime`) is
            --  kept; the discarded branch is parsed (must be well-formed) but
            --  never type-checked or lowered.
            if C.Cur.Kind = Kw_Xlatime
              or else (C.Cur.Kind = Op_Bang
                       and then Peek_Tok (C).Kind = Kw_Xlatime)
            then
               declare
                  Negated   : Boolean := False;
                  Then_Blk  : Stmt_Vectors.Vector;
                  Else_Blk  : Stmt_Vectors.Vector;
               begin
                  if C.Cur.Kind = Op_Bang then
                     Negated := True;
                     Advance (C);
                  end if;
                  Advance (C);   --  xlatime
                  Parse_Block_Stmts (C, Then_Blk);
                  if C.Cur.Kind = Kw_Else then
                     Advance (C);
                     Parse_Block_Stmts (C, Else_Blk);
                  end if;
                  S := new Stmt_Node (Kind => S_If);
                  S.SI_Cond := new Expr_Node (Kind => E_Bool_Lit);
                  S.SI_Cond.Bool_V := True;
                  --  Execution time: `xlatime` is false. `if xlatime` keeps
                  --  the else branch; `if !xlatime` keeps the then branch.
                  if Negated then
                     S.SI_Then := Then_Blk;
                  else
                     S.SI_Then := Else_Blk;
                  end if;
                  return S;
               end;
            end if;

            --  §7.3.3 `if let PAT = e { } else { }` refutable pattern branch.
            if C.Cur.Kind = Kw_Let then
               Advance (C);
               S := new Stmt_Node (Kind => S_If);
               S.SI_Is_Let := True;
               --  Pattern: Enum::Variant [ { binds } ] (positional bindings),
               --  same shape as a match arm pattern.
               S.SI_Let_Pat.Kind := Pat_Variant;
               S.SI_Let_Pat.Path.Append
                 (Take_Ident (C, "enum name in if-let pattern"));
               while C.Cur.Kind = Punct_ColonColon loop
                  Advance (C);
                  S.SI_Let_Pat.Path.Append (Take_Ident (C, "variant name"));
               end loop;
               if C.Cur.Kind = Punct_LBrace then
                  Parse_Payload_Binds (C, S.SI_Let_Pat);
               end if;
               Expect (C, Punct_Eq, "'=' in if-let");
               --  Suppress trailing struct-literal parsing so the then-block
               --  `{` is not read as `scrutinee { ... }`.
               S.SI_Cond := Parse_Cond (C);
               Parse_Block_Stmts (C, S.SI_Then);
               Expect (C, Kw_Else, "'else' in if-let (spec 7.3.3)");
               if C.Cur.Kind = Kw_If then
                  S.SI_Else.Append (Parse_Stmt (C));   --  else-if chaining
               else
                  Parse_Block_Stmts (C, S.SI_Else);
               end if;
               return S;
            end if;

            declare
               Cond : constant Expr_Access := Parse_Cond (C);
            begin
               if C.Cur.Kind = Punct_Arrow then
                  --  Contract-binding form: if e -> v [| err] { } else { }
                  Advance (C);
                  S := new Stmt_Node (Kind => S_If);
                  S.SI_Cond        := Cond;
                  S.SI_Is_Contract := True;
                  S.SI_Succ_Bind   := Take_Ident (C, "success binding");
                  if C.Cur.Kind = Op_Bar then
                     Advance (C);
                     S.SI_Fail_Bind := Take_Ident (C, "failure binding");
                  end if;
                  Parse_Block_Stmts (C, S.SI_Then);
                  if C.Cur.Kind = Kw_Else then
                     Advance (C);
                     if C.Cur.Kind = Kw_If then
                        S.SI_Else.Append (Parse_Stmt (C));
                     else
                        Parse_Block_Stmts (C, S.SI_Else);
                     end if;
                  end if;
                  return S;
               elsif C.Cur.Kind = Punct_LBrace then
                  S := new Stmt_Node (Kind => S_If);
                  S.SI_Cond := Cond;
                  Parse_Block_Stmts (C, S.SI_Then);
                  if C.Cur.Kind = Kw_Else then
                     Advance (C);
                     if C.Cur.Kind = Kw_If then
                        --  else-if: nest a single S_If in the else body.
                        S.SI_Else.Append (Parse_Stmt (C));
                     else
                        Parse_Block_Stmts (C, S.SI_Else);
                     end if;
                  end if;
                  return S;
               else
                  --  Inline if-expression used as an expression statement.
                  declare
                     E : constant Expr_Access :=
                       new Expr_Node (Kind => E_If);
                  begin
                     E.I_Cond := Cond;
                     Expect (C, Kw_Then, "'then'");
                     E.I_Then := Parse_Expr (C);
                     Expect (C, Kw_Else, "'else'");
                     E.I_Else := Parse_Expr (C);
                     Expect (C, Punct_Semi, "';'");
                     S := new Stmt_Node (Kind => S_Expr);
                     S.E_Val := E;
                     return S;
                  end;
               end if;
            end;

   end Stmt_If;
