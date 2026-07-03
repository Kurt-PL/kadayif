separate (Kurt.Parser)
   function Parse_Stmt (C : in out Cursor) return Stmt_Access is
      S : Stmt_Access;
      Asm_Pos_Idx : Natural := 0;   --  §6.11 anonymous-operand index counter
   begin
      case C.Cur.Kind is
         when Kw_Return =>
            Advance (C);
            S := new Stmt_Node (Kind => S_Return);
            --  §5.1 bare `return;` in a void subroutine: no value expression.
            if C.Cur.Kind = Punct_Semi then
               S.R_Val := null;
            else
               S.R_Val := Parse_Expr (C);
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Airside =>
            Advance (C);
            S := new Stmt_Node (Kind => S_Airside_Block);
            Parse_Block_Stmts (C, S.A_Stmts);
            --  §3.2: block expressions used as statements need no ';'
            return S;

         when Dir_At_Trap =>
            --  §7.10 `@trap;` termination primitive (statement position).
            --  The `@trap { ... }` handler form is a top-level declaration,
            --  parsed in Parse_Unit, so here a `;` always follows.
            Advance (C);
            S := new Stmt_Node (Kind => S_Trap);
            Expect (C, Punct_Semi, "';'");
            return S;

         when Tok_Asm =>
            --  §6.11 inline assembly. The lexer captured the brace body
            --  verbatim. An optional `with { in/out/io/clobber; ... }` clause
            --  binds Kurt values to concrete registers (bootstrap subset).
            S := new Stmt_Node (Kind => S_Asm);
            S.Asm_Body := C.Cur.Lexeme;
            Advance (C);
            if C.Cur.Kind = Kw_With then
               Advance (C);
               Expect (C, Punct_LBrace, "'{' after `with` in asm");
               --  §6.11 next positional index for an anonymous `in()`/`out()`.
               Asm_Pos_Idx := 0;
               while C.Cur.Kind /= Punct_RBrace
                 and then C.Cur.Kind /= Tok_EOF
               loop
                  declare
                     KS : constant String :=
                       (if C.Cur.Kind = Tok_Ident
                        then SU.To_String (C.Cur.Lexeme) else "");
                  begin
                     if KS = "clobber" then
                        Advance (C);
                        Expect (C, Punct_LParen, "'(' after clobber");
                        while C.Cur.Kind /= Punct_RParen
                          and then C.Cur.Kind /= Tok_EOF
                        loop
                           if C.Cur.Kind = Tok_Ident then
                              S.Asm_Clobbers.Append (C.Cur.Lexeme);
                           end if;
                           Advance (C);   --  register name or comma
                        end loop;
                        Expect (C, Punct_RParen, "')'");
                     elsif KS = "in" or else KS = "out" or else KS = "io" then
                        Advance (C);
                        Expect (C, Punct_LParen, "'(' after in/out/io");
                        declare
                           --  §6.11 operand target — one of:
                           --    `(x0)`    concrete register (resource mode),
                           --    `('name)` logical operand (kept with `'`),
                           --    `('N)`    explicit positional index,
                           --    `()`      anonymous → next positional index.
                           --  Logical / positional targets carry a leading `'`
                           --  so codegen substitutes them in the body.
                           Reg : SU.Unbounded_String;
                        begin
                           if C.Cur.Kind = Punct_RParen then
                              Reg := SU.To_Unbounded_String
                                ("'" & Trim_Img (Asm_Pos_Idx));
                              Asm_Pos_Idx := Asm_Pos_Idx + 1;
                           elsif C.Cur.Kind = Tok_Label then
                              Reg := SU.To_Unbounded_String
                                ("'" & SU.To_String (C.Cur.Lexeme));
                              --  Explicit positional `'N` bumps the counter.
                              declare
                                 LX : constant String :=
                                   SU.To_String (C.Cur.Lexeme);
                                 N  : Natural := 0;
                                 OK : Boolean := LX'Length > 0;
                              begin
                                 for J in LX'Range loop
                                    if LX (J) in '0' .. '9' then
                                       N := N * 10 + (Character'Pos (LX (J))
                                                      - Character'Pos ('0'));
                                    else
                                       OK := False;
                                    end if;
                                 end loop;
                                 if OK and then N + 1 > Asm_Pos_Idx then
                                    Asm_Pos_Idx := N + 1;
                                 end if;
                              end;
                              Advance (C);
                           else
                              Reg := Take_Ident (C, "asm operand register");
                           end if;
                           Expect (C, Punct_RParen, "')'");
                           if KS = "in" or else KS = "io" then
                              Expect (C, Punct_Eq, "'=' in asm in/io operand");
                              S.Asm_In_Regs.Append (Reg);
                              S.Asm_In_Exprs.Append (Parse_Expr (C));
                           end if;
                           if KS = "out" or else KS = "io" then
                              Expect (C, Punct_Arrow,
                                      "'->' in asm out/io operand");
                              S.Asm_Out_Regs.Append (Reg);
                              S.Asm_Out_Names.Append
                                (Take_Ident (C, "asm output binding"));
                           end if;
                        end;
                     else
                        raise Syntax_Error with
                          "expected in/out/io/clobber in asm `with` at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                     if C.Cur.Kind = Punct_Semi then
                        Advance (C);
                     end if;
                  end;
               end loop;
               Expect (C, Punct_RBrace, "'}' to close asm `with`");
            end if;
            if C.Cur.Kind = Punct_Semi then
               Advance (C);
            end if;
            return S;

         when Dir_At_Guard | Dir_At_Volatile =>
            --  §8.5.3 ordering fences: `@guard[.start|.end]`,
            --  `@volatile[.start|.end]`. Each fence is a statement terminated
            --  by a mandatory ';' (part of the grammar, spec 8.5.3).
            S := new Stmt_Node (Kind => S_Fence);
            S.Fn_Guard := C.Cur.Kind = Dir_At_Guard;
            Advance (C);
            if C.Cur.Kind = Punct_Dot then
               Advance (C);
               declare
                  Suffix : constant SU.Unbounded_String :=
                    Take_Ident (C, "'start' or 'end' fence suffix");
               begin
                  if SU.To_String (Suffix) = "start" then
                     S.Fn_Form := FF_Start;
                  elsif SU.To_String (Suffix) = "end" then
                     S.Fn_Form := FF_End;
                  else
                     raise Syntax_Error with
                       "fence suffix must be 'start' or 'end' (spec 8.5.3), "
                       & "got '" & SU.To_String (Suffix) & "' at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end;
            end if;
            Expect (C, Punct_Semi,
              "';' after ordering fence (mandatory, spec 8.5.3)");
            return S;

         when Kw_Let =>
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

         when Kw_Mut =>
            --  §5.2: mut IDENT [: type] [= expr] ;
            --  Multi-assignment binding (§2.2.1).
            Advance (C);
            S := new Stmt_Node (Kind => S_Mut);
            S.L_Name := Take_Ident (C, "mut binding name");
            if C.Cur.Kind = Punct_Colon then
               Advance (C);
               if C.Cur.Kind = Op_Question then   --  §4.12 inferred
                  Advance (C);
               else
                  S.L_Ty := Parse_Type (C);
               end if;
            end if;
            if C.Cur.Kind = Punct_Eq then
               Advance (C);
               S.L_Init := Parse_Expr (C);
            else
               S.L_Init := null;
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Tok_Label =>
            --  §7.9: a `'name:` label prefixes a loop (labelled blocks are
            --  not yet supported). Attach the name to the loop it heads.
            declare
               Lbl : constant SU.Unbounded_String := C.Cur.Lexeme;
            begin
               Advance (C);
               Expect (C, Punct_Colon, "':' after loop label (spec 7.9)");
               if C.Cur.Kind /= Kw_While and then C.Cur.Kind /= Kw_Loop then
                  raise Syntax_Error with
                    "a label shall prefix a `while`/`loop` (labelled blocks "
                    & "are not supported) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               S := Parse_Stmt (C);   --  parse the loop, then label it
               S.W_Label := Lbl;
               return S;
            end;

         when Kw_While =>
            --  §7.5.1 / §7.5.3: while expr { stmts } [ then { stmts } ].
            --  The `then` block runs after each iteration and is the
            --  target of `continue`; `break` skips it.
            Advance (C);
            S := new Stmt_Node (Kind => S_While);
            --  §7.5.1 `while let PAT = e { }`: refutable pattern tested each
            --  iteration; the loop exits when it fails. Same pattern shape as
            --  `if let` (a variant pattern with positional payload bindings).
            if C.Cur.Kind = Kw_Let then
               Advance (C);
               S.W_Is_Let := True;
               S.W_Let_Pat.Kind := Pat_Variant;
               S.W_Let_Pat.Path.Append
                 (Take_Ident (C, "enum name in while-let pattern"));
               while C.Cur.Kind = Punct_ColonColon loop
                  Advance (C);
                  S.W_Let_Pat.Path.Append (Take_Ident (C, "variant name"));
               end loop;
               if C.Cur.Kind = Punct_LBrace then
                  Parse_Payload_Binds (C, S.W_Let_Pat);
               end if;
               Expect (C, Punct_Eq, "'=' in while-let");
            end if;
            S.W_Cond := Parse_Cond (C);
            --  §7.5.1 `while cond -> v { }`: bind the contract success
            --  payload to `v` for the body. (Not available with `while let`.)
            if not S.W_Is_Let and then C.Cur.Kind = Punct_Arrow then
               Advance (C);
               S.W_Is_Contract := True;
               S.W_Succ_Bind := Take_Ident (C, "while `->` success binding");
            end if;
            Parse_Block_Stmts (C, S.W_Body);
            if C.Cur.Kind = Kw_Then then
               Advance (C);
               if C.Cur.Kind /= Punct_LBrace then
                  raise Syntax_Error with
                    "`then` on a loop requires a braced block "
                    & "(spec 7.5.3) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Parse_Block_Stmts (C, S.W_Then);
            end if;
            return S;

         when Kw_Loop =>
            --  §7.5.2: `loop` is semantically `while true`.
            Advance (C);
            S := new Stmt_Node (Kind => S_While);
            S.W_Cond := new Expr_Node (Kind => E_Bool_Lit);
            S.W_Cond.Bool_V := True;
            Parse_Block_Stmts (C, S.W_Body);
            return S;

         when Kw_If =>
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

         when Kw_Break =>
            --  §7.7 / §7.9: break ['label] [expr] ";". The label names the
            --  loop to terminate; the optional expression is its value.
            Advance (C);
            S := new Stmt_Node (Kind => S_Break);
            if C.Cur.Kind = Tok_Label then
               S.Brk_Label := C.Cur.Lexeme;
               Advance (C);
            end if;
            if C.Cur.Kind /= Punct_Semi then
               S.Brk_Val := Parse_Expr (C);
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Continue =>
            --  §7.9: continue ['label] ";".
            Advance (C);
            S := new Stmt_Node (Kind => S_Continue);
            if C.Cur.Kind = Tok_Label then
               S.Cont_Label := C.Cur.Lexeme;
               Advance (C);
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Express =>
            --  §7.8: express <expr> ";"  (labels deferred).
            Advance (C);
            S := new Stmt_Node (Kind => S_Express);
            S.Xp_Val := Parse_Expr (C);
            Expect (C, Punct_Semi, "';'");
            return S;

         when others =>
            --  Expression statement, assignment `place = expr`, or
            --  compound assignment `place op= expr` (§6.7; desugared to
            --  `place = place op expr`).
            declare
               E : constant Expr_Access := Parse_Expr (C);

               function Compound_Op
                 (K : Token_Kind; Op : out Binary_Op) return Boolean is
               begin
                  case K is
                     when Op_PlusEq      => Op := B_Add;
                     when Op_MinusEq     => Op := B_Sub;
                     when Op_StarEq      => Op := B_Mul;
                     when Op_SlashEq     => Op := B_Div;
                     when Op_PercentEq   => Op := B_Mod;
                     when Op_AmpEq       => Op := B_And;
                     when Op_BarEq       => Op := B_Or;
                     when Op_CaretEq     => Op := B_Xor;
                     when Op_ShlEq       => Op := B_Shl;
                     when Op_ShrEq       => Op := B_Shr;
                     when Op_PlusBarEq   => Op := B_Sat_Add;
                     when Op_MinusBarEq  => Op := B_Sat_Sub;
                     when Op_StarBarEq   => Op := B_Sat_Mul;
                     when Op_SlashBarEq  => Op := B_Sat_Div;
                     when others         => return False;
                  end case;
                  return True;
               end Compound_Op;

               C_Op : Binary_Op;
            begin
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  S := new Stmt_Node (Kind => S_Assign);
                  S.Asn_Lhs := E;
                  S.Asn_Rhs := Parse_Expr (C);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               elsif C.Cur.Kind = Punct_LArrow then
                  --  §7.2.3 extract-assignment `place <- e else [err] { }`.
                  if E.Kind /= E_Path
                    or else Natural (E.Segments.Length) /= 1
                  then
                     raise Syntax_Error with
                       "extract-assignment target must be a place at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  Advance (C);   --  <-
                  S := new Stmt_Node (Kind => S_Extract);
                  S.X_Is_Place := True;
                  S.X_Bind := E.Segments.Last_Element;
                  S.X_Expr := Parse_Expr (C);
                  Expect (C, Kw_Else, "'else' in extract-assignment");
                  if C.Cur.Kind = Tok_Ident then
                     S.X_Err := Take_Ident (C, "failure binding");
                  end if;
                  Parse_Block_Stmts (C, S.X_Else);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               elsif Compound_Op (C.Cur.Kind, C_Op) then
                  Advance (C);
                  declare
                     Rhs    : constant Expr_Access := Parse_Expr (C);
                     Combo  : constant Expr_Access :=
                       new Expr_Node (Kind => E_Binary);
                  begin
                     Combo.B_Op  := C_Op;
                     Combo.B_Lhs := E;     --  evaluated twice in bootstrap
                     Combo.B_Rhs := Rhs;
                     S := new Stmt_Node (Kind => S_Assign);
                     S.Asn_Lhs := E;
                     S.Asn_Rhs := Combo;
                     Expect (C, Punct_Semi, "';'");
                     return S;
                  end;
               else
                  S := new Stmt_Node (Kind => S_Expr);
                  S.E_Val := E;
                  Expect (C, Punct_Semi, "';'");
                  return S;
               end if;
            end;
      end case;
   end Parse_Stmt;
