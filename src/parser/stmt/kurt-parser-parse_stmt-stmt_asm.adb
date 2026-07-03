separate (Kurt.Parser.Parse_Stmt)
   function Stmt_Asm return Stmt_Access is
   begin
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

   end Stmt_Asm;
