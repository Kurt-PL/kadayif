separate (Kurt.Parser.Parse_Stmt)
   function Stmt_Let return Stmt_Access is
   begin
            --  §5.2 binding  OR  §4.7 tuple destructuring:
            --      let v = expr ;
            --      let .{ a, b } = expr ;
            --  (§7.2.3 contract extraction, `contract e else ...`, is an
            --  ordinary expression -- it reaches here only as `expr` above.)
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
            --  §5.2.1/§5.10.4: a variant pattern (the head ident is
            --  followed by `::` or `{`) destructured against a scrutinee.
            --  L_Is_Refut here only records the *syntactic shape* --
            --  whether this is the variant-pattern form of `let` at all
            --  (every other consumer of it, in codegen/mono/namespacing,
            --  just dispatches on that shape). Genuine refutability is a
            --  static-semantic property of the matched enum (irrefutable
            --  when it has exactly one variant, spec 5.10.4) that only
            --  Kurt.Sema.Check can determine, once the enum decl is
            --  known -- so `else` is parsed here only when present; its
            --  presence is validated against the pattern's actual
            --  refutability in Check_Let (spec 5.2.1's biconditional).
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
               if C.Cur.Kind = Kw_Else then
                  Advance (C);
                  Parse_Block_Stmts (C, S.L_Else);
               end if;
               Expect (C, Punct_Semi, "';'");
               return S;
            end if;
            declare
               Name : constant SU.Unbounded_String :=
                 Take_Ident (C, "let binding name");
            begin
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
               --  §5.2: `let NAME: type;` — deferred initialization
               --  (single-assignment; Kurt.Sema.Check's definite-
               --  assignment pass proves every path assigns it exactly
               --  once before any read). Mirrors `mut`'s own deferred
               --  form (Kw_Mut in Parse_Stmt); the type annotation is
               --  mandatory here (enforced in Check_Let, spec 5.2's
               --  "omits both" constraint).
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  S.L_Init := Parse_Expr (C);
               else
                  S.L_Init := null;
               end if;
               Expect (C, Punct_Semi, "';'");
               return S;
            end;

   end Stmt_Let;
