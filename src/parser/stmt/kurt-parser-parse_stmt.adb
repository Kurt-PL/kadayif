separate (Kurt.Parser)
   function Parse_Stmt (C : in out Cursor) return Stmt_Access is
      S : Stmt_Access;
      Asm_Pos_Idx : Natural := 0;   --  §6.11 anonymous-operand index counter
      function Stmt_If return Stmt_Access is separate;
      function Stmt_Let return Stmt_Access is separate;
      function Stmt_Asm return Stmt_Access is separate;
      function Stmt_Const return Stmt_Access is separate;
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
            return Stmt_Asm;
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
            return Stmt_Let;
         when Kw_Const =>
            --  §5.3: statement-position `const NAME: T = expr;` inside a
            --  fn body (the spec's examples use `const` both at top level
            --  and locally; the bootstrap previously accepted only the
            --  former).
            return Stmt_Const;
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
            --  §7.9: a `'name:` label prefixes a loop or a block. A
            --  labelled block in statement position is an expression
            --  statement (§7.1) whose value, if any, is discarded.
            declare
               Lbl : constant SU.Unbounded_String := C.Cur.Lexeme;
            begin
               Advance (C);
               Expect (C, Punct_Colon, "':' after label (spec 7.9)");
               if C.Cur.Kind = Punct_LBrace then
                  declare
                     E : constant Expr_Access :=
                       new Expr_Node (Kind => E_Airside_Blk);
                  begin
                     E.AB_Airside := False;
                     E.AB_Label   := Lbl;
                     Parse_Block_Stmts (C, E.AB_Stmts);
                     S := new Stmt_Node (Kind => S_Expr);
                     S.E_Val := E;
                     --  §3.2: block expressions as statements need no ';'
                     if C.Cur.Kind = Punct_Semi then
                        Advance (C);
                     end if;
                     return S;
                  end;
               end if;
               if C.Cur.Kind /= Kw_While and then C.Cur.Kind /= Kw_Loop then
                  raise Syntax_Error with
                    "a label shall prefix a `while`/`loop`/`{` block "
                    & "(spec 7.9) at line"
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
            return Stmt_If;

         when Kw_Match =>
            --  §3.3: `match` used as a statement admits an OPTIONAL
            --  trailing ';', like if/while/loop/airside.
            S := new Stmt_Node (Kind => S_Expr);
            S.E_Val := Parse_Expr (C);
            if C.Cur.Kind = Punct_Semi then
               Advance (C);
            end if;
            return S;

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
            --  §7.8/§7.9: express ['label] <expr> ";". The label names
            --  the enclosing labelled block to exit; without one the
            --  immediately enclosing block is targeted.
            Advance (C);
            S := new Stmt_Node (Kind => S_Express);
            if C.Cur.Kind = Tok_Label then
               S.Xp_Label := C.Cur.Lexeme;
               Advance (C);
            end if;
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
