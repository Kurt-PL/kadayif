separate (Kurt.Parser)
   function Parse_Primary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
      function Prim_Match return Expr_Access is separate;
      function Prim_Ident return Expr_Access is separate;
   begin
      case C.Cur.Kind is
         when Tok_Int_Lit =>
            E := new Expr_Node (Kind => E_Int_Lit);
            E.Int_V      := C.Cur.Int_V;
            E.Int_Suffix := C.Cur.Int_Suffix;
            Advance (C);
            return E;

         when Op_Slash =>
            --  §9.9 closure `/.params/ ...` (the opening `/.`).
            return Parse_Closure (C, Xfer => False);

         when Kw_Uninit =>
            --  §6.1.8: uninitialized value. Its type is supplied by the
            --  enclosing assignment; sema enforces the airside-only and
            --  assignment-value-only constraints.
            E := new Expr_Node (Kind => E_Uninit);
            Advance (C);
            return E;

         when Tok_Char_Lit =>
            --  §3.5.4: a character literal denotes a single cell value
            --  of type ui1.
            E := new Expr_Node (Kind => E_Int_Lit);
            E.Int_V      := C.Cur.Int_V;
            E.Int_Suffix := SU.To_Unbounded_String ("ui1");
            Advance (C);
            return E;

         when Kw_Cellbits =>
            --  §4.3.1: `cellbits[::exec|::xlat]` evaluates to a `uaddr`
            --  value. `::exec` / `::xlat` name the execution / translation
            --  cell widths; unqualified `cellbits` is `::exec` outside a
            --  xlatime evaluation and max(exec, xlat) within one. On this
            --  host/target exec = xlat, so every form yields the same
            --  value. All three derive from the single source in Kurt.
            Advance (C);
            declare
               Val : Long_Long_Integer := Kurt.Cell_Bits_Exec;
            begin
               if C.Cur.Kind = Punct_ColonColon then
                  Advance (C);
                  declare
                     Q : constant String :=
                       SU.To_String (Take_Ident (C, "cellbits qualifier"));
                  begin
                     if Q = "exec" then
                        Val := Kurt.Cell_Bits_Exec;
                     elsif Q = "xlat" then
                        Val := Kurt.Cell_Bits_Xlat;
                     else
                        raise Syntax_Error with
                          "cellbits qualifier shall be 'exec' or 'xlat' "
                          & "(spec 4.2.1) at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                  end;
               end if;
               E := new Expr_Node (Kind => E_Int_Lit);
               E.Int_V      := Val;
               E.Int_Suffix := SU.To_Unbounded_String ("uaddr");
               return E;
            end;

         when Tok_Float_Lit =>
            E := new Expr_Node (Kind => E_Float_Lit);
            E.Float_V       := C.Cur.Float_V;
            E.Float_Suffix  := C.Cur.Int_Suffix;
            E.Float_Special := C.Cur.Float_Special;
            E.Nan_Quiet     := C.Cur.Nan_Quiet;
            E.Nan_Payload   := C.Cur.Nan_Payload;
            Advance (C);
            return E;

         when Kw_True | Kw_False =>
            --  §3.5.3 bool literals (built-in constants of type bool).
            E := new Expr_Node (Kind => E_Bool_Lit);
            E.Bool_V := C.Cur.Kind = Kw_True;
            Advance (C);
            return E;

         when Punct_Dot =>
            --  Tuple literal `.{ e, e, ... }` (§6.1.7).
            Advance (C);
            Expect (C, Punct_LBrace, "'{' after '.' in tuple literal");
            E := new Expr_Node (Kind => E_Tuple_Lit);
            if C.Cur.Kind /= Punct_RBrace then
               loop
                  E.TL_Elems.Append (Parse_Expr (C));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
               end loop;
            end if;
            Expect (C, Punct_RBrace, "'}' to close tuple literal");
            return E;

         when Tok_String_Lit =>
            E := new Expr_Node (Kind => E_String_Lit);
            E.Str_Bytes := C.Cur.Str_Bytes;
            Advance (C);
            return E;

         when Kw_Xfer =>
            --  §9.9 `xfer /.params/ ...` consuming closure: the `xfer` keyword
            --  immediately precedes the `/.` opener.
            Advance (C);   --  'xfer'
            return Parse_Closure (C, Xfer => True);

         when Kw_Destruct | Kw_Undestruct =>
            --  §8.11: `destruct(e)` and `undestruct(e)` expression forms.
            declare
               Undo : constant Boolean := C.Cur.Kind = Kw_Undestruct;
            begin
               Advance (C);   --  the keyword
               Expect (C, Punct_LParen, "'(' after destruct/undestruct");
               E := new Expr_Node (Kind => E_Destruct);
               E.DT_Undo  := Undo;
               E.DT_Inner := Parse_Expr (C);
               Expect (C, Punct_RParen, "')' to close destruct/undestruct");
               return E;
            end;

         when Tok_Ident | Kw_Self | Kw_Super | Kw_Srcroot =>
            return Prim_Ident;
         when Punct_LParen =>
            Advance (C);
            --  Explicit grouping resolves the struct-literal/block-body
            --  ambiguity that motivates No_Struct_Lit (§6.6): once inside
            --  '(' ... ')' a `{` cannot be mistaken for the caller's block,
            --  so a literal is unambiguous here even where the enclosing
            --  context (e.g. a `match`/`if` scrutinee) forbids one.
            declare
               Saved : constant Boolean := C.No_Struct_Lit;
            begin
               C.No_Struct_Lit := False;
               E := Parse_Expr (C);
               C.No_Struct_Lit := Saved;
            end;
            Expect (C, Punct_RParen, "')'");
            E.Was_Paren := True;   --  §6.6 explicit grouping
            return E;

         when Kw_If =>
            --  §7.1 inline form: `if cond then a else b`. The block
            --  form is deferred.
            Advance (C);
            --  §6.10 `if xlatime then E1 else E2` / `if !xlatime ...`: the
            --  condition is statically false at execution time, so only the
            --  selected operand is kept; the other is parsed but discarded.
            if C.Cur.Kind = Kw_Xlatime
              or else (C.Cur.Kind = Op_Bang
                       and then Peek_Tok (C).Kind = Kw_Xlatime)
            then
               declare
                  Negated : Boolean := False;
                  E1, E2  : Expr_Access;

                  --  §6.10 an `if xlatime` branch in the block form. As with
                  --  a `xlatime { … }` block, the bootstrap restricts the
                  --  body to a single `express E;` (its value); an empty
                  --  block yields `void`.
                  function Xlat_Block return Expr_Access is
                     R : Expr_Access :=
                       new Expr_Node (Kind => E_Path);   --  void placeholder
                  begin
                     R.Segments.Append (SU.To_Unbounded_String ("void"));
                     Expect (C, Punct_LBrace, "'{' in `if xlatime` block");
                     while C.Cur.Kind /= Punct_RBrace
                       and then C.Cur.Kind /= Tok_EOF
                     loop
                        if C.Cur.Kind = Kw_Express then
                           Advance (C);
                           R := Parse_Expr (C);
                           if C.Cur.Kind = Punct_Semi then
                              Advance (C);
                           end if;
                        else
                           raise Syntax_Error with
                             "the bootstrap supports only "
                             & "`if xlatime { express E; }` (no statements) "
                             & "at line" & Positive'Image (C.Cur.Line);
                        end if;
                     end loop;
                     Expect (C, Punct_RBrace, "'}' to close `if xlatime`");
                     return R;
                  end Xlat_Block;
               begin
                  if C.Cur.Kind = Op_Bang then
                     Negated := True;
                     Advance (C);
                  end if;
                  Advance (C);   --  xlatime
                  if C.Cur.Kind = Punct_LBrace then
                     --  §6.10 block form: `if xlatime { … } [else { … }]`.
                     E1 := Xlat_Block;
                     if C.Cur.Kind = Kw_Else then
                        Advance (C);
                        E2 := Xlat_Block;
                     else
                        E2 := new Expr_Node (Kind => E_Path);
                        E2.Segments.Append (SU.To_Unbounded_String ("void"));
                     end if;
                  else
                     --  §6.10 expression form: `if xlatime then E else E`.
                     Expect (C, Kw_Then, "'then' in `if xlatime`");
                     E1 := Parse_Expr (C);
                     Expect (C, Kw_Else, "'else' in `if xlatime`");
                     E2 := Parse_Expr (C);
                  end if;
                  --  §6.10: `xlatime` evaluates to true exactly when the
                  --  surrounding context is itself translation-time
                  --  evaluation (an enclosing `xlatime { ... }` block or a
                  --  `const`/`static` initializer, §6.10.2) -- tracked by
                  --  C.Xlatime_Depth. An ordinary (execution-time) fn body
                  --  has depth 0, so `xlatime` is false there -- the
                  --  existing, pre-fix behaviour.
                  declare
                     Xlat_True : constant Boolean := C.Xlatime_Depth > 0;
                     Cond_Val  : constant Boolean :=
                       (if Negated then not Xlat_True else Xlat_True);
                  begin
                     return (if Cond_Val then E1 else E2);
                  end;
               end;
            end if;
            E := new Expr_Node (Kind => E_If);
            E.I_Cond := Parse_Expr (C);
            Expect (C, Kw_Then, "'then'");
            E.I_Then := Parse_Expr (C);
            Expect (C, Kw_Else, "'else'");
            E.I_Else := Parse_Expr (C);
            return E;

         when Kw_Contract =>
            --  §7.2.3 contract extraction: `contract e else [.id] fallback`.
            --  A general expression: its type is e's success payload type;
            --  the (optional) `.id` binds the failure payload, in scope
            --  only within `fallback`.
            Advance (C);   --  contract
            E := new Expr_Node (Kind => E_Extract);
            E.Ex_Inner := Parse_Expr (C);
            Expect (C, Kw_Else, "'else' in `contract ... else` (spec 7.2.3)");
            --  `.id` vs a fallback that itself starts with `.` (a tuple
            --  literal `.{ ... }`): only `.` followed by an IDENTIFIER is
            --  the optional binding; `.{` belongs to the fallback.
            if C.Cur.Kind = Punct_Dot
              and then Peek_Tok (C).Kind = Tok_Ident
            then
               Advance (C);   --  '.'
               E.Ex_Err := Take_Ident (C, "failure binding after 'else.'");
            end if;
            E.Ex_Fallback := Parse_Expr (C);
            return E;

         when Kw_Xlatime =>
            --  §6.10 `xlatime { express E; }` block expression. The bootstrap
            --  evaluates it at translation time by folding to the expressed
            --  value (subject to the existing const-expression handling); the
            --  body shall be a single `express E;`.
            Advance (C);   --  xlatime
            Expect (C, Punct_LBrace, "'{' after xlatime");
            declare
               Result : Expr_Access := null;
            begin
               --  §6.10: the body of a `xlatime { ... }` block is a
               --  translation-time-evaluated region -- `if xlatime` /
               --  `if !xlatime` nested within it see `xlatime` as TRUE.
               --  Depth-counted (not a flag) so nesting an ordinary fn
               --  body inside would be wrong, but xlatime blocks/consts
               --  themselves may nest.
               C.Xlatime_Depth := C.Xlatime_Depth + 1;
               while C.Cur.Kind /= Punct_RBrace
                 and then C.Cur.Kind /= Tok_EOF
               loop
                  if C.Cur.Kind = Kw_Express then
                     Advance (C);
                     Result := Parse_Expr (C);
                     if C.Cur.Kind = Punct_Semi then
                        Advance (C);
                     end if;
                  else
                     C.Xlatime_Depth := C.Xlatime_Depth - 1;
                     raise Syntax_Error with
                       "the bootstrap supports only `xlatime { express E; }` "
                       & "(no statements) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end loop;
               C.Xlatime_Depth := C.Xlatime_Depth - 1;
               Expect (C, Punct_RBrace, "'}' to close xlatime block");
               if Result = null then
                  raise Syntax_Error with
                    "`xlatime` block requires an `express` (bootstrap)";
               end if;
               return Result;
            end;

         when Kw_Airside =>
            --  §6.9 `airside { ... }` block expression. The value is yielded
            --  by a trailing `express`; with none the block is `void`.
            --  (Statement-position `airside { ... }` never reaches here —
            --  Parse_Stmt claims it first.)
            Advance (C);   --  airside
            E := new Expr_Node (Kind => E_Airside_Blk);
            E.AB_Airside := True;
            Parse_Block_Stmts (C, E.AB_Stmts);
            return E;

         when Punct_LBrace =>
            --  §7.8 a plain brace block `{ … }` in an expression position:
            --  an express block. Its value is yielded by a trailing
            --  `express`; with none the block is `void`. Unlike `airside`,
            --  it does not enter the airside region.
            E := new Expr_Node (Kind => E_Airside_Blk);
            E.AB_Airside := False;
            Parse_Block_Stmts (C, E.AB_Stmts);
            return E;

         when Tok_Label =>
            --  §7.9 labelled block expression `'name: { … }`. Its value
            --  is yielded by `express` (plain or `express 'name`); the
            --  label is what an `express 'name` searches for.
            declare
               Lbl : constant SU.Unbounded_String := C.Cur.Lexeme;
            begin
               Advance (C);
               Expect (C, Punct_Colon, "':' after block label (spec 7.9)");
               if C.Cur.Kind /= Punct_LBrace then
                  raise Syntax_Error with
                    "a label in expression position shall prefix a "
                    & "`{` block (spec 7.9) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               E := new Expr_Node (Kind => E_Airside_Blk);
               E.AB_Airside := False;
               E.AB_Label   := Lbl;
               Parse_Block_Stmts (C, E.AB_Stmts);
               return E;
            end;

         when Kw_Loop =>
            --  §7.7 `loop { … }` as an expression, yielding a `break` value.
            --  (Statement-position `loop` never reaches here — Parse_Stmt
            --  claims it first and desugars it to `while true`.)
            Advance (C);   --  loop
            E := new Expr_Node (Kind => E_Loop);
            Parse_Block_Stmts (C, E.Loop_Body);
            return E;

         when Kw_Match =>
            return Prim_Match;
         when Punct_LBracket =>
            --  §6.1.6 array literal `[a, b, c]` or repeat `[v; N]`.
            Advance (C);
            E := new Expr_Node (Kind => E_Array_Lit);
            if C.Cur.Kind = Punct_RBracket then
               raise Syntax_Error with
                 "array literal needs at least one element at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E.AL_Elems.Append (Parse_Expr (C));
            if C.Cur.Kind = Punct_Semi then
               --  repeat form: the single element fills N slots. §6.1.6: N
               --  "shall be evaluable at translation time" -- any
               --  expression is accepted here (a bare literal, a `const`,
               --  or arithmetic over those); Kurt.Sema.Check resolves it
               --  to a positive literal count (Kurt.Parser.Fold_Int_Expr),
               --  rejecting non-positive/unfoldable N with a diagnostic.
               Advance (C);
               E.AL_Repeat_Expr := Parse_Expr (C);
            else
               while C.Cur.Kind = Punct_Comma loop
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBracket;  --  trailing comma
                  E.AL_Elems.Append (Parse_Expr (C));
               end loop;
            end if;
            Expect (C, Punct_RBracket, "']' to close array literal");
            return E;

         when others =>
            raise Syntax_Error with
              "expected primary expression, got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
      end case;
   end Parse_Primary;
