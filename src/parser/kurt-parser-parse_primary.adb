separate (Kurt.Parser)
   function Parse_Primary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
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
            --  §4.2.1: `cellbits[::exec|::xlat]` evaluates to a `uaddr`
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
            Advance (C);
            return E;

         when Kw_True | Kw_False =>
            --  §3.4.3 bool literals (built-in constants of type bool).
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
            --  §9.2 / §10.6: the keywords admissible as a path head are
            --  `self` (method receiver), `super`, and `srcroot` (module
            --  paths); every other keyword in an identifier position
            --  fails below.
            E := new Expr_Node (Kind => E_Path);
            E.Segments.Append (C.Cur.Lexeme);
            Advance (C);
            while C.Cur.Kind = Punct_ColonColon loop
               Advance (C);
               --  §6.1.5 wild construction `Enum::#wild#`: a value of the
               --  enum's implicit `#wild#` (for enums without a declared one).
               if C.Cur.Kind = Tok_Hash_Wild then
                  Advance (C);
                  declare
                     W : constant Expr_Access :=
                       new Expr_Node (Kind => E_Variant_New);
                  begin
                     W.VN_Enum    := E.Segments.First_Element;
                     W.VN_Variant := SU.To_Unbounded_String ("#wild#");
                     return W;
                  end;
               end if;
               --  §10.6 `super::super::name` — chained enclosing-module
               --  references.
               if C.Cur.Kind /= Tok_Ident
                 and then C.Cur.Kind /= Kw_Super
               then
                  raise Syntax_Error with
                    "expected identifier after '::', got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               E.Segments.Append (C.Cur.Lexeme);
               Advance (C);
            end loop;
            --  Explicit generic arguments `path.< T, ... >` (§5.9.2). On a
            --  callee path they drive monomorphisation (Kurt.Mono); on a
            --  literal path (`Box.<si4> { ... }`) the concrete type comes
            --  from context, so the captured args are simply unused.
            if C.Cur.Kind = Punct_Dot
              and then Peek_Tok (C).Kind = Op_Lt
            then
               Advance (C);   --  '.'
               Advance (C);   --  '<'
               Split_Shr_If_Present (C);
               if C.Cur.Kind /= Op_Gt then
                  loop
                     E.P_Type_Args.Append (Parse_Type (C));
                     exit when C.Cur.Kind /= Punct_Comma;
                     Advance (C);
                     Split_Shr_If_Present (C);
                     exit when C.Cur.Kind = Op_Gt;
                  end loop;
               end if;
               Expect (C, Op_Gt, "'>' to close generic arguments");
            end if;
            --  §6.12.2 name intrinsic `T@name`: a translation-time string
            --  (`&[ui1]`) of the type's name. Desugared to a string literal.
            if C.Cur.Kind = Dir_At_Name then
               if Natural (E.Segments.Length) /= 1
                 or else not E.P_Type_Args.Is_Empty
               then
                  raise Syntax_Error with
                    "`@name` operand shall be a plain named type (bootstrap) "
                    & "at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);   --  consume @name
               declare
                  S : constant Expr_Access :=
                    new Expr_Node (Kind => E_String_Lit);
               begin
                  S.Str_Bytes := E.Segments.First_Element;
                  return S;
               end;
            end if;
            --  §6.12 type intrinsic: the parsed path names a *type* when
            --  followed by `@size` / `@align` / `@offset(field)`.
            --  Bootstrap subset: a single-segment named type.
            if C.Cur.Kind in Dir_At_Size | Dir_At_Align | Dir_At_Offset
            then
               if Natural (E.Segments.Length) /= 1
                 or else not E.P_Type_Args.Is_Empty
               then
                  raise Syntax_Error with
                    "type intrinsic operand shall be a plain named type "
                    & "(bootstrap) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               declare
                  TI : constant Expr_Access :=
                    new Expr_Node (Kind => E_Type_Intrinsic);
               begin
                  TI.TI_Ty := new AST_Type'
                    (Kind => T_Named,
                     Name => E.Segments.First_Element,
                     Args => Type_Vectors.Empty_Vector);
                  --  §5.8: an alias name is replaced by its underlying type
                  --  at every use site — including as intrinsic operand.
                  for I in C.Aliases.First_Index ..
                           C.Aliases.Last_Index
                  loop
                     if C.Aliases.Element (I).Params.Is_Empty
                       and then SU."=" (C.Aliases.Element (I).Name,
                                        TI.TI_Ty.Name)
                     then
                        TI.TI_Ty := C.Aliases.Element (I).Target;
                        exit;
                     end if;
                  end loop;
                  case C.Cur.Kind is
                     when Dir_At_Size  => TI.TI_Op := TI_Size;
                     when Dir_At_Align => TI.TI_Op := TI_Align;
                     when others       => TI.TI_Op := TI_Offset;
                  end case;
                  Advance (C);
                  if TI.TI_Op = TI_Offset then
                     Expect (C, Punct_LParen, "'('");
                     TI.TI_Field := Take_Ident (C, "field name");
                     Expect (C, Punct_RParen, "')'");
                  end if;
                  return TI;
               end;
            end if;
            if C.Cur.Kind = Punct_LBrace
              and then not C.No_Struct_Lit
              and then Natural (E.Segments.Length) in 1 .. 2
            then
               declare
                  --  §10.3: `alias::Type { ... }` (alias a known `@add ...
                  --  as alias;` name in this file) is a namespace-qualified
                  --  struct literal, not `Enum::Variant { ... }` — stored as
                  --  a compound `SL_Name` ("alias::Type"), mirroring how
                  --  qualified type names are stored, and mangled later by
                  --  Resolve_Aliases.
                  Is_Add_Alias : constant Boolean :=
                    Natural (E.Segments.Length) = 2
                    and then (for some A of C.Add_Aliases =>
                                SU."=" (A, E.Segments.First_Element));
                  Two  : constant Boolean :=
                    Natural (E.Segments.Length) = 2
                    and then not Is_Add_Alias;
                  Lit  : constant Expr_Access :=
                    (if Two then new Expr_Node (Kind => E_Variant_New)
                            else new Expr_Node (Kind => E_Struct_Lit));
               begin
                  if Two then
                     Lit.VN_Enum    := E.Segments.First_Element;
                     Lit.VN_Variant := E.Segments.Last_Element;
                  elsif Is_Add_Alias then
                     Lit.SL_Name := SU.To_Unbounded_String
                       (SU.To_String (E.Segments.First_Element) & "::"
                        & SU.To_String (E.Segments.Last_Element));
                  else
                     Lit.SL_Name := E.Segments.Last_Element;
                  end if;
                  Advance (C);  --  consume '{'
                  if C.Cur.Kind /= Punct_RBrace then
                     --  §6.1.5 positional vs named: a leading `ident '='`
                     --  starts a named initialiser; anything else is
                     --  positional. Named form is allowed for both struct
                     --  literals and (struct-)variant construction. The
                     --  positional form is meaningful only for tuple
                     --  variants — but using it for a struct literal will
                     --  surface as a field-not-found error in sema.
                     declare
                        Named : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Eq;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              FI : Field_Init;
                           begin
                              if Named then
                                 FI.Name := Take_Ident (C, "field name");
                                 Expect (C, Punct_Eq, "'='");
                              else
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    FI.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Idx := Idx + 1;
                              end if;
                              FI.Val := Parse_Expr (C);
                              if Two then
                                 Lit.VN_Fields.Append (FI);
                              else
                                 Lit.SL_Fields.Append (FI);
                              end if;
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
                  return Lit;
               end;
            end if;
            return E;

         when Punct_LParen =>
            Advance (C);
            E := Parse_Expr (C);
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
                  return (if Negated then E1 else E2);
               end;
            end if;
            E := new Expr_Node (Kind => E_If);
            E.I_Cond := Parse_Expr (C);
            Expect (C, Kw_Then, "'then'");
            E.I_Then := Parse_Expr (C);
            Expect (C, Kw_Else, "'else'");
            E.I_Else := Parse_Expr (C);
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
                     raise Syntax_Error with
                       "the bootstrap supports only `xlatime { express E; }` "
                       & "(no statements) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end loop;
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

         when Kw_Loop =>
            --  §7.7 `loop { … }` as an expression, yielding a `break` value.
            --  (Statement-position `loop` never reaches here — Parse_Stmt
            --  claims it first and desugars it to `while true`.)
            Advance (C);   --  loop
            E := new Expr_Node (Kind => E_Loop);
            Parse_Block_Stmts (C, E.Loop_Body);
            return E;

         when Kw_Match =>
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
               --  repeat form: the single element fills N slots.
               Advance (C);
               if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
                  raise Syntax_Error with
                    "repeat count must be a positive integer literal at "
                    & "line" & Positive'Image (C.Cur.Line);
               end if;
               E.AL_Repeat := Natural (C.Cur.Int_V);
               Advance (C);
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
