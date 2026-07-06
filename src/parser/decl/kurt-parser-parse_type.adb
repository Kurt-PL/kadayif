separate (Kurt.Parser)
   function Parse_Type (C : in out Cursor) return Type_Access is
      Node : Type_Access;
   begin
      if C.Cur.Kind = Op_Amp then
         declare
            Amp_Line : constant Positive := C.Cur.Line;
            Amp_Col  : constant Positive := C.Cur.Col;
         begin
            Advance (C);
            Node := new AST_Type (Kind => T_Ref);
            Node.Sigil := R_Shared;
            --  §8.1 `&raw` is a single fused token — no separator may
            --  appear between `&` and `raw` (strict EBNF, ch. 3/8). A
            --  `raw` that follows any whitespace is an ordinary type
            --  name, not the raw-reference qualifier.
            if C.Cur.Kind = Tok_Ident
              and then SU.To_String (C.Cur.Lexeme) = "raw"
              and then C.Cur.Line = Amp_Line
              and then C.Cur.Col = Amp_Col + 1
            then
               Advance (C);
               Node.Sigil := R_Raw;
            end if;
         end;
         --  §8.4 optional lifetime annotation, e.g. `&'static T`.
         if C.Cur.Kind = Tok_Label then
            Node.R_Life := C.Cur.Lexeme;
            Advance (C);
         end if;
         Parse_Ref_Modifiers (C, Node.R_Volatile, Node.R_Store);
         Node.Target := Parse_Type (C);
         return Node;
      elsif C.Cur.Kind = Op_Dollar then
         Advance (C);
         Node := new AST_Type (Kind => T_Ref);
         Node.Sigil := R_Excl;
         --  §8.4 optional lifetime annotation, e.g. `$'a T`.
         if C.Cur.Kind = Tok_Label then
            Node.R_Life := C.Cur.Lexeme;
            Advance (C);
         end if;
         --  §8.1: `$` is inherently storable — only `volatile` may follow.
         Parse_Ref_Modifiers (C, Node.R_Volatile, Node.R_Store);
         if Node.R_Store /= RS_None then
            raise Syntax_Error with
              "'$' is inherently storable; 'mut'/'atomic'/'guard' shall "
              & "not appear after it (spec 8.1) at line"
              & Positive'Image (C.Cur.Line);
         end if;
         Node.Target := Parse_Type (C);
         return Node;
      elsif C.Cur.Kind = Kw_Dyn then
         --  §9.5 trait object `dyn Trait` (appears as `&dyn Trait`).
         Advance (C);
         Node := new AST_Type (Kind => T_Dyn);
         Node.Trait_Name := Take_Ident (C, "trait name after 'dyn'");
         return Node;
      elsif C.Cur.Kind = Kw_Fn or else C.Cur.Kind = Kw_Extern
        or else C.Cur.Kind = Kw_Variadic or else C.Cur.Kind = Kw_Airside
      then
         --  §4.10 subroutine pointer type:
         --      [extern[(iface)]] [variadic] [airside] fn '(' types ')'
         --      [ '->' ( type | never ) ]
         Node := new AST_Type (Kind => T_Fn);
         if C.Cur.Kind = Kw_Extern then
            Advance (C);
            if C.Cur.Kind = Punct_LParen then
               Advance (C);
               Node.Fn_Extern := Take_Ident (C, "extern interface name");
               --  `extern(native)` denotes the native interface (empty).
               if SU.To_String (Node.Fn_Extern) = "native" then
                  Node.Fn_Extern := SU.Null_Unbounded_String;
               end if;
               Expect (C, Punct_RParen, "')'");
            end if;
         end if;
         if C.Cur.Kind = Kw_Variadic then
            Advance (C);
            Node.Fn_Variadic := True;
         end if;
         if C.Cur.Kind = Kw_Airside then
            Advance (C);
            Node.Fn_Airside := True;
         end if;
         Expect (C, Kw_Fn, "'fn'");
         if C.Cur.Kind = Punct_Dot then
            raise Syntax_Error with
              "generic subroutine pointer types are not yet supported "
              & "at line" & Positive'Image (C.Cur.Line);
         end if;
         Expect (C, Punct_LParen, "'('");
         while C.Cur.Kind /= Punct_RParen loop
            --  Optional informational `name :` prefix (no semantic effect).
            if C.Cur.Kind = Tok_Ident
              and then Peek_Tok (C).Kind = Punct_Colon
            then
               Advance (C);   --  name
               Advance (C);   --  ':'
            end if;
            Node.Fn_Params.Append (Parse_Type (C));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);       --  ','  (trailing comma tolerated)
         end loop;
         Expect (C, Punct_RParen, "')'");
         if C.Cur.Kind = Punct_Arrow then
            Advance (C);
            if C.Cur.Kind = Kw_Never then
               Advance (C);
               Node.Fn_Never := True;
               Node.Fn_Ret   := null;
            else
               Node.Fn_Ret := Parse_Type (C);
            end if;
         else
            Node.Fn_Ret := null;
         end if;
         return Node;
      elsif C.Cur.Kind = Op_Slash
        or else (C.Cur.Kind = Kw_Xfer
                 and then Peek_Tok (C).Kind = Op_Slash)
      then
         --  §9.9.2 invocable type: `[xfer] /. T, ... / [ -> ( type | never ) ]`.
         --  Like `fn(T) -> U` it is a pointer-sized value; Fn_Invocable marks
         --  it, Fn_Xfer the consuming `xfer /.T/ -> U` form.
         Node := new AST_Type (Kind => T_Fn);
         Node.Fn_Invocable := True;
         if C.Cur.Kind = Kw_Xfer then
            Advance (C);   --  'xfer'
            Node.Fn_Xfer := True;
         end if;
         Expect (C, Op_Slash, "'/.' to open an invocable type");
         Expect (C, Punct_Dot, "'.' after '/' to open an invocable type");
         while C.Cur.Kind /= Op_Slash loop
            --  Optional informational `name :` prefix (no semantic effect).
            if C.Cur.Kind = Tok_Ident
              and then Peek_Tok (C).Kind = Punct_Colon
            then
               Advance (C);   --  name
               Advance (C);   --  ':'
            end if;
            Node.Fn_Params.Append (Parse_Type (C));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);       --  ','  (trailing comma tolerated)
         end loop;
         Expect (C, Op_Slash, "'/' to close the invocable parameter list");
         if C.Cur.Kind = Punct_Arrow then
            Advance (C);
            if C.Cur.Kind = Kw_Never then
               Advance (C);
               Node.Fn_Never := True;
               Node.Fn_Ret   := null;
            else
               Node.Fn_Ret := Parse_Type (C);
            end if;
         else
            Node.Fn_Ret := null;
         end if;
         return Node;
      elsif C.Cur.Kind = Punct_LBracket then
         --  §4.6 array type: `[T; N]` fixed-size (Len = N) or `[T]`
         --  unsized slice (Len = 0, only valid as a reference target).
         Advance (C);
         Node := new AST_Type (Kind => T_Array);
         Node.Elem := Parse_Type (C);
         if C.Cur.Kind = Punct_Semi then
            Advance (C);
            --  §4.7: `N` need not be a bare integer literal -- any
            --  xlatime-evaluable expression is permitted (a `const`,
            --  arithmetic over literals/consts, ...). The common case (a
            --  plain literal) is still folded immediately here, exactly
            --  as before; anything else is recorded in Len_Expr and
            --  resolved later, by Kurt.Mono.Monomorphize.Visit_Type
            --  (Kurt.Parser.Fold_Int_Expr), ahead of any
            --  Kurt.Layout.Size_Of query -- see the note on Len_Expr in
            --  kurt-parser.ads.
            if C.Cur.Kind = Tok_Int_Lit then
               if C.Cur.Int_V <= 0 then
                  raise Syntax_Error with
                    "array length must be a positive integer literal at "
                    & "line" & Positive'Image (C.Cur.Line);
               end if;
               --  §4.7: an array length that overflows the layout engine's
               --  representable range is a translation failure, not a
               --  wraparound or an uncaught crash. (Kadayif represents
               --  lengths/sizes in `Natural`, narrower than the spec's
               --  64-bit `uaddr`; a length that does not fit here is
               --  rejected cleanly rather than silently truncated.)
               if C.Cur.Int_V > Long_Long_Integer (Natural'Last) then
                  raise Syntax_Error with
                    "array length exceeds the representable range at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Node.Len := Natural (C.Cur.Int_V);
               Advance (C);
            else
               Node.Len_Expr := Parse_Expr (C);
            end if;
         else
            Node.Len := 0;   --  unsized slice `[T]`
         end if;
         Expect (C, Punct_RBracket, "']' to close array type");
         return Node;
      elsif C.Cur.Kind = Punct_Dot then
         --  Tuple type `.{ T, T, ... }` (§4.7).
         Advance (C);
         Expect (C, Punct_LBrace, "'{' after '.' in tuple type");
         Node := new AST_Type (Kind => T_Tuple);
         if C.Cur.Kind /= Punct_RBrace then
            loop
               Node.Elems.Append (Parse_Type (C));
               exit when C.Cur.Kind /= Punct_Comma;
               Advance (C);
               exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
            end loop;
         end if;
         Expect (C, Punct_RBrace, "'}' to close tuple type");
         return Node;
      elsif C.Cur.Kind = Tok_Ident or else C.Cur.Kind = Kw_Selftype then
         --  §9.2: `selftype` is the one keyword admissible as a type name —
         --  the implementing-type placeholder, substituted in Subst_Self.
         Node := new AST_Type (Kind => T_Named);
         Node.Name := SU.To_Unbounded_String
           (Canon_Float (SU.To_String (C.Cur.Lexeme)));
         Advance (C);
         --  Generic arguments: `Name.<T, U>`.
         if C.Cur.Kind = Punct_Dot then
            Advance (C);
            Expect (C, Op_Lt, "'<' after '.' in generic arguments");
            Split_Shr_If_Present (C);
            if C.Cur.Kind /= Op_Gt then
               loop
                  Node.Args.Append (Parse_Type (C));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  Split_Shr_If_Present (C);
                  exit when C.Cur.Kind = Op_Gt;
               end loop;
            end if;
            Expect (C, Op_Gt, "'>' to close generic arguments");
         end if;
         --  §9.3.1 qualified associated-type path `Head::Item` (commonly
         --  `selftype::Item`). Stored as a compound name; resolved when the
         --  impl method is specialised (Subst_Self / mono).
         if C.Cur.Kind = Punct_ColonColon then
            Advance (C);
            Node.Name := SU.To_Unbounded_String
              (SU.To_String (Node.Name) & "::"
               & SU.To_String (Take_Ident (C, "associated type name")));
         end if;
         --  §5.8: a type-alias name is replaced by its underlying type at
         --  every use site. A non-generic alias substitutes directly; a
         --  generic alias `Name.<Args>` expands its template with the
         --  arguments bound to the alias parameters. Declared before use.
         for I in C.Aliases.First_Index .. C.Aliases.Last_Index loop
            if SU."=" (C.Aliases.Element (I).Name, Node.Name) then
               declare
                  AE : Alias_Entry renames C.Aliases.Element (I);
               begin
                  if AE.Params.Is_Empty and then Node.Args.Is_Empty then
                     return AE.Target;
                  elsif Natural (AE.Params.Length)
                          = Natural (Node.Args.Length)
                    and then not AE.Params.Is_Empty
                  then
                     return Copy_Subst (AE.Target, AE.Params, Node.Args);
                  end if;
               end;
            end if;
         end loop;
         return Node;
      else
         raise Syntax_Error with
           "expected type expression, got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Type;
