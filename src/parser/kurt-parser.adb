with Ada.Strings.Fixed;

package body Kurt.Parser is

   use Kurt.Lexer;

   ----------------------------------------------------------------------
   --  Token cursor
   ----------------------------------------------------------------------

   --  §5.8 type aliases registered so far (substituted at use sites
   --  during type parsing; bootstrap: non-generic, declare-before-use).
   type Alias_Entry is record
      Name   : SU.Unbounded_String;
      Target : Type_Access;
      Params : Path_Segments.Vector;   --  §5.8 generic alias `Name.<T,...>`
   end record;

   package Alias_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Alias_Entry);

   package Token_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Kurt.Lexer.Token);

   type Cursor is record
      Lex  : access Kurt.Lexer.Lexer;
      Cur  : Kurt.Lexer.Token;
      Lookahead : Token_Vectors.Vector;
      --  When set, a `path {` is NOT read as a struct literal — used
      --  while parsing if/while conditions, where `{` opens the body.
      --  (Same disambiguation Rust applies.)
      No_Struct_Lit : Boolean := False;
      Aliases : Alias_Vectors.Vector;
      --  §10.3 `@add ... as name;` namespace names seen so far in this file
      --  (declare-before-use, same discipline as `Aliases`). Lets a
      --  composite literal `alias::Type { ... }` be recognised as a
      --  (namespace-qualified) struct literal rather than the default
      --  `Enum::Variant { ... }` reading of a 2-segment path.
      Add_Aliases : Path_Segments.Vector;
   end record;

   procedure Advance (C : in out Cursor) is
   begin
      if not C.Lookahead.Is_Empty then
         C.Cur := C.Lookahead.First_Element;
         C.Lookahead.Delete_First;
      else
         C.Cur := Next_Token (C.Lex.all);
      end if;
   end Advance;

   --  Token after C.Cur (without consuming it).
   function Peek_Tok (C : in out Cursor) return Kurt.Lexer.Token is
   begin
      if C.Lookahead.Is_Empty then
         C.Lookahead.Append (Next_Token (C.Lex.all));
      end if;
      return C.Lookahead.First_Element;
   end Peek_Tok;

   procedure Split_Shr_If_Present (C : in out Cursor) is
   begin
      if C.Cur.Kind = Op_Shr then
         C.Cur.Kind := Op_Gt;
         C.Cur.Lexeme := SU.To_Unbounded_String (">");
         declare
            Tok : Kurt.Lexer.Token;
         begin
            Tok.Kind := Op_Gt;
            Tok.Lexeme := SU.To_Unbounded_String (">");
            Tok.Line := C.Cur.Line;
            Tok.Col := C.Cur.Col + 1;
            C.Lookahead.Prepend (Tok);
         end;
      end if;
   end Split_Shr_If_Present;

   function Image (K : Token_Kind) return String is (Token_Kind'Image (K));

   function Image (T : Kurt.Lexer.Token) return String is
      (Image (T.Kind) & " '" & SU.To_String (T.Lexeme) & "'");

   procedure Expect (C : in out Cursor; K : Token_Kind; What : String) is
   begin
      if K = Op_Gt then
         Split_Shr_If_Present (C);
      end if;
      if C.Cur.Kind /= K then
         raise Syntax_Error with
           "expected " & What & " (" & Image (K) & "), got "
           & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line)
           & ", col"   & Positive'Image (C.Cur.Col);
      end if;
      Advance (C);
   end Expect;

   function Take_Ident (C : in out Cursor; What : String)
      return SU.Unbounded_String
   is
      Name : SU.Unbounded_String;
   begin
      if C.Cur.Kind /= Tok_Ident then
         raise Syntax_Error with
           "expected identifier (" & What & "), got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
      Name := C.Cur.Lexeme;
      Advance (C);
      return Name;
   end Take_Ident;

   --  §3.4.1: like Take_Ident, but for positions where the grammar admits
   --  keywords as words — bound names (`numeric`, `destruct`, ...) and
   --  with-clause items (`contract`, `destruct`, ...). Keywords keep their
   --  spelling in Lexeme, so callers match on the returned string.
   function Take_Word (C : in out Cursor; What : String)
      return SU.Unbounded_String
   is
      Name : SU.Unbounded_String;
   begin
      if not Kurt.Lexer.Is_Word (C.Cur.Kind) then
         raise Syntax_Error with
           "expected word (" & What & "), got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
      Name := C.Cur.Lexeme;
      Advance (C);
      return Name;
   end Take_Word;

   ----------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------

   --  Canonicalise floating-point type aliases to their fe{e}m{m} spelling
   --  (§4) so the rest of the compiler compares one name per type.
   function Canon_Float (N : String) return String is
     (if    N = "f16"  then "fe5m10"
      elsif N = "bf16" then "fe8m7"
      elsif N = "f32"  then "fe8m23"
      elsif N = "f64"  then "fe11m52"
      elsif N = "f128" then "fe15m112"
      elsif N = "f256" then "fe19m236"
      else  N);

   --  §8.1: consume the `[volatile] [mut|atomic|guard]` modifier sequence
   --  between a reference sigil and the referent. Shared by Parse_Type and
   --  the E_Ref prefix expression. The modifiers may appear in any order;
   --  `mut`/`atomic`/`guard` are pairwise mutually exclusive.
   procedure Parse_Ref_Modifiers
     (C        : in out Cursor;
      Volatile : in out Boolean;
      Store    : in out Ref_Store)
   is
      procedure Set_Store (S : Ref_Store) is
      begin
         if Store /= RS_None then
            raise Syntax_Error with
              "'mut', 'atomic' and 'guard' are mutually exclusive "
              & "(spec 8.1) at line" & Positive'Image (C.Cur.Line);
         end if;
         Store := S;
      end Set_Store;
   begin
      loop
         if C.Cur.Kind = Kw_Mut then
            Advance (C);
            Set_Store (RS_Mut);
         elsif C.Cur.Kind = Kw_Volatile then
            Advance (C);
            Volatile := True;
         elsif C.Cur.Kind = Kw_Atomic then
            Advance (C);
            Set_Store (RS_Atomic);
         elsif C.Cur.Kind = Kw_Guard then
            Advance (C);
            Set_Store (RS_Guard);
         else
            exit;
         end if;
      end loop;
   end Parse_Ref_Modifiers;

   --  §8.4.3 `with lifetime` ordering constraints, on a subroutine or a
   --  composite-type declaration:
   --      with lifetime 'a 'b              (single chain, braces optional)
   --      with lifetime { 'a 'b, 'c 'd }   (multiple chains)
   --  Lifetimes are a compile-time discipline with no representation, so the
   --  bootstrap validates the shape and erases it. Pre: the current token is
   --  `with` and the following identifier is `lifetime`.
   procedure Parse_Lifetime_Clause (C : in out Cursor) is
      procedure Parse_Chain is
      begin
         if C.Cur.Kind /= Tok_Label then
            raise Syntax_Error with
              "expected a lifetime ('name) in a 'with lifetime' chain at "
              & "line" & Positive'Image (C.Cur.Line);
         end if;
         while C.Cur.Kind = Tok_Label loop
            Advance (C);
         end loop;
      end Parse_Chain;
   begin
      Advance (C);   --  'with'
      Advance (C);   --  'lifetime'
      if C.Cur.Kind = Punct_LBrace then
         Advance (C);
         loop
            Parse_Chain;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);                            --  ','
            exit when C.Cur.Kind = Punct_RBrace;    --  trailing comma
         end loop;
         Expect (C, Punct_RBrace, "'}' to close 'with lifetime'");
      else
         Parse_Chain;
      end if;
   end Parse_Lifetime_Clause;

   --  Whether the cursor sits at a `with lifetime` clause (`lifetime` is an
   --  ordinary identifier, so this distinguishes it from `with destruct`
   --  etc. by lookahead).
   function At_Lifetime_Clause (C : in out Cursor) return Boolean is
   begin
      return C.Cur.Kind = Kw_With
        and then Peek_Tok (C).Kind = Tok_Ident
        and then SU.To_String (Peek_Tok (C).Lexeme) = "lifetime";
   end At_Lifetime_Clause;

   --  §8.10 parse a `concurrent` with-item body (the keyword `concurrent` is
   --  already consumed): a single item or a braced comma-list, each item
   --  `[!] transfer` or `[!] reference`. Accumulates onto the decl's flags
   --  and rejects a positive together with its own negation (§8.10.1).
   procedure Parse_Concurrent_Items
     (C : in out Cursor;
      Transfer, No_Transfer, Reference, No_Reference : in out Boolean)
   is
      procedure One_Item is
         Neg : Boolean := False;
      begin
         if C.Cur.Kind = Op_Bang then
            Neg := True;
            Advance (C);
         end if;
         if C.Cur.Kind /= Tok_Ident then
            raise Syntax_Error with
              "expected 'transfer' or 'reference' in a 'with concurrent' "
              & "clause at line" & Positive'Image (C.Cur.Line);
         end if;
         declare
            Item : constant String := SU.To_String (C.Cur.Lexeme);
         begin
            Advance (C);
            if Item = "transfer" then
               if Neg then No_Transfer := True; else Transfer := True; end if;
            elsif Item = "reference" then
               if Neg then No_Reference := True; else Reference := True; end if;
            else
               raise Syntax_Error with
                 "a 'with concurrent' item shall be 'transfer' or "
                 & "'reference' (spec 8.10) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
         end;
      end One_Item;
   begin
      if C.Cur.Kind = Punct_LBrace then
         Advance (C);
         loop
            One_Item;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);                            --  ','
            exit when C.Cur.Kind = Punct_RBrace;    --  trailing comma
         end loop;
         Expect (C, Punct_RBrace, "'}' to close 'with concurrent'");
      else
         One_Item;
      end if;
      --  §8.10.1: a positive and its own negation shall not both appear.
      if Transfer and then No_Transfer then
         raise Syntax_Error with
           "'with concurrent' declares both 'transfer' and '!transfer' "
           & "(spec 8.10.1) at line" & Positive'Image (C.Cur.Line);
      end if;
      if Reference and then No_Reference then
         raise Syntax_Error with
           "'with concurrent' declares both 'reference' and '!reference' "
           & "(spec 8.10.1) at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Concurrent_Items;

   --  §5.8 deep-copy a type, substituting each named type matching a generic
   --  alias parameter with the corresponding argument. Used to expand a
   --  generic alias instance `Name.<Args>` against its template.
   function Copy_Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is
      R : Type_Access;
   begin
      if T = null then
         return null;
      end if;
      if T.Kind = T_Named and then T.Args.Is_Empty then
         for I in Params.First_Index .. Params.Last_Index loop
            if SU."=" (Params.Element (I), T.Name) then
               return Args.Element
                 (Args.First_Index + (I - Params.First_Index));
            end if;
         end loop;
      end if;
      R := new AST_Type'(T.all);   --  shallow copy (incl. discriminant)
      case R.Kind is
         when T_Named =>
            R.Args := Type_Vectors.Empty_Vector;
            for I in T.Args.First_Index .. T.Args.Last_Index loop
               R.Args.Append (Copy_Subst (T.Args.Element (I), Params, Args));
            end loop;
         when T_Ref =>
            R.Target := Copy_Subst (T.Target, Params, Args);
         when T_Array =>
            R.Elem := Copy_Subst (T.Elem, Params, Args);
         when T_Tuple =>
            R.Elems := Type_Vectors.Empty_Vector;
            for I in T.Elems.First_Index .. T.Elems.Last_Index loop
               R.Elems.Append (Copy_Subst (T.Elems.Element (I), Params, Args));
            end loop;
         when T_Fn =>
            R.Fn_Params := Type_Vectors.Empty_Vector;
            for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
               R.Fn_Params.Append
                 (Copy_Subst (T.Fn_Params.Element (I), Params, Args));
            end loop;
            R.Fn_Ret := Copy_Subst (T.Fn_Ret, Params, Args);
         when others =>
            null;
      end case;
      return R;
   end Copy_Subst;

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
            if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
               raise Syntax_Error with
                 "array length must be a positive integer literal at line"
                 & Positive'Image (C.Cur.Line);
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

   --  Optional generic parameter clause on a subroutine (§5.9):
   --  `.< T [: bound { '+' bound }], ... >`. Bounds are builtin bound
   --  names (§9.8) recorded for the type-erasure check in Kurt.Sema.
   procedure Parse_Opt_Generic_Params_Bounded
     (C : in out Cursor; Params : out Generic_Param_Vectors.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            --  §5.9 lifetime parameter `'name`: a compile-time discipline
            --  with no representation, so it is parsed and ignored (the
            --  bootstrap's borrow analysis does not consume it).
            if C.Cur.Kind = Tok_Label then
               Advance (C);
            else
               declare
                  P : Generic_Param;
               begin
                  P.Name := Take_Ident (C, "generic parameter");
                  if C.Cur.Kind = Punct_Colon then
                     Advance (C);
                     loop
                        --  §9.8: built-in bound names are keywords
                        --  (`numeric`, `integer`, `primitive`, `contract`,
                        --  `destruct`, `variadic`); trait bounds are
                        --  ordinary identifiers.
                        P.Bounds.Append (Take_Word (C, "bound name"));
                        exit when C.Cur.Kind /= Op_Plus;
                        Advance (C);
                     end loop;
                  end if;
                  Params.Append (P);
               end;
            end if;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params_Bounded;

   --  Optional generic parameter clause on a declaration: `.<T, U>`.
   procedure Parse_Opt_Generic_Params
     (C : in out Cursor; Params : out Path_Segments.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            Params.Append (Take_Ident (C, "generic parameter"));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params;

   ----------------------------------------------------------------------
   --  Parameters
   ----------------------------------------------------------------------

   function Parse_Param
     (C : in out Cursor; Allow_Unnamed : Boolean) return Param
   is
      P : Param;
   begin
      --  §5.1 `mut name: T` — a mutable parameter binding. The `mut` modifier
      --  is local to the body; it does not affect the signature.
      if C.Cur.Kind = Kw_Mut then
         Advance (C);
         P.Is_Mut := True;
      end if;
      --  §9.2 self parameter: `&self` / `$self`. The referent is the
      --  placeholder `selftype`, substituted with the impl type by
      --  Parse_Impl_Decl.
      if (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar)
        and then Peek_Tok (C).Kind = Kw_Self
      then
         --  §9.2 self_param: `mut` and a reference sigil are mutually
         --  exclusive alternatives — `mut &self` shall not appear.
         if P.Is_Mut then
            raise Syntax_Error with
              "`mut` and a reference sigil are mutually exclusive on "
              & "`self` (spec 9.2) at line" & Positive'Image (C.Cur.Line);
         end if;
         declare
            Sigil : constant Ref_Sigil :=
              (if C.Cur.Kind = Op_Amp then R_Shared else R_Excl);
         begin
            Advance (C);   --  sigil
            Advance (C);   --  self
            P.Name := SU.To_Unbounded_String ("self");
            P.Ty   := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil  := Sigil;
            P.Ty.Target := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String ("selftype");
            return P;
         end;
      end if;
      if C.Cur.Kind = Tok_Ident then
         declare
            Saved : constant SU.Unbounded_String := C.Cur.Lexeme;
         begin
            Advance (C);
            if C.Cur.Kind = Punct_Colon then
               Advance (C);
               P.Name := Saved;
               P.Ty   := Parse_Type (C);
               return P;
            elsif Allow_Unnamed then
               --  The identifier we already consumed was the head of a
               --  bare-type expression: synthesize a named type from it.
               P.Name := SU.Null_Unbounded_String;
               P.Ty   := new AST_Type (Kind => T_Named);
               P.Ty.Name := Saved;
               return P;
            else
               raise Syntax_Error with
                 "expected ':' after parameter name, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
            end if;
         end;
      elsif Allow_Unnamed
        and then (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar
                  or else C.Cur.Kind = Kw_Dyn
                  or else C.Cur.Kind = Punct_LBracket
                  --  §4.10 unnamed subroutine-pointer-typed parameter.
                  or else C.Cur.Kind = Kw_Fn
                  or else C.Cur.Kind = Kw_Extern
                  or else C.Cur.Kind = Kw_Variadic
                  or else C.Cur.Kind = Kw_Airside)
      then
         P.Name := SU.Null_Unbounded_String;
         P.Ty   := Parse_Type (C);
         return P;
      else
         raise Syntax_Error with
           "expected parameter, got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Param;

   procedure Parse_Param_List
     (C             : in out Cursor;
      Params        : out Param_Vectors.Vector;
      Allow_Unnamed : Boolean)
   is
   begin
      Expect (C, Punct_LParen, "'('");
      if C.Cur.Kind /= Punct_RParen then
         loop
            Params.Append (Parse_Param (C, Allow_Unnamed));
            --  §9.2: the self_param production fixes `self` as the FIRST
            --  parameter; a self parameter in any later position shall
            --  not appear.
            if Natural (Params.Length) > 1
              and then SU.To_String (Params.Last_Element.Name) = "self"
            then
               raise Syntax_Error with
                 "`self` shall be the first parameter (spec 9.2) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;
         end loop;
      end if;
      Expect (C, Punct_RParen, "')'");
   end Parse_Param_List;

   ----------------------------------------------------------------------
   --  Expressions
   --
   --  Grammar layered as:
   --     Expr      = Binary
   --     Binary    = Postfix { binop Postfix }      Pratt by binding power
   --     Postfix   = Primary { '.' IDENT | '(' args ')' }
   --     Primary   = INT | STRING | path | '(' Expr ')'
   --               | "if" Expr "then" Expr "else" Expr
   --
   --  Precedence is taken from §6 (lower number = tighter binding).
   --  We convert to "binding power" where higher number = tighter.
   ----------------------------------------------------------------------

   function Parse_Expr (C : in out Cursor) return Expr_Access;

   --  §9.9 closure expression (body defined after Parse_Block_Stmts).
   function Parse_Closure
     (C : in out Cursor; Xfer : Boolean) return Expr_Access;

   function Token_To_Binop (K : Token_Kind; Op : out Binary_Op) return Boolean is
   begin
      case K is
         when Op_Plus     => Op := B_Add;
         when Op_Minus    => Op := B_Sub;
         when Op_Star     => Op := B_Mul;
         when Op_Slash    => Op := B_Div;
         when Op_Percent  => Op := B_Mod;
         when Op_PlusBar  => Op := B_Sat_Add;
         when Op_MinusBar => Op := B_Sat_Sub;
         when Op_StarBar  => Op := B_Sat_Mul;
         when Op_SlashBar => Op := B_Sat_Div;
         when Op_Amp      => Op := B_And;
         when Op_Bar      => Op := B_Or;
         when Op_Caret    => Op := B_Xor;
         when Op_Shl      => Op := B_Shl;
         when Op_Shr      => Op := B_Shr;
         when Op_PlusAt   => Op := B_Wide_Add;
         when Op_StarAt   => Op := B_Wide_Mul;
         when Op_EqEq    => Op := B_Eq;
         when Op_BangEq  => Op := B_Ne;
         when Op_Lt      => Op := B_Lt;
         when Op_Gt      => Op := B_Gt;
         when Op_Le      => Op := B_Le;
         when Op_Ge      => Op := B_Ge;
         when Op_AmpAmp  => Op := B_LAnd;
         when Op_BarBar  => Op := B_LOr;
         when others     => return False;
      end case;
      return True;
   end Token_To_Binop;

   --  Higher = tighter binding. Mirrors §6 precedence table:
   --    spec prec 7  (* / %)              => bp 70
   --    spec prec 8  (+ -)                => bp 60
   --    spec prec 13 (== != < > <= >=)    => bp 30
   function Binding_Power (Op : Binary_Op) return Natural is
   begin
      case Op is
         when B_Mul | B_Div | B_Mod | B_Sat_Mul | B_Sat_Div
            | B_Wide_Mul => return 70;
         when B_Add | B_Sub | B_Sat_Add | B_Sat_Sub
            | B_Wide_Add => return 60;
         when B_Shl | B_Shr => return 50;   --  §6 level 9
         when B_And         => return 45;   --  level 10
         when B_Xor         => return 40;   --  level 11
         when B_Or          => return 35;   --  level 12
         when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge => return 30;  --  13
         when B_LAnd        => return 20;   --  §7.2.2, below comparison
         when B_LOr         => return 15;
      end case;
   end Binding_Power;

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
            E.Float_V      := C.Cur.Float_V;
            E.Float_Suffix := C.Cur.Int_Suffix;
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
               begin
                  if C.Cur.Kind = Op_Bang then
                     Negated := True;
                     Advance (C);
                  end if;
                  Advance (C);   --  xlatime
                  Expect (C, Kw_Then, "'then' in `if xlatime`");
                  E1 := Parse_Expr (C);
                  Expect (C, Kw_Else, "'else' in `if xlatime`");
                  E2 := Parse_Expr (C);
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
                           --  Optional payload destructuring `{ a, b }`.
                           if C.Cur.Kind = Punct_LBrace then
                              Advance (C);
                              if C.Cur.Kind /= Punct_RBrace then
                                 loop
                                    P.Bindings.Append
                                      (Take_Ident (C, "payload binding"));
                                    exit when C.Cur.Kind /= Punct_Comma;
                                    Advance (C);
                                    exit when C.Cur.Kind = Punct_RBrace;
                                 end loop;
                              end if;
                              Expect (C, Punct_RBrace, "'}'");
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

   function Parse_Postfix (C : in out Cursor; Start : Expr_Access)
      return Expr_Access
   is
      Left : Expr_Access := Start;
   begin
      loop
         case C.Cur.Kind is
            when Punct_Dot =>
               Advance (C);
               declare
                  --  Struct/method field is an identifier; tuple field is
                  --  a non-negative integer literal (§4.7, §6.2.2).
                  Name : SU.Unbounded_String;
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Field);
               begin
                  if C.Cur.Kind = Tok_Int_Lit then
                     declare
                        Im : constant String := C.Cur.Int_V'Image;
                     begin  --  'Image of a non-negative has a leading space
                        Name := SU.To_Unbounded_String
                          (Im (Im'First + 1 .. Im'Last));
                     end;
                     Advance (C);
                  else
                     Name := Take_Ident (C, "field name or tuple index");
                  end if;
                  Next.F_Recv := Left;
                  Next.F_Name := Name;
                  Left := Next;
               end;

            when Op_Question =>
               --  §6.2.4 / §7.2.4: contract propagation. `e?` extracts the
               --  success payload of a contract value, or returns its
               --  failure value from the enclosing subroutine.
               Advance (C);
               declare
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Question);
               begin
                  Next.Q_Inner := Left;
                  Left := Next;
               end;

            when Punct_LParen =>
               Advance (C);
               declare
                  Args : Expr_Vectors.Vector;
                  Next : Expr_Access;
               begin
                  if C.Cur.Kind /= Punct_RParen then
                     loop
                        Args.Append (Parse_Expr (C));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RParen;
                     end loop;
                  end if;
                  Expect (C, Punct_RParen, "')'");
                  Next := new Expr_Node (Kind => E_Call);
                  Next.C_Callee := Left;
                  Next.C_Args   := Args;
                  Left := Next;
               end;

            when Punct_ColonColon =>
               --  §6.1.1 qualified path root `(T as Trait)::item…`: the left
               --  operand is a parenthesized `(T as Trait)` cast. Desugar to
               --  the path `T::item…` — the trait selects the impl namespace,
               --  and in the bootstrap an associated item mangles identically
               --  to `T$item`, so resolution is unambiguous. (The `T`-impl-
               --  `Trait` relationship is not separately re-validated here.)
               exit when Left.Kind /= E_Cast
                 or else not Left.Was_Paren
                 or else Left.Cast_Bang or else Left.Cast_Disc
                 or else Left.Cast_Inner = null
                 or else Left.Cast_Inner.Kind /= E_Path;
               declare
                  NP : constant Expr_Access := new Expr_Node (Kind => E_Path);
               begin
                  NP.Segments := Left.Cast_Inner.Segments;   --  T
                  NP.Path_Trait := Left.Cast_Ty.Name;        --  Trait
                  loop
                     Advance (C);   --  '::'
                     NP.Segments.Append
                       (Take_Ident (C, "name after '::' in qualified path"));
                     exit when C.Cur.Kind /= Punct_ColonColon;
                  end loop;
                  Left := NP;
               end;

            when others =>
               exit;
         end case;
      end loop;
      return Left;
   end Parse_Postfix;

   --  Unary prefix operators (§6.3, prec 5). Bootstrap: `*` deref, `-` neg,
   --  `!` not, and §8.1 reference creation `&[raw] [mods] place` / `$place`.
   function Parse_Unary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
   begin
      if C.Cur.Kind = Op_Star then
         Advance (C);
         E := new Expr_Node (Kind => E_Deref);
         E.D_Inner := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Amp then
         --  §8.1 reference creation. Prefix position only — the infix
         --  bitwise `&` is consumed by Parse_Binary before reaching here.
         declare
            Amp_Line : constant Positive := C.Cur.Line;
            Amp_Col  : constant Positive := C.Cur.Col;
         begin
            Advance (C);
            E := new Expr_Node (Kind => E_Ref);
            E.Rf_Sigil := R_Shared;
            --  §8.1 `&raw` is a single fused token — see Parse_Type.
            if C.Cur.Kind = Tok_Ident
              and then SU.To_String (C.Cur.Lexeme) = "raw"
              and then C.Cur.Line = Amp_Line
              and then C.Cur.Col = Amp_Col + 1
            then
               Advance (C);
               E.Rf_Sigil := R_Raw;
            end if;
         end;
         Parse_Ref_Modifiers (C, E.Rf_Volatile, E.Rf_Store);
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Dollar then
         Advance (C);
         E := new Expr_Node (Kind => E_Ref);
         E.Rf_Sigil := R_Excl;
         declare
            Vol   : Boolean   := False;
            Store : Ref_Store := RS_None;
         begin
            Parse_Ref_Modifiers (C, Vol, Store);
            if Store /= RS_None then
               raise Syntax_Error with
                 "'$' is inherently storable; 'mut'/'atomic'/'guard' shall "
                 & "not appear after it (spec 8.1) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E.Rf_Volatile := Vol;
         end;
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Minus then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Neg;
         E.U_Operand := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Bang then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Not;
         E.U_Operand := Parse_Unary (C);
         return E;
      else
         return Parse_Postfix (C, Parse_Primary (C));
      end if;
   end Parse_Unary;

   --  Cast operators `as` / `as ?` (§6.8, prec 6 — between unary and
   --  multiplicative). `as!` (airside reinterpret) is deferred.
   function Parse_Cast (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Unary (C);
   begin
      while C.Cur.Kind = Kw_As or else C.Cur.Kind = Kw_As_Bang loop
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_Cast);
            Bang : constant Boolean := C.Cur.Kind = Kw_As_Bang;  --  §6.8.11
         begin
            Advance (C);   --  consume `as` / `as!`
            Next.Cast_Inner := E;
            Next.Cast_Bang  := Bang;
            if C.Cur.Kind = Op_Question and then not Bang then
               Advance (C);
               Next.Cast_Disc := True;
               Next.Cast_Ty   := null;
            else
               Next.Cast_Ty := Parse_Type (C);
            end if;
            E := Next;
         end;
      end loop;
      return E;
   end Parse_Cast;

   function Is_Cmp (Op : Binary_Op) return Boolean is
     (Op in B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge);

   --  §6.6 bitwise / shift operators (`& | ^ << >>`).
   function Is_Bitsh (Op : Binary_Op) return Boolean is
     (Op in B_And | B_Or | B_Xor | B_Shl | B_Shr);

   --  §6.6: a comparison mixed with a bitwise/shift operator (in either
   --  order) without intervening parentheses shall not appear. An operand
   --  that is itself an un-parenthesised binary node of the opposing class
   --  is the violation; explicit grouping (`Was_Paren`) makes it well-formed.
   function Mixes_Cmp_Bitsh (Op : Binary_Op; Operand : Expr_Access)
     return Boolean is
   begin
      if Operand = null or else Operand.Kind /= E_Binary
        or else Operand.Was_Paren
      then
         return False;
      end if;
      return (Is_Cmp (Op) and then Is_Bitsh (Operand.B_Op))
        or else (Is_Bitsh (Op) and then Is_Cmp (Operand.B_Op));
   end Mixes_Cmp_Bitsh;

   function Parse_Binary
     (C : in out Cursor; Min_BP : Natural) return Expr_Access
   is
      Left : Expr_Access := Parse_Cast (C);
      Op   : Binary_Op;
   begin
      while Token_To_Binop (C.Cur.Kind, Op) loop
         declare
            BP : constant Natural := Binding_Power (Op);
            Next : Expr_Access;
         begin
            exit when BP < Min_BP;
            Advance (C);
            --  Left-associative: parse RHS with strictly higher BP.
            declare
               R : constant Expr_Access := Parse_Binary (C, BP + 1);
               Next_Op : Binary_Op;
            begin
               --  §6.6: comparison operators are non-associative.
               --  `a < b < c` shall be parenthesised, not chained.
               if Is_Cmp (Op)
                 and then Token_To_Binop (C.Cur.Kind, Next_Op)
                 and then Is_Cmp (Next_Op)
               then
                  raise Syntax_Error with
                    "comparison operators are non-associative (§6.6); "
                    & "parenthesise the chain at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               --  §6.6 mixed comparison × bitwise/shift without parens.
               if Mixes_Cmp_Bitsh (Op, Left)
                 or else Mixes_Cmp_Bitsh (Op, R)
               then
                  raise Syntax_Error with
                    "a comparison mixed with a bitwise/shift operator "
                    & "requires explicit parentheses (§6.6) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Next := new Expr_Node (Kind => E_Binary);
               Next.B_Op  := Op;
               Next.B_Lhs := Left;
               Next.B_Rhs := R;
               Left := Next;
            end;
         end;
      end loop;
      return Left;
   end Parse_Binary;

   --  §8.7 compare-and-swap: `target >.< expected <- new` (eq-CAS) and
   --  `target >!< expected <- new` (ne-CAS), at the lowest binding power
   --  (the operands are full binary expressions). Non-associative.
   function Parse_Expr (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Binary (C, 0);
   begin
      --  §3.7: `..`/`..=` are pattern-only tokens — no value-level range
      --  type exists, so a range in expression position is ill-formed.
      if C.Cur.Kind = Op_DotDot or else C.Cur.Kind = Op_DotDotEq then
         raise Syntax_Error with
           "`..`/`..=` form patterns only; no range value exists (§3.7) "
           & "at line" & Positive'Image (C.Cur.Line);
      end if;
      if C.Cur.Kind = Op_EqCas or else C.Cur.Kind = Op_NeCas then
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_CAS);
         begin
            Next.CAS_Ne := C.Cur.Kind = Op_NeCas;
            Advance (C);
            Next.CAS_Tgt := E;
            Next.CAS_Exp := Parse_Binary (C, 0);
            Expect (C, Punct_LArrow, "'<-' in compare-and-swap (spec 8.7)");
            Next.CAS_New := Parse_Binary (C, 0);
            E := Next;
         end;
      end if;
      return E;
   end Parse_Expr;

   ----------------------------------------------------------------------
   --  Statements / blocks
   ----------------------------------------------------------------------

   function Parse_Stmt (C : in out Cursor) return Stmt_Access;

   --  Parse a condition expression with struct-literal suppression so
   --  the following '{' is read as a block, not a struct literal.
   function Parse_Cond (C : in out Cursor) return Expr_Access is
      Saved : constant Boolean := C.No_Struct_Lit;
      R     : Expr_Access;
   begin
      C.No_Struct_Lit := True;
      R := Parse_Expr (C);
      C.No_Struct_Lit := Saved;
      return R;
   end Parse_Cond;

   procedure Parse_Block_Stmts
     (C : in out Cursor; Stmts : out Stmt_Vectors.Vector)
   is
   begin
      Expect (C, Punct_LBrace, "'{'");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         --  §7.1 null statement: a bare `;` performs no operations.
         if C.Cur.Kind = Punct_Semi then
            Advance (C);
         else
            Stmts.Append (Parse_Stmt (C));
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}'");
   end Parse_Block_Stmts;

   --  §9.9 closure: `[xfer] '/.' [ name [: T] {',' ...} ] '/' tail`, where the
   --  tail is `-> T { block }`, `{ block }`, or `<- expr`. The `xfer` keyword
   --  (if present) is already consumed by the caller. The opening `/.` lexes
   --  as `/` then `.`; the closing `/` is a lone `/`.
   function Parse_Closure
     (C : in out Cursor; Xfer : Boolean) return Expr_Access
   is
      E : constant Expr_Access := new Expr_Node (Kind => E_Closure);
   begin
      E.Clo_Xfer := Xfer;
      Expect (C, Op_Slash, "'/.' to open a closure");
      Expect (C, Punct_Dot, "'.' after '/' to open a closure");
      if C.Cur.Kind /= Op_Slash then
         loop
            declare
               PName : constant SU.Unbounded_String :=
                 Take_Ident (C, "closure parameter name");
               PTy   : Type_Access := null;
            begin
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  PTy := Parse_Type (C);
               end if;
               E.Clo_Params.Append ((Name => PName, Ty => PTy));
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
         end loop;
      end if;
      Expect (C, Op_Slash, "'/' to close the closure parameter list");

      if C.Cur.Kind = Punct_Arrow then
         Advance (C);
         E.Clo_Ret := Parse_Type (C);
         Parse_Block_Stmts (C, E.Clo_Body);
      elsif C.Cur.Kind = Punct_LBrace then
         Parse_Block_Stmts (C, E.Clo_Body);
      elsif C.Cur.Kind = Punct_LArrow then
         --  Short form `/.p/ <- e` desugars to `{ return e; }`.
         Advance (C);
         declare
            R : constant Stmt_Access := new Stmt_Node (Kind => S_Return);
         begin
            R.R_Val := Parse_Expr (C);
            E.Clo_Body.Append (R);
         end;
      else
         raise Syntax_Error with
           "expected '->', '{', or '<-' in a closure tail at line"
           & Positive'Image (C.Cur.Line);
      end if;
      return E;
   end Parse_Closure;

   --  Natural to string with no leading space.
   function Trim_Img (N : Natural) return String is
      Raw : constant String := Natural'Image (N);
   begin
      return Raw (Raw'First + 1 .. Raw'Last);
   end Trim_Img;

   function Parse_Stmt (C : in out Cursor) return Stmt_Access is
      S : Stmt_Access;
      Asm_Pos_Idx : Natural := 0;   --  §6.11 anonymous-operand index counter
   begin
      case C.Cur.Kind is
         when Kw_Return =>
            Advance (C);
            S := new Stmt_Node (Kind => S_Return);
            S.R_Val := Parse_Expr (C);
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
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     loop
                        S.L_Refut_Pat.Bindings.Append
                          (Take_Ident (C, "payload binding"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RBrace;
                     end loop;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
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
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     loop
                        S.W_Let_Pat.Bindings.Append
                          (Take_Ident (C, "payload binding"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RBrace;
                     end loop;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
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
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     loop
                        S.SI_Let_Pat.Bindings.Append
                          (Take_Ident (C, "payload binding"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RBrace;
                     end loop;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
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

   ----------------------------------------------------------------------
   --  fn header / proto / decl
   ----------------------------------------------------------------------

   procedure Parse_Fn_Header
     (C             : in out Cursor;
      Allow_Unnamed : Boolean;
      H             : out Fn_Header)
   is
   begin
      --  §5.14/§5.15: `@inline` / `@no_inline` / `@symbol "name"` precede
      --  the rest of the header (before `pub`/`airside`). The inlining
      --  directives are mutually exclusive.
      while C.Cur.Kind = Dir_At_Inline
            or else C.Cur.Kind = Dir_At_No_Inline
            or else C.Cur.Kind = Dir_At_Symbol
      loop
         if C.Cur.Kind = Dir_At_Inline then
            H.Is_Inline := True;
            Advance (C);
         elsif C.Cur.Kind = Dir_At_No_Inline then
            H.Is_No_Inline := True;
            Advance (C);
         else
            Advance (C);   --  past @symbol
            if C.Cur.Kind /= Tok_String_Lit then
               raise Syntax_Error with
                 "`@symbol` requires a string literal (spec 5.15) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            H.Symbol_Name := C.Cur.Str_Bytes;
            Advance (C);
         end if;
      end loop;
      if H.Is_Inline and then H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline` and `@no_inline` shall not both appear on the same "
           & "subroutine (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;

      --  §5.1 header order: [pub] [extern[(iface)]] — independent
      --  modifiers; `pub extern fn` is legal.
      if C.Cur.Kind = Kw_Pub then
         H.Is_Pub := True;
         Advance (C);
      end if;
      if C.Cur.Kind = Kw_Extern then
         H.Is_Extern := True;
         Advance (C);
      end if;

      if C.Cur.Kind = Kw_Variadic then
         Advance (C);
         H.Is_Variadic := True;
         --  §5.1.3: the declaration form requires the binding clause
         --  `variadic(name: T)`; the bare keyword is the prototype form
         --  (subroutine_proto_header, e.g. inside @dyn).
         if C.Cur.Kind = Punct_LParen then
            Advance (C);
            H.Variadic_Name := Take_Ident (C, "variadic binding name");
            Expect (C, Punct_Colon, "':'");
            H.Variadic_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif not Allow_Unnamed then
            raise Syntax_Error with
              "a variadic subroutine definition requires "
              & "'variadic(name: type)' (spec 5.1.3) at line"
              & Positive'Image (C.Cur.Line);
         end if;
      end if;

      if C.Cur.Kind = Kw_Airside then
         H.Is_Airside := True;
         Advance (C);
      end if;

      Expect (C, Kw_Fn, "'fn'");
      H.Name := Take_Ident (C, "function name");
      Parse_Opt_Generic_Params_Bounded (C, H.Generic_Params);
      Parse_Param_List (C, H.Params, Allow_Unnamed);

      if C.Cur.Kind = Punct_Arrow then
         Advance (C);
         if C.Cur.Kind = Kw_Never then
            --  §4.10/§7.11: `-> never`. No value type; the body diverges.
            Advance (C);
            H.Is_Never    := True;
            H.Return_Type := null;
         else
            H.Return_Type := Parse_Type (C);
         end if;
      else
         H.Return_Type := null;
      end if;

      --  §8.4.3 optional `with lifetime` ordering clause on the subroutine.
      if At_Lifetime_Clause (C) then
         Parse_Lifetime_Clause (C);
      end if;
   end Parse_Fn_Header;

   function Parse_Fn_Decl (C : in out Cursor) return Fn_Decl is
      F : Fn_Decl;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => False, H => F.Header);
      --  §5.15: `@symbol` on a definition requires the `extern` prefix
      --  (a non-extern subroutine has no external name to override).
      if SU.Length (F.Header.Symbol_Name) > 0
        and then not F.Header.Is_Extern
      then
         raise Syntax_Error with
           "`@symbol` requires `extern` (or a `@dyn` block) (spec 5.15) at "
           & "line" & Positive'Image (C.Cur.Line);
      end if;
      Parse_Block_Stmts (C, F.Body_Stmts);
      return F;
   end Parse_Fn_Decl;

   function Parse_Fn_Proto (C : in out Cursor) return Fn_Proto is
      H : Fn_Header;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => True, H => H);
      --  §5.14: inlining directives shall not apply to a prototype (a
      --  declaration without a body).
      if H.Is_Inline or else H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline`/`@no_inline` shall not be applied to a subroutine "
           & "prototype (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;
      Expect (C, Punct_Semi, "';' to terminate fn prototype");
      return H;
   end Parse_Fn_Proto;

   ----------------------------------------------------------------------
   --  @dyn declaration
   ----------------------------------------------------------------------

   function Parse_Dyn_Decl (C : in out Cursor) return Dyn_Decl is
      D : Dyn_Decl;
   begin
      Expect (C, Dir_At_Dyn, "'@dyn'");
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      --  §10.4 optional bound form `[prefix::]"path"`. The path identifies the
      --  opaque code; resolution/symbol-presence checking against the host
      --  linker is deferred, so the path is recorded but not yet verified.
      if C.Cur.Kind = Tok_Ident
        and then Peek_Tok (C).Kind = Punct_ColonColon
      then
         Advance (C);   --  prefix
         Advance (C);   --  ::
      end if;
      if C.Cur.Kind = Tok_String_Lit then
         D.Bound_Path := C.Cur.Str_Bytes;
         Advance (C);
      end if;
      Expect (C, Kw_As, "'as'");
      D.Alias := Take_Ident (C, "alias name for @dyn block");

      Expect (C, Punct_LBrace, "'{'");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         if C.Cur.Kind = Kw_Fn
           or else C.Cur.Kind = Kw_Pub
           or else C.Cur.Kind = Kw_Extern
           or else C.Cur.Kind = Kw_Variadic
           or else C.Cur.Kind = Dir_At_Symbol   --  §5.15 on a dyn item
         then
            D.Items.Append (Parse_Fn_Proto (C));
         else
            raise Syntax_Error with
              "expected fn prototype inside @dyn block, got "
              & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}'");
      return D;
   end Parse_Dyn_Decl;

   ----------------------------------------------------------------------
   --  impl block (§9.1 — inherent implementations, bootstrap subset:
   --  concrete type, fn items with &self/$self). Methods are lowered to
   --  plain fns named `Type$method` with the receiver as first param;
   --  the call-site desugar lives in Kurt.Sema.
   ----------------------------------------------------------------------

   procedure Parse_Impl_Decl
     (C           : in out Cursor;
      Fns         : in out Fn_Vectors.Vector;
      Trait_Impls : in out Trait_Impl_Vectors.Vector;
      Gen_Methods : in out Gen_Method_Vectors.Vector;
      Traits      : Trait_Vectors.Vector)
   is
      Ty_Name     : SU.Unbounded_String;
      Impl_Params : Generic_Param_Vectors.Vector;  --  §9.1 `impl(...)` list
      Is_Generic  : Boolean := False;
      TI : Trait_Impl;        --  populated only for `impl Type as Trait`

      --  Replace the `selftype` placeholder with the impl type, in place; also
      --  resolve `selftype::Item` (§9.3.1) to the impl's concrete associated
      --  type. Associated-type defs must precede methods that use them.
      procedure Subst_Self (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               declare
                  NM : constant String := SU.To_String (T.Name);
               begin
                  if NM = "selftype" then
                     T.Name := Ty_Name;
                  elsif NM'Length > 10
                    and then NM (NM'First .. NM'First + 9) = "selftype::"
                  then
                     declare
                        Item : constant String :=
                          NM (NM'First + 10 .. NM'Last);
                        Res  : Type_Access := null;
                     begin
                        for I in TI.Assoc_Types.First_Index ..
                                 TI.Assoc_Types.Last_Index
                        loop
                           if SU.To_String (TI.Assoc_Types.Element (I).Name)
                                = Item
                           then
                              Res := TI.Assoc_Types.Element (I).Ty;
                           end if;
                        end loop;
                        --  §9.3.1 the impl omitted `type Item = ...` — fall
                        --  back to the trait's declared default, if any.
                        if Res = null then
                           for T in Traits.First_Index .. Traits.Last_Index
                           loop
                              if SU.To_String (Traits.Element (T).Name)
                                   = SU.To_String (TI.Trait_Name)
                              then
                                 declare
                                    TD : Trait_Decl renames Traits.Element (T);
                                 begin
                                    for K in TD.Assoc_Types.First_Index ..
                                             TD.Assoc_Types.Last_Index
                                    loop
                                       if SU.To_String
                                            (TD.Assoc_Types.Element (K).Name)
                                            = Item
                                         and then TD.Assoc_Types.Element (K).Ty
                                                    /= null
                                       then
                                          Res :=
                                            TD.Assoc_Types.Element (K).Ty;
                                       end if;
                                    end loop;
                                 end;
                              end if;
                           end loop;
                        end if;
                        if Res /= null then
                           T.all := Res.all;   --  splice the concrete type in
                        end if;
                     end;
                  end if;
               end;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  Subst_Self (T.Args.Element (I));
               end loop;
            when T_Ref =>
               Subst_Self (T.Target);
            when T_Array =>
               Subst_Self (T.Elem);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  Subst_Self (T.Elems.Element (I));
               end loop;
            when T_Dyn =>
               null;   --  `dyn Trait` names a trait, never `selftype`
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  Subst_Self (T.Fn_Params.Element (I));
               end loop;
               Subst_Self (T.Fn_Ret);
         end case;
      end Subst_Self;
   begin
      Expect (C, Kw_Impl, "'impl'");
      --  §9.1 / §9.4: optional `impl(P [: bound]...)` generic parameter list,
      --  immediately after `impl` and before the target type.
      if C.Cur.Kind = Punct_LParen then
         Advance (C);
         loop
            declare
               P : Generic_Param;
            begin
               P.Name := Take_Ident (C, "impl generic parameter");
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  loop
                     P.Bounds.Append (Take_Ident (C, "bound name"));
                     exit when C.Cur.Kind /= Op_Plus;
                     Advance (C);
                  end loop;
               end if;
               Impl_Params.Append (P);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;  --  trailing comma
         end loop;
         Expect (C, Punct_RParen, "')' to close impl generic parameters");
         Is_Generic := True;
      end if;
      Ty_Name := Take_Ident (C, "impl type name");
      TI.Ty_Name := Ty_Name;
      --  The target's own generic clause `Owner.<P...>` binds the impl
      --  parameters to the owner; the names are recorded in Impl_Params,
      --  so the clause itself is consumed and discarded here.
      declare
         Dummy : Generic_Param_Vectors.Vector;
      begin
         Parse_Opt_Generic_Params_Bounded (C, Dummy);
      end;
      --  §9.4: `impl Type as Trait`. (`impl Type` is an inherent block.)
      if C.Cur.Kind = Kw_As then
         Advance (C);
         TI.Trait_Name := Take_Ident (C, "trait name");
         --  A trait may carry its own generic clause `as Trait.<...>`.
         declare
            Dummy : Generic_Param_Vectors.Vector;
         begin
            Parse_Opt_Generic_Params_Bounded (C, Dummy);
         end;
      end if;
      Expect (C, Punct_LBrace, "'{' to open impl block");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
       if C.Cur.Kind = Kw_Type then
         --  §9.3.1 associated-type definition `type Item = Concrete;`.
         Advance (C);
         declare
            ATy : Assoc_Type;
         begin
            ATy.Name := Take_Ident (C, "associated type name");
            Expect (C, Punct_Eq, "'=' in associated type definition");
            ATy.Ty := Parse_Type (C);
            Expect (C, Punct_Semi, "';' after associated type definition");
            --  Resolve `selftype::Item` style names in the concrete type and
            --  record it for the impl's method specialisation.
            Subst_Self (ATy.Ty);
            TI.Assoc_Types.Append (ATy);
         end;
       elsif C.Cur.Kind = Kw_Const then
         --  §9.3.2 associated-const definition `const NAME: type = expr;`.
         Advance (C);
         declare
            AC : Assoc_Const;
         begin
            AC.Name := Take_Ident (C, "associated const name");
            Expect (C, Punct_Colon, "':' in associated const");
            AC.Ty := Parse_Type (C);
            Expect (C, Punct_Eq, "'=' in associated const definition");
            AC.Val := Parse_Expr (C);
            AC.Has_Val := True;
            Expect (C, Punct_Semi, "';' after associated const");
            TI.Consts.Append (AC);
         end;
       else
         declare
            Fn : Fn_Decl := Parse_Fn_Decl (C);
            MN : constant SU.Unbounded_String := Fn.Header.Name;
         begin
            if Is_Generic then
               --  §9.1/§9.4 generic impl: keep the method as a template.
               --  `selftype` stays a placeholder and the impl parameters are
               --  free; Kurt.Mono specialises it per owner instance. The
               --  bare method name is preserved (mangled to
               --  `Owner$args$method` at instantiation time).
               Gen_Methods.Append
                 ((Owner      => Ty_Name,
                   Trait_Name => TI.Trait_Name,
                   Gen_Params => Impl_Params,
                   Method     => Fn));
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            else
               for I in Fn.Header.Params.First_Index ..
                        Fn.Header.Params.Last_Index
               loop
                  Subst_Self (Fn.Header.Params.Element (I).Ty);
               end loop;
               Subst_Self (Fn.Header.Return_Type);
               --  §9.2.1: the method is namespaced under its type. An
               --  inherent method lowers to `Type$method`; a trait-impl method
               --  to `Type$Trait$method`, so two traits providing the same
               --  method name on one type get distinct symbols and are
               --  disambiguated by `(e as Trait).m()`.
               if SU.Length (TI.Trait_Name) > 0 then
                  Fn.Header.Name := SU.To_Unbounded_String
                    (SU.To_String (Ty_Name) & "$"
                     & SU.To_String (TI.Trait_Name) & "$"
                     & SU.To_String (MN));
               else
                  Fn.Header.Name := SU.To_Unbounded_String
                    (SU.To_String (Ty_Name) & "$" & SU.To_String (MN));
               end if;
               Fns.Append (Fn);
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            end if;
         end;
       end if;
      end loop;
      Expect (C, Punct_RBrace, "'}' to close impl block");
      --  A concrete `impl Type as Trait` registers a dispatch-table
      --  candidate; a generic trait impl provides static methods only
      --  (per-instance dispatch tables are out of scope for the
      --  bootstrap), so it is not registered here.
      --  A concrete `impl Type as Trait` registers a dispatch-table
      --  candidate; an INHERENT `impl Type` (empty Trait_Name) is registered
      --  too so its associated constants are discoverable — consumers that
      --  emit dispatch tables / check trait relationships guard on a
      --  non-empty Trait_Name.
      if not Is_Generic then
         Trait_Impls.Append (TI);
      end if;
   end Parse_Impl_Decl;

   ----------------------------------------------------------------------
   --  trait declaration (§9.3). Bootstrap subset: method signatures and
   --  default methods. The `selftype` placeholder in signatures stays
   --  abstract here; impl blocks substitute the concrete type.
   ----------------------------------------------------------------------

   procedure Parse_Trait_Decl
     (C : in out Cursor; Traits : in out Trait_Vectors.Vector)
   is
      D : Trait_Decl;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Trait, "'trait'");
      D.Name := Take_Ident (C, "trait name");
      --  §9.3.3 supertrait bounds: `with { selftype: Bar + Baz }`.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         Expect (C, Punct_LBrace, "'{' after 'with' on a trait");
         --  Expect `selftype : Trait { '+' Trait }`. (The bootstrap models
         --  only the single `selftype: ...` form.)
         Expect (C, Kw_Selftype, "'selftype' in supertrait bound");
         begin
            Expect (C, Punct_Colon, "':' in supertrait bound");
            loop
               D.Supertraits.Append (Take_Ident (C, "supertrait name"));
               exit when C.Cur.Kind /= Op_Plus;
               Advance (C);
            end loop;
         end;
         Expect (C, Punct_RBrace, "'}' to close supertrait clause");
      end if;
      Expect (C, Punct_LBrace, "'{' to open trait body");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         if C.Cur.Kind = Kw_Type then
            --  §9.3.1 associated type: `type Item [= Default];`.
            Advance (C);
            declare
               ATy : Assoc_Type;
            begin
               ATy.Name := Take_Ident (C, "associated type name");
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  ATy.Ty := Parse_Type (C);   --  default
               end if;
               Expect (C, Punct_Semi, "';' after associated type");
               D.Assoc_Types.Append (ATy);
            end;
         elsif C.Cur.Kind = Kw_Const then
            --  §9.3.2 associated constant: `const NAME: type [= expr];`.
            Advance (C);
            declare
               AC : Assoc_Const;
            begin
               AC.Name := Take_Ident (C, "associated const name");
               Expect (C, Punct_Colon, "':' in associated const");
               AC.Ty := Parse_Type (C);
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  AC.Val := Parse_Expr (C);
                  AC.Has_Val := True;
               end if;
               Expect (C, Punct_Semi, "';' after associated const");
               D.Consts.Append (AC);
            end;
         else
            declare
               M : Trait_Method;
            begin
               --  Parse_Fn_Header consumes `fn name(params) -> ret`.
               Parse_Fn_Header (C, Allow_Unnamed => False, H => M.Sig);
               if C.Cur.Kind = Punct_LBrace then
                  --  §9.3.4 default method: a signature with a body.
                  M.Has_Body := True;
                  Parse_Block_Stmts (C, M.Body_Stmts);
               else
                  Expect (C, Punct_Semi,
                          "';' after trait method signature");
               end if;
               D.Methods.Append (M);
            end;
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}' to close trait body");
      Traits.Append (D);
   end Parse_Trait_Decl;

   ----------------------------------------------------------------------
   --  Top-level dispatch
   ----------------------------------------------------------------------

   --  struct_declaration = "struct" IDENT "{" field { "," field } "}"
   --  field = IDENT ":" type            (§5.5, bootstrap subset)
   function Parse_Struct_Decl (C : in out Cursor) return Struct_Decl is
      D : Struct_Decl;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Struct, "'struct'");
      D.Name := Take_Ident (C, "struct name");
      Parse_Opt_Generic_Params (C, D.Generic_Params);
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               Fld : Struct_Field;
            begin
               --  §5.5.1 field modifiers — recorded on the field.
               while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                  case C.Cur.Kind is
                     when Kw_Pub     => Fld.Is_Pub     := True;
                     when Kw_Mut     => Fld.Is_Mut     := True;
                     when Kw_Airside => Fld.Is_Airside := True;
                     when others     => null;
                  end case;
                  Advance (C);
               end loop;
                if C.Cur.Kind = Op_Question then
                   Fld.Name := SU.To_Unbounded_String ("?");
                   Advance (C);
                else
                   Fld.Name := Take_Ident (C, "field name");
                end if;
               Expect (C, Punct_Colon, "':'");
               Fld.Ty := Parse_Type (C);
               --  §5.5.3 optional default-value expression.
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  Fld.Default := Parse_Expr (C);
               end if;
               D.Fields.Append (Fld);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");

      --  Optional `with` clause (§5.11). Recognised items: `repr(packed)`
      --  (§4.11.4) and `align(N)` (§4.11.5) — bare or inside a with-block;
      --  unrecognised items are skipped (balanced) like the enum parser.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         declare
            procedure Parse_Struct_With_Item is
               Item : constant String := SU.To_String (C.Cur.Lexeme);
            begin
               --  §5.11: with-item words include keywords (`destruct`,
               --  `contract`) and contextual words (`repr`, `align`, ...).
               if not Kurt.Lexer.Is_Word (C.Cur.Kind) then
                  raise Syntax_Error with
                    "expected with-item word, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);
               if Item = "repr" then
                  Expect (C, Punct_LParen, "'('");
                  declare
                     Arg : constant String :=
                       SU.To_String (Take_Ident (C, "repr argument"));
                  begin
                     if Arg = "packed" then
                        D.Repr_Packed := True;
                     elsif Arg = "native" then
                        --  §10.9.2: `repr(native)` is the default layout /
                        --  invocation interface — in a single-unit bootstrap
                        --  it coincides with the default KSA, so no effect.
                        null;
                     else
                        raise Syntax_Error with
                          "unknown `repr(" & Arg & ")` - expected `packed` "
                          & "or `native` (spec 4.11.4) at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                  end;
                  Expect (C, Punct_RParen, "')'");
               elsif Item = "align" then
                  Expect (C, Punct_LParen, "'('");
                  if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
                     raise Syntax_Error with
                       "expected positive integer in align(N) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  D.Align_N := Natural (C.Cur.Int_V);
                  Advance (C);
                  Expect (C, Punct_RParen, "')'");
               elsif Item = "destruct" then
                  --  §8.11 `with destruct [block]`.
                  D.Has_Destruct := True;
                  if C.Cur.Kind = Punct_LBrace then
                     Parse_Block_Stmts (C, D.Destruct_Block);
                  end if;
               elsif Item = "concurrent" then
                  --  §8.10 context-safety markers.
                  Parse_Concurrent_Items
                    (C, D.Conc_Transfer, D.Conc_No_Transfer,
                     D.Conc_Reference, D.Conc_No_Reference);
               else
                  --  Skip a balanced unrecognised item.
                  declare
                     Depth : Natural := 0;
                  begin
                     while not (Depth = 0
                                and then (C.Cur.Kind = Punct_Comma
                                          or else C.Cur.Kind
                                                 = Punct_RBrace
                                          or else C.Cur.Kind
                                                 = Punct_Semi
                                          or else C.Cur.Kind = Tok_EOF))
                     loop
                        if C.Cur.Kind in Punct_LParen | Punct_LBrace then
                           Depth := Depth + 1;
                        elsif C.Cur.Kind in Punct_RParen | Punct_RBrace
                        then
                           Depth := Depth - 1;
                        end if;
                        Advance (C);
                     end loop;
                  end;
               end if;
            end Parse_Struct_With_Item;
         begin
            if C.Cur.Kind = Punct_LBrace then
               --  with_braced (§5.11): the closing brace terminates the
               --  clause; no trailing ';'.
               Advance (C);
               loop
                  exit when C.Cur.Kind = Punct_RBrace;
                  Parse_Struct_With_Item;
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
               end loop;
               Expect (C, Punct_RBrace, "'}'");
            else
               --  with_single (§5.11): a terminating ';' is required
               --  (§5.6: `composite_form, with_single, ';'`).
               Parse_Struct_With_Item;
               Expect (C, Punct_Semi,
                 "';' after single-item `with` clause (spec 5.11)");
            end if;
         end;
      end if;
      return D;
   end Parse_Struct_Decl;

   --  enum_declaration = "enum" IDENT "{" variant { "," variant } "}"
   --  variant = IDENT [ "=" integer_literal ]    (§5.6, unit variants)
   --  Discriminants default to 0,1,2,... continuing from the last value.
   function Parse_Enum_Decl (C : in out Cursor) return Enum_Decl is
      D    : Enum_Decl;
      Next : Long_Long_Integer := 0;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Enum, "'enum'");
      D.Name := Take_Ident (C, "enum name");
      Parse_Opt_Generic_Params (C, D.Generic_Params);
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               V : Enum_Variant;
            begin
               V.Name := Take_Ident (C, "variant name");
               --  Optional payload (§5.6):
               --     struct variant: `{ ident: type, ... }`  (named fields)
               --     tuple  variant: `{ [pub|mut|airside]* type, ... }`
               --                                          (positional)
               --  Disambiguated by the first non-modifier token sequence:
               --  `ident ':'` -> struct, otherwise -> tuple.
               if C.Cur.Kind = Punct_LBrace then
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     --  Skip leading modifiers to peek the first payload
                     --  token (modifiers themselves are not stored in the
                     --  bootstrap field model).
                     while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                        Advance (C);
                     end loop;
                     declare
                        Is_Struct_Variant : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Colon;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              Fld : Struct_Field;
                           begin
                              if Is_Struct_Variant then
                                 if C.Cur.Kind = Op_Question then
                                    Fld.Name := SU.To_Unbounded_String ("?");
                                    Advance (C);
                                 else
                                    Fld.Name := Take_Ident (C, "payload field name");
                                 end if;
                                 Expect (C, Punct_Colon, "':'");
                                 Fld.Ty := Parse_Type (C);
                              else
                                 --  Synthetic positional name "0", "1", ...
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    Fld.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Fld.Ty := Parse_Type (C);
                                 Idx := Idx + 1;
                              end if;
                              V.Payload.Append (Fld);
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                           while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside
                           loop
                              Advance (C);
                           end loop;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
               end if;
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  if C.Cur.Kind = Tok_Hash_Wild then
                     --  `= #wild#` or `= #wild#(V)`: this variant covers
                     --  all otherwise-unlisted discriminant values, with
                     --  optional canonical value V (§4.5, §5.6).
                     Advance (C);
                     V.Is_Wild := True;
                     if C.Cur.Kind = Punct_LParen then
                        Advance (C);
                        declare
                           Neg : Boolean := False;
                        begin
                           if C.Cur.Kind = Op_Minus then
                              Neg := True;
                              Advance (C);
                           end if;
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer in #wild#(...), got "
                                & Image (C.Cur)
                                & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                           V.Value :=
                             (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                        end;
                        V.Wild_Canon := True;
                        Advance (C);
                        Expect (C, Punct_RParen, "')'");
                     else
                        --  bare `= #wild#`: discriminant via occupied-set pass.
                        V.Auto_Disc := True;
                     end if;
                  elsif C.Cur.Kind = Tok_Int_Lit
                    or else C.Cur.Kind = Op_Minus
                  then
                     --  §4.11.3: a negative explicit value selects a
                     --  signed discriminant type.
                     declare
                        Neg : Boolean := False;
                     begin
                        if C.Cur.Kind = Op_Minus then
                           Neg := True;
                           Advance (C);
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer after '-' in "
                                & "discriminant value, got "
                                & Image (C.Cur) & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                        end if;
                        Next := (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                     end;
                     Advance (C);
                     V.Value := Next;          --  explicit value
                  else
                     raise Syntax_Error with
                       "expected discriminant value after '=', got "
                       & Image (C.Cur)
                       & " at line" & Positive'Image (C.Cur.Line);
                  end if;
               else
                  V.Auto_Disc := True;         --  no `=`: occupied-set pass
               end if;
               D.Variants.Append (V);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");

      --  §5.7 automatic discriminant assignment (occupied-set algorithm):
      --  S = all explicit values + `#wild#(V)` canonical values; counter c=0;
      --  each variant lacking an explicit value (incl. bare `#wild#`) takes the
      --  smallest value >= c not in S, which is then added to S and c bumped.
      declare
         function In_S (Val : Long_Long_Integer) return Boolean is
         begin
            for I in D.Variants.First_Index .. D.Variants.Last_Index loop
               if not D.Variants.Element (I).Auto_Disc
                 and then D.Variants.Element (I).Value = Val
               then
                  return True;     --  explicit or already-assigned / canonical
               end if;
            end loop;
            return False;
         end In_S;
         Cc : Long_Long_Integer := 0;
      begin
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            if D.Variants.Element (I).Auto_Disc then
               while In_S (Cc) loop Cc := Cc + 1; end loop;
               declare
                  V : Enum_Variant := D.Variants.Element (I);
               begin
                  V.Value := Cc;
                  V.Auto_Disc := False;   --  now part of S for later variants
                  D.Variants.Replace_Element (I, V);
               end;
               Cc := Cc + 1;
            end if;
         end loop;
      end;

      --  Optional `with` clause (§5.10).
      --     `with contract`                       — bare contract clause
      --     `with { item, item, ... }`              — with-block (§4.5, §5.10)
      --  Items recognised by the bootstrap: `contract [-> type]`, `discrim
      --  (type)`. Other items (repr, align, ...) are parsed-and-discarded.
      if C.Cur.Kind = Kw_With then
       declare
         Is_Braced : Boolean := False;
       begin
         Advance (C);
         if C.Cur.Kind = Punct_LBrace then
            Is_Braced := True;
            Advance (C);
            loop
               exit when C.Cur.Kind = Punct_RBrace;
               if Kurt.Lexer.Is_Word (C.Cur.Kind) then
                  declare
                     Item : constant String := SU.To_String (C.Cur.Lexeme);
                  begin
                     Advance (C);
                     if Item = "contract" then
                        D.Is_Contract := True;
                        --  Optional `-> inverted_pair_type` (§7.2). The
                        --  inverted pair is parsed and discarded; `!verdict`
                        --  is not yet activated.
                        if C.Cur.Kind = Punct_Arrow then
                           Advance (C);
                           declare
                              Ignore : constant Type_Access := Parse_Type (C);
                              pragma Unreferenced (Ignore);
                           begin null; end;
                        end if;
                     elsif Item = "discrim" then
                        --  §4.11.3: `with discrim(T)` fixes the
                        --  discriminant type (validated by sema).
                        Expect (C, Punct_LParen, "'('");
                        D.Discrim_Ty := Parse_Type (C);
                        Expect (C, Punct_RParen, "')'");
                     elsif Item = "destruct" then
                        --  §8.11 `with destruct [block]`.
                        D.Has_Destruct := True;
                        if C.Cur.Kind = Punct_LBrace then
                           Parse_Block_Stmts (C, D.Destruct_Block);
                        end if;
                     elsif Item = "concurrent" then
                        --  §8.10 context-safety markers.
                        Parse_Concurrent_Items
                          (C, D.Conc_Transfer, D.Conc_No_Transfer,
                           D.Conc_Reference, D.Conc_No_Reference);
                     else
                        --  Unrecognised with-item: skip balanced tokens up
                        --  to the next ',' or '}'. The bootstrap does not
                        --  semantically use repr/align/lifetime/...
                        declare
                           Depth : Natural := 0;
                        begin
                           while not (Depth = 0
                                      and then (C.Cur.Kind = Punct_Comma
                                                or else C.Cur.Kind
                                                       = Punct_RBrace))
                           loop
                              if C.Cur.Kind in Punct_LParen
                                | Punct_LBrace
                              then
                                 Depth := Depth + 1;
                              elsif C.Cur.Kind in Punct_RParen
                                | Punct_RBrace
                              then
                                 Depth := Depth - 1;
                              end if;
                              Advance (C);
                           end loop;
                        end;
                     end if;
                  end;
               else
                  raise Syntax_Error with
                    "expected with-item word, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               exit when C.Cur.Kind /= Punct_Comma;
               Advance (C);
            end loop;
            Expect (C, Punct_RBrace, "'}'");
         elsif C.Cur.Kind = Kw_Contract then
            D.Is_Contract := True;
            Advance (C);
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "discrim"
         then
            --  Bare form `with discrim(T)` (§4.11.3 example form).
            Advance (C);
            Expect (C, Punct_LParen, "'('");
            D.Discrim_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif C.Cur.Kind = Kw_Destruct then
            --  §8.11 bare `with destruct [block]`.
            Advance (C);
            D.Has_Destruct := True;
            if C.Cur.Kind = Punct_LBrace then
               Parse_Block_Stmts (C, D.Destruct_Block);
               Is_Braced := True;   --  the block terminates it; no ';'
            end if;
         else
            raise Syntax_Error with
              "expected 'contract' or '{' after 'with', got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
         --  §5.7 / §5.11: `with_single` requires a terminating ';';
         --  `with_braced` is terminated by its closing brace.
         if not Is_Braced then
            Expect (C, Punct_Semi,
              "';' after single-item `with` clause (spec 5.11)");
         end if;
       end;
      end if;
      return D;
   end Parse_Enum_Decl;

   --  §5.3 `const NAME: T = expr ;` — the type annotation is mandatory.
   function Parse_Const_Decl (C : in out Cursor) return Const_Decl is
      D : Const_Decl;
   begin
      Expect (C, Kw_Const, "'const'");
      D.Name := Take_Ident (C, "const name");
      Expect (C, Punct_Colon, "':' (const type annotation is mandatory, "
              & "spec 5.3)");
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      D.Init := Parse_Expr (C);
      Expect (C, Punct_Semi, "';' after const declaration");
      return D;
   end Parse_Const_Decl;

   --  §5.4 `static [mut] NAME: T = expr ;`.
   function Parse_Static_Decl (C : in out Cursor) return Static_Decl is
      D : Static_Decl;
   begin
      Advance (C);   --  consume the `static` identifier-word
      if C.Cur.Kind = Kw_Mut then
         D.Is_Mut := True;
         Advance (C);
      end if;
      D.Name := Take_Ident (C, "static name");
      Expect (C, Punct_Colon, "':' (static type annotation)");
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      D.Init := Parse_Expr (C);
      Expect (C, Punct_Semi, "';' after static declaration");
      return D;
   end Parse_Static_Decl;

   procedure Merge_Unit
     (Into : in out Translation_Unit; From : Translation_Unit) is
   begin
      Into.Fns.Append (From.Fns);
      Into.Dyns.Append (From.Dyns);
      Into.Structs.Append (From.Structs);
      Into.Enums.Append (From.Enums);
      Into.Traits.Append (From.Traits);
      Into.Trait_Impls.Append (From.Trait_Impls);
      Into.Consts.Append (From.Consts);
      Into.Statics.Append (From.Statics);
      Into.Gen_Methods.Append (From.Gen_Methods);
      Into.Gen_Fns.Append (From.Gen_Fns);
      Into.Top_Asm.Append (From.Top_Asm);
      --  §7.10.1 at most one trap handler across the translation unit.
      if From.Has_Trap_Handler then
         if Into.Has_Trap_Handler then
            raise Syntax_Error with
              "multiple @trap handlers across the translation unit (§7.10.1)";
         end if;
         Into.Has_Trap_Handler := True;
         Into.Trap_Handler := From.Trap_Handler;
      end if;
   end Merge_Unit;

   ----------------------------------------------------------------------
   --  §10.3 namespace mangling (see kurt-parser.ads for the design note).
   ----------------------------------------------------------------------

   function Snapshot (U : Translation_Unit) return Rename_From is
      function P1 (N : Natural) return Positive is (Positive (N + 1));
   begin
      return
        (Fns         => P1 (Natural (U.Fns.Length)),
         Gen_Fns     => P1 (Natural (U.Gen_Fns.Length)),
         Structs     => P1 (Natural (U.Structs.Length)),
         Enums       => P1 (Natural (U.Enums.Length)),
         Traits      => P1 (Natural (U.Traits.Length)),
         Trait_Impls => P1 (Natural (U.Trait_Impls.Length)),
         Consts      => P1 (Natural (U.Consts.Length)),
         Statics     => P1 (Natural (U.Statics.Length)),
         Gen_Methods => P1 (Natural (U.Gen_Methods.Length)));
   end Snapshot;

   procedure Apply_Namespace
     (U           : in out Translation_Unit;
      NS_Prefix   : String;
      From        : Rename_From := (others => 1);
      Extra_Names : Path_Segments.Vector := Path_Segments.Empty_Vector)
   is
      Names : Path_Segments.Vector := Extra_Names;

      function In_Names (Nm : String) return Boolean is
      begin
         for I in Names.First_Index .. Names.Last_Index loop
            if SU.To_String (Names.Element (I)) = Nm then
               return True;
            end if;
         end loop;
         return False;
      end In_Names;

      --  "area" -> "NS$area" (whole name declared); "point$area" ->
      --  "NS$point$area" (owner segment, up to the first '$', declared).
      function Mangle_Value (Nm : String) return String is
         Dollar : constant Natural := Ada.Strings.Fixed.Index (Nm, "$");
         Head   : constant String :=
           (if Dollar = 0 then Nm else Nm (Nm'First .. Dollar - 1));
      begin
         if In_Names (Head) then
            return NS_Prefix & "$" & Nm;
         end if;
         return Nm;
      end Mangle_Value;

      --  "point" -> "NS$point"; "selftype::Item" untouched (selftype is never a
      --  local declared name); "point::Assoc" -> "NS$point::Assoc".
      function Mangle_Type_Name (Nm : String) return String is
         Sep : constant Natural := Ada.Strings.Fixed.Index (Nm, "::");
      begin
         if Sep = 0 then
            if In_Names (Nm) then
               return NS_Prefix & "$" & Nm;
            end if;
            return Nm;
         end if;
         declare
            Head : constant String := Nm (Nm'First .. Sep - 1);
            Rest : constant String := Nm (Sep .. Nm'Last);
         begin
            if In_Names (Head) then
               return NS_Prefix & "$" & Head & Rest;
            end if;
            return Nm;
         end;
      end Mangle_Type_Name;

      procedure RT (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               T.Name := SU.To_Unbounded_String
                 (Mangle_Type_Name (SU.To_String (T.Name)));
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  RT (T.Args.Element (I));
               end loop;
            when T_Ref =>
               RT (T.Target);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  RT (T.Elems.Element (I));
               end loop;
            when T_Array =>
               RT (T.Elem);
            when T_Dyn =>
               T.Trait_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (T.Trait_Name)));
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  RT (T.Fn_Params.Element (I));
               end loop;
               RT (T.Fn_Ret);
         end case;
      end RT;

      procedure RE (E : Expr_Access);
      procedure RS (S : Stmt_Access);

      procedure RBlk (V : Stmt_Vectors.Vector) is
      begin
         for I in V.First_Index .. V.Last_Index loop
            RS (V.Element (I));
         end loop;
      end RBlk;

      procedure RPat (P : in out Pattern) is
      begin
         if not P.Path.Is_Empty then
            declare
               H : constant String := SU.To_String (P.Path.First_Element);
            begin
               if In_Names (H) then
                  P.Path.Replace_Element
                    (P.Path.First_Index,
                     SU.To_Unbounded_String (NS_Prefix & "$" & H));
               end if;
            end;
         end if;
      end RPat;

      procedure RE (E : Expr_Access) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_String_Lit
               | E_Uninit =>
               null;
            when E_Path =>
               if Natural (E.Segments.Length) = 1 then
                  E.Segments.Replace_Element
                    (E.Segments.First_Index,
                     SU.To_Unbounded_String
                       (Mangle_Value
                          (SU.To_String (E.Segments.First_Element))));
               elsif Natural (E.Segments.Length) >= 2 then
                  declare
                     H : constant String :=
                       SU.To_String (E.Segments.First_Element);
                  begin
                     if In_Names (H) then
                        E.Segments.Replace_Element
                          (E.Segments.First_Index,
                           SU.To_Unbounded_String (NS_Prefix & "$" & H));
                     end if;
                  end;
               end if;
               for I in E.P_Type_Args.First_Index ..
                        E.P_Type_Args.Last_Index loop
                  RT (E.P_Type_Args.Element (I));
               end loop;
            when E_Field =>
               RE (E.F_Recv);
            when E_Call =>
               RE (E.C_Callee);
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  RE (E.C_Args.Element (I));
               end loop;
            when E_If =>
               RE (E.I_Cond); RE (E.I_Then); RE (E.I_Else);
            when E_Binary =>
               RE (E.B_Lhs); RE (E.B_Rhs);
            when E_Deref =>
               RE (E.D_Inner);
            when E_Struct_Lit =>
               E.SL_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.SL_Name)));
               for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index
               loop
                  RE (E.SL_Fields.Element (I).Val);
               end loop;
            when E_Variant_New =>
               E.VN_Enum := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.VN_Enum)));
               for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index
               loop
                  RE (E.VN_Fields.Element (I).Val);
               end loop;
            when E_Match =>
               RE (E.M_Scrut);
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  declare
                     A : Match_Arm := E.M_Arms.Element (I);
                  begin
                     RPat (A.Pat);
                     RE (A.Guard);
                     RE (A.Arm_Body);
                     E.M_Arms.Replace_Element (I, A);
                  end;
               end loop;
            when E_Cast =>
               RE (E.Cast_Inner);
               RT (E.Cast_Ty);
            when E_Unary =>
               RE (E.U_Operand);
            when E_Tuple_Lit =>
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
                  RE (E.TL_Elems.Element (I));
               end loop;
            when E_Question =>
               RE (E.Q_Inner);
            when E_Ref =>
               RE (E.Rf_Place);
            when E_CAS =>
               RE (E.CAS_Tgt); RE (E.CAS_Exp); RE (E.CAS_New);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  RE (E.AL_Elems.Element (I));
               end loop;
            when E_Dyn_Cast =>
               RE (E.DC_Inner);
               E.DC_Conc := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.DC_Conc)));
               E.DC_Trait := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.DC_Trait)));
            when E_Slice_Cast =>
               RE (E.SC_Inner);
            when E_Type_Intrinsic =>
               RT (E.TI_Ty);
            when E_Closure =>
               for I in E.Clo_Params.First_Index .. E.Clo_Params.Last_Index
               loop
                  RT (E.Clo_Params.Element (I).Ty);
               end loop;
               RT (E.Clo_Ret);
               RBlk (E.Clo_Body);
            when E_Destruct =>
               RE (E.DT_Inner);
         end case;
      end RE;

      procedure RS (S : Stmt_Access) is
      begin
         if S = null then
            return;
         end if;
         case S.Kind is
            when S_Return => RE (S.R_Val);
            when S_Expr    => RE (S.E_Val);
            when S_Airside_Block => RBlk (S.A_Stmts);
            when S_Let | S_Mut =>
               RT (S.L_Ty);
               RE (S.L_Init);
               if S.L_Is_Refut then
                  RPat (S.L_Refut_Pat);
               end if;
               RBlk (S.L_Else);
            when S_Assign =>
               RE (S.Asn_Lhs); RE (S.Asn_Rhs);
            when S_While =>
               RE (S.W_Cond);
               RBlk (S.W_Body);
               RBlk (S.W_Then);
               if S.W_Is_Let then
                  RPat (S.W_Let_Pat);
               end if;
            when S_If =>
               RE (S.SI_Cond);
               RBlk (S.SI_Then);
               RBlk (S.SI_Else);
               if S.SI_Is_Let then
                  RPat (S.SI_Let_Pat);
               end if;
            when S_Extract =>
               RE (S.X_Expr);
               RBlk (S.X_Else);
            when S_Break => RE (S.Brk_Val);
            when S_Continue => null;
            when S_Express => RE (S.Xp_Val);
            when S_Fence => null;
            when S_Trap => null;
            when S_Asm =>
               for I in S.Asm_In_Exprs.First_Index ..
                        S.Asm_In_Exprs.Last_Index loop
                  RE (S.Asm_In_Exprs.Element (I));
               end loop;
         end case;
      end RS;

      procedure RHeader (H : in out Fn_Header) is
      begin
         H.Name := SU.To_Unbounded_String
           (Mangle_Value (SU.To_String (H.Name)));
         for I in H.Params.First_Index .. H.Params.Last_Index loop
            RT (H.Params.Element (I).Ty);
         end loop;
         RT (H.Return_Type);
      end RHeader;
   begin
      --  1. Collect the bare top-level names U itself declares.
      for I in From.Structs .. U.Structs.Last_Index loop
         Names.Append (U.Structs.Element (I).Name);
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         Names.Append (U.Enums.Element (I).Name);
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         Names.Append (U.Traits.Element (I).Name);
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         Names.Append (U.Consts.Element (I).Name);
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         Names.Append (U.Statics.Element (I).Name);
      end loop;
      for I in From.Fns .. U.Fns.Last_Index loop
         if Ada.Strings.Fixed.Index
              (SU.To_String (U.Fns.Element (I).Header.Name), "$") = 0
         then
            Names.Append (U.Fns.Element (I).Header.Name);
         end if;
      end loop;
      for I in From.Gen_Fns .. U.Gen_Fns.Last_Index loop
         Names.Append (U.Gen_Fns.Element (I).Header.Name);
      end loop;
      for I in From.Gen_Methods .. U.Gen_Methods.Last_Index loop
         Names.Append (U.Gen_Methods.Element (I).Owner);
      end loop;

      --  2. Rename the declaration labels themselves.
      for I in From.Structs .. U.Structs.Last_Index loop
         declare
            D : Struct_Decl := U.Structs.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Structs.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         declare
            D : Enum_Decl := U.Enums.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Enums.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         declare
            D : Trait_Decl := U.Traits.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Traits.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         declare
            D : Const_Decl := U.Consts.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Consts.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         declare
            D : Static_Decl := U.Statics.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Statics.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Trait_Impls .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl := U.Trait_Impls.Element (I);
         begin
            TI.Ty_Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (TI.Ty_Name)));
            TI.Trait_Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (TI.Trait_Name)));
            U.Trait_Impls.Replace_Element (I, TI);
         end;
      end loop;
      for I in From.Gen_Methods .. U.Gen_Methods.Last_Index loop
         declare
            GM : Gen_Method := U.Gen_Methods.Element (I);
         begin
            GM.Owner := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (GM.Owner)));
            if SU.Length (GM.Trait_Name) > 0 then
               GM.Trait_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (GM.Trait_Name)));
            end if;
            RHeader (GM.Method.Header);
            RBlk (GM.Method.Body_Stmts);
            U.Gen_Methods.Replace_Element (I, GM);
         end;
      end loop;

      --  3. Walk every reachable type/expr/stmt and rename references.
      for I in From.Fns .. U.Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Fns.Element (I);
         begin
            RHeader (F.Header);
            RBlk (F.Body_Stmts);
            U.Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in From.Gen_Fns .. U.Gen_Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Gen_Fns.Element (I);
         begin
            RHeader (F.Header);
            RBlk (F.Body_Stmts);
            U.Gen_Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in From.Structs .. U.Structs.Last_Index loop
         declare
            D : constant Struct_Decl := U.Structs.Element (I);
         begin
            for K in D.Fields.First_Index .. D.Fields.Last_Index loop
               RT (D.Fields.Element (K).Ty);
               RE (D.Fields.Element (K).Default);
            end loop;
            RBlk (D.Destruct_Block);
         end;
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         declare
            D : constant Enum_Decl := U.Enums.Element (I);
         begin
            for V in D.Variants.First_Index .. D.Variants.Last_Index loop
               for K in D.Variants.Element (V).Payload.First_Index ..
                        D.Variants.Element (V).Payload.Last_Index loop
                  RT (D.Variants.Element (V).Payload.Element (K).Ty);
                  RE (D.Variants.Element (V).Payload.Element (K).Default);
               end loop;
            end loop;
            RT (D.Discrim_Ty);
            RBlk (D.Destruct_Block);
         end;
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         RT (U.Consts.Element (I).Ty);
         RE (U.Consts.Element (I).Init);
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         RT (U.Statics.Element (I).Ty);
         RE (U.Statics.Element (I).Init);
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         declare
            D : Trait_Decl := U.Traits.Element (I);
         begin
            for K in D.Methods.First_Index .. D.Methods.Last_Index loop
               declare
                  M : Trait_Method := D.Methods.Element (K);
               begin
                  RHeader (M.Sig);
                  RBlk (M.Body_Stmts);
                  D.Methods.Replace_Element (K, M);
               end;
            end loop;
            for K in D.Consts.First_Index .. D.Consts.Last_Index loop
               RT (D.Consts.Element (K).Ty);
               RE (D.Consts.Element (K).Val);
            end loop;
            for K in D.Assoc_Types.First_Index ..
                     D.Assoc_Types.Last_Index loop
               RT (D.Assoc_Types.Element (K).Ty);
            end loop;
            U.Traits.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Trait_Impls .. U.Trait_Impls.Last_Index loop
         declare
            TI : constant Trait_Impl := U.Trait_Impls.Element (I);
         begin
            for K in TI.Consts.First_Index .. TI.Consts.Last_Index loop
               RT (TI.Consts.Element (K).Ty);
               RE (TI.Consts.Element (K).Val);
            end loop;
            for K in TI.Assoc_Types.First_Index ..
                     TI.Assoc_Types.Last_Index loop
               RT (TI.Assoc_Types.Element (K).Ty);
            end loop;
         end;
      end loop;
      RBlk (U.Trap_Handler);
   end Apply_Namespace;

   ----------------------------------------------------------------------

   procedure Resolve_Aliases
     (U              : in out Translation_Unit;
      Alias_Names    : Path_Segments.Vector;
      Alias_Prefixes : Path_Segments.Vector)
   is
      --  Find the mangled prefix bound to a local `@add ... as alias;` name;
      --  "" (empty) if Head is not a known alias.
      function Prefix_Of (Head : String) return String is
      begin
         for I in Alias_Names.First_Index .. Alias_Names.Last_Index loop
            if SU.To_String (Alias_Names.Element (I)) = Head then
               return SU.To_String (Alias_Prefixes.Element (I));
            end if;
         end loop;
         return "";
      end Prefix_Of;

      --  §10.3: the target of an `alias::item` reference shall be `pub` in
      --  the imported unit. Scans U's own (already-merged, already-mangled)
      --  declaration vectors for Mangled; a name absent from all of them
      --  (e.g. an enum variant, which isn't independently `pub`-tracked) is
      --  not flagged here — ordinary name resolution catches a bad access.
      function Check_Pub (Mangled : String) return Boolean is
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            if SU.To_String (U.Fns.Element (I).Header.Name) = Mangled then
               return U.Fns.Element (I).Header.Is_Pub;
            end if;
         end loop;
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            if SU.To_String (U.Structs.Element (I).Name) = Mangled then
               return U.Structs.Element (I).Is_Pub;
            end if;
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if SU.To_String (U.Enums.Element (I).Name) = Mangled then
               return U.Enums.Element (I).Is_Pub;
            end if;
         end loop;
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            if SU.To_String (U.Traits.Element (I).Name) = Mangled then
               return U.Traits.Element (I).Is_Pub;
            end if;
         end loop;
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            if SU.To_String (U.Consts.Element (I).Name) = Mangled then
               return U.Consts.Element (I).Is_Pub;
            end if;
         end loop;
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            if SU.To_String (U.Statics.Element (I).Name) = Mangled then
               return U.Statics.Element (I).Is_Pub;
            end if;
         end loop;
         return True;   --  not a tracked top-level decl; let sema judge it
      end Check_Pub;

      --  Collapse a >=2-segment path whose first segment is a known alias:
      --  [alias, Head, Rest...] -> [prefix & "$" & Head, Rest...].
      procedure Collapse (Segs : in out Path_Segments.Vector) is
         Pfx : constant String :=
           Prefix_Of (SU.To_String (Segs.First_Element));
      begin
         if Pfx = "" or else Natural (Segs.Length) < 2 then
            return;
         end if;
         declare
            Second  : constant String :=
              SU.To_String (Segs.Element (Segs.First_Index + 1));
            Mangled : constant String := Pfx & "$" & Second;
            Tail    : Path_Segments.Vector;
         begin
            for I in Segs.First_Index + 2 .. Segs.Last_Index loop
               Tail.Append (Segs.Element (I));
            end loop;
            if not Check_Pub (Mangled) then
               raise Syntax_Error with
                 "'" & Second & "' is not `pub` in the imported unit "
                 & "(spec 10.3)";
            end if;
            Segs.Clear;
            Segs.Append (SU.To_Unbounded_String (Mangled));
            Segs.Append (Tail);
         end;
      end Collapse;

      --  "alias::Item" -> "prefix$Item" (checking `pub`); anything else
      --  (no "::", or an unrecognised head) is returned unchanged. Used for
      --  compound names stored as a single string (qualified struct-literal
      --  `SL_Name`, qualified type names).
      function Mangle_Compound (Nm : String) return String is
         Sep : constant Natural := Ada.Strings.Fixed.Index (Nm, "::");
      begin
         if Sep = 0 then
            return Nm;
         end if;
         declare
            Head : constant String := Nm (Nm'First .. Sep - 1);
            Rest : constant String := Nm (Sep + 2 .. Nm'Last);
            Pfx  : constant String := Prefix_Of (Head);
         begin
            if Pfx = "" then
               return Nm;
            end if;
            declare
               Mangled : constant String := Pfx & "$" & Rest;
            begin
               if not Check_Pub (Mangled) then
                  raise Syntax_Error with
                    "'" & Rest & "' is not `pub` in the imported unit '"
                    & Head & "' (spec 10.3)";
               end if;
               return Mangled;
            end;
         end;
      end Mangle_Compound;

      procedure RT (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               declare
                  Nm : constant String := SU.To_String (T.Name);
               begin
                  T.Name := SU.To_Unbounded_String (Mangle_Compound (Nm));
               end;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  RT (T.Args.Element (I));
               end loop;
            when T_Ref =>
               RT (T.Target);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  RT (T.Elems.Element (I));
               end loop;
            when T_Array =>
               RT (T.Elem);
            when T_Dyn =>
               null;
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index
               loop
                  RT (T.Fn_Params.Element (I));
               end loop;
               RT (T.Fn_Ret);
         end case;
      end RT;

      procedure RE (E : Expr_Access);
      procedure RS (S : Stmt_Access);

      procedure RBlk (V : Stmt_Vectors.Vector) is
      begin
         for I in V.First_Index .. V.Last_Index loop
            RS (V.Element (I));
         end loop;
      end RBlk;

      procedure RE (E : Expr_Access) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_String_Lit
               | E_Uninit =>
               null;
            when E_Path =>
               if Natural (E.Segments.Length) >= 2 then
                  Collapse (E.Segments);
               end if;
               for I in E.P_Type_Args.First_Index ..
                        E.P_Type_Args.Last_Index loop
                  RT (E.P_Type_Args.Element (I));
               end loop;
            when E_Field =>
               RE (E.F_Recv);
            when E_Call =>
               RE (E.C_Callee);
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  RE (E.C_Args.Element (I));
               end loop;
            when E_If =>
               RE (E.I_Cond); RE (E.I_Then); RE (E.I_Else);
            when E_Binary =>
               RE (E.B_Lhs); RE (E.B_Rhs);
            when E_Deref =>
               RE (E.D_Inner);
            when E_Struct_Lit =>
               E.SL_Name := SU.To_Unbounded_String
                 (Mangle_Compound (SU.To_String (E.SL_Name)));
               for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index
               loop
                  RE (E.SL_Fields.Element (I).Val);
               end loop;
            when E_Variant_New =>
               for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index
               loop
                  RE (E.VN_Fields.Element (I).Val);
               end loop;
            when E_Match =>
               RE (E.M_Scrut);
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  declare
                     A : Match_Arm := E.M_Arms.Element (I);
                  begin
                     if Natural (A.Pat.Path.Length) >= 2 then
                        Collapse (A.Pat.Path);
                     end if;
                     RE (A.Guard);
                     RE (A.Arm_Body);
                     E.M_Arms.Replace_Element (I, A);
                  end;
               end loop;
            when E_Cast =>
               RE (E.Cast_Inner);
               RT (E.Cast_Ty);
            when E_Unary =>
               RE (E.U_Operand);
            when E_Tuple_Lit =>
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
                  RE (E.TL_Elems.Element (I));
               end loop;
            when E_Question =>
               RE (E.Q_Inner);
            when E_Ref =>
               RE (E.Rf_Place);
            when E_CAS =>
               RE (E.CAS_Tgt); RE (E.CAS_Exp); RE (E.CAS_New);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  RE (E.AL_Elems.Element (I));
               end loop;
            when E_Dyn_Cast =>
               RE (E.DC_Inner);
            when E_Slice_Cast =>
               RE (E.SC_Inner);
            when E_Type_Intrinsic =>
               RT (E.TI_Ty);
            when E_Closure =>
               for I in E.Clo_Params.First_Index .. E.Clo_Params.Last_Index
               loop
                  RT (E.Clo_Params.Element (I).Ty);
               end loop;
               RT (E.Clo_Ret);
               RBlk (E.Clo_Body);
            when E_Destruct =>
               RE (E.DT_Inner);
         end case;
      end RE;

      procedure RS (S : Stmt_Access) is
      begin
         if S = null then
            return;
         end if;
         case S.Kind is
            when S_Return => RE (S.R_Val);
            when S_Expr    => RE (S.E_Val);
            when S_Airside_Block => RBlk (S.A_Stmts);
            when S_Let | S_Mut =>
               RT (S.L_Ty);
               RE (S.L_Init);
               if S.L_Is_Refut and then Natural (S.L_Refut_Pat.Path.Length)
                                          >= 2
               then
                  Collapse (S.L_Refut_Pat.Path);
               end if;
               RBlk (S.L_Else);
            when S_Assign =>
               RE (S.Asn_Lhs); RE (S.Asn_Rhs);
            when S_While =>
               RE (S.W_Cond);
               RBlk (S.W_Body);
               RBlk (S.W_Then);
               if S.W_Is_Let and then Natural (S.W_Let_Pat.Path.Length) >= 2
               then
                  Collapse (S.W_Let_Pat.Path);
               end if;
            when S_If =>
               RE (S.SI_Cond);
               RBlk (S.SI_Then);
               RBlk (S.SI_Else);
               if S.SI_Is_Let and then Natural (S.SI_Let_Pat.Path.Length)
                                         >= 2
               then
                  Collapse (S.SI_Let_Pat.Path);
               end if;
            when S_Extract =>
               RE (S.X_Expr);
               RBlk (S.X_Else);
            when S_Break => RE (S.Brk_Val);
            when S_Continue => null;
            when S_Express => RE (S.Xp_Val);
            when S_Fence => null;
            when S_Trap => null;
            when S_Asm =>
               for I in S.Asm_In_Exprs.First_Index ..
                        S.Asm_In_Exprs.Last_Index loop
                  RE (S.Asm_In_Exprs.Element (I));
               end loop;
         end case;
      end RS;
   begin
      if Alias_Names.Is_Empty then
         return;
      end if;
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Fns.Element (I);
         begin
            for K in F.Header.Params.First_Index ..
                     F.Header.Params.Last_Index loop
               RT (F.Header.Params.Element (K).Ty);
            end loop;
            RT (F.Header.Return_Type);
            RBlk (F.Body_Stmts);
            U.Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Gen_Fns.Element (I);
         begin
            for K in F.Header.Params.First_Index ..
                     F.Header.Params.Last_Index loop
               RT (F.Header.Params.Element (K).Ty);
            end loop;
            RT (F.Header.Return_Type);
            RBlk (F.Body_Stmts);
            U.Gen_Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            D : constant Struct_Decl := U.Structs.Element (I);
         begin
            for K in D.Fields.First_Index .. D.Fields.Last_Index loop
               RT (D.Fields.Element (K).Ty);
               RE (D.Fields.Element (K).Default);
            end loop;
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            D : constant Enum_Decl := U.Enums.Element (I);
         begin
            for V in D.Variants.First_Index .. D.Variants.Last_Index loop
               for K in D.Variants.Element (V).Payload.First_Index ..
                        D.Variants.Element (V).Payload.Last_Index loop
                  RT (D.Variants.Element (V).Payload.Element (K).Ty);
               end loop;
            end loop;
         end;
      end loop;
      for I in U.Consts.First_Index .. U.Consts.Last_Index loop
         RT (U.Consts.Element (I).Ty);
         RE (U.Consts.Element (I).Init);
      end loop;
      for I in U.Statics.First_Index .. U.Statics.Last_Index loop
         RT (U.Statics.Element (I).Ty);
         RE (U.Statics.Element (I).Init);
      end loop;
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : constant Trait_Impl := U.Trait_Impls.Element (I);
         begin
            for K in TI.Consts.First_Index .. TI.Consts.Last_Index loop
               RT (TI.Consts.Element (K).Ty);
               RE (TI.Consts.Element (K).Val);
            end loop;
         end;
      end loop;
      RBlk (U.Trap_Handler);
   end Resolve_Aliases;

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit
   is
      C : Cursor := (Lex => Lex'Unchecked_Access, others => <>);
      U : Translation_Unit;
      --  §10.6 `module name { … }` nesting depth. A module is a transparent
      --  namespace wrapper in the bootstrap: its declarations are flattened
      --  into the unit (qualified `name::item` access resolves by last
      --  segment, as for `@dyn` aliases). `super`/`srcroot` path roots and
      --  strict module-scoped name resolution are deferred.
      Module_Depth : Natural := 0;
   begin
      Advance (C);
      while C.Cur.Kind /= Tok_EOF loop
         --  §5.16: skip any `@[ ... ]@` annotations preceding a declaration.
         --  Their content is opaque and unrecognised ones are ignored.
         while C.Cur.Kind = Dir_At_LBracket loop
            Advance (C);
            while C.Cur.Kind /= Dir_At_RBracket loop
               if C.Cur.Kind = Tok_EOF then
                  raise Syntax_Error with
                    "unbalanced `@[` annotation (missing `]@`, spec 5.16)";
               end if;
               Advance (C);
            end loop;
            Advance (C);   --  past `]@`
         end loop;
         exit when C.Cur.Kind = Tok_EOF;
         case C.Cur.Kind is
            when Kw_Fn | Kw_Extern | Kw_Variadic | Kw_Airside
               | Dir_At_Inline | Dir_At_No_Inline   --  §5.14
               | Dir_At_Symbol =>                    --  §5.15
               U.Fns.Append (Parse_Fn_Decl (C));
            when Kw_Pub =>
               --  `pub` heads a subroutine, trait, struct, enum, const, or
               --  static. §10.3: `pub` governs whether the declaration is
               --  reachable through a `@add`-ing unit's namespace.
               if Peek_Tok (C).Kind = Kw_Trait then
                  Parse_Trait_Decl (C, U.Traits);
               elsif Peek_Tok (C).Kind = Kw_Struct then
                  U.Structs.Append (Parse_Struct_Decl (C));
               elsif Peek_Tok (C).Kind = Kw_Enum then
                  U.Enums.Append (Parse_Enum_Decl (C));
               elsif Peek_Tok (C).Kind = Kw_Const then
                  Advance (C);
                  declare
                     CD : Const_Decl := Parse_Const_Decl (C);
                  begin
                     CD.Is_Pub := True;
                     U.Consts.Append (CD);
                  end;
               elsif Peek_Tok (C).Kind = Kw_Module then
                  --  §10.6 `pub module name { … }` (flattened).
                  Advance (C);   --  `pub`
                  Advance (C);   --  `module`
                  declare
                     Nm : constant SU.Unbounded_String :=
                       Take_Ident (C, "module name");
                     pragma Unreferenced (Nm);
                  begin null; end;
                  Expect (C, Punct_LBrace, "'{' to open module body");
                  Module_Depth := Module_Depth + 1;
               elsif Peek_Tok (C).Kind = Kw_Static then
                  Advance (C);
                  declare
                     SD : Static_Decl := Parse_Static_Decl (C);
                  begin
                     SD.Is_Pub := True;
                     U.Statics.Append (SD);
                  end;
               else
                  U.Fns.Append (Parse_Fn_Decl (C));
               end if;
            when Kw_Const =>
               U.Consts.Append (Parse_Const_Decl (C));
            when Dir_At_Dyn =>
               U.Dyns.Append (Parse_Dyn_Decl (C));
            when Dir_At_Add =>
               --  §10.2/§10.3 `@add [pub] [prefix::]"path" as ident;` — the
               --  `as ident` namespace name is mandatory and is how the
               --  import's `pub` declarations are accessed (`ident::item`).
               --  (`@add pub` re-export chaining is not modelled.)
               Advance (C);
               declare
                  Prefix : SU.Unbounded_String;
               begin
                  if C.Cur.Kind = Kw_Pub then
                     Advance (C);   --  `pub` re-export (not modelled)
                  end if;
                  if C.Cur.Kind = Tok_Ident
                    and then Peek_Tok (C).Kind = Punct_ColonColon
                  then
                     Prefix := C.Cur.Lexeme;
                     Advance (C);   --  prefix
                     Advance (C);   --  ::
                  end if;
                  if C.Cur.Kind /= Tok_String_Lit then
                     raise Syntax_Error with
                       "`@add` requires a string path at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  U.Adds.Append (C.Cur.Str_Bytes);
                  U.Add_Prefixes.Append (Prefix);
                  Advance (C);
                  Expect (C, Kw_As, "`as` in @add (spec 10.2)");
                  declare
                     Ns : constant SU.Unbounded_String :=
                       Take_Ident (C, "@add namespace name");
                  begin
                     U.Add_Names.Append (Ns);
                     C.Add_Aliases.Append (Ns);
                  end;
                  Expect (C, Punct_Semi, "';' after @add");
               end;
            when Dir_At_Path =>
               --  §10.5 `@path "base" as name;` — named search-path prefix.
               Advance (C);
               if C.Cur.Kind /= Tok_String_Lit then
                  raise Syntax_Error with
                    "`@path` requires a string base at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               declare
                  Base : constant SU.Unbounded_String := C.Cur.Str_Bytes;
                  Line : constant Positive := C.Cur.Line;
               begin
                  Advance (C);
                  Expect (C, Kw_As, "'as' in @path");
                  declare
                     Nm : constant SU.Unbounded_String :=
                       Take_Ident (C, "@path prefix name");
                  begin
                     --  §10.5: duplicate declarations of the same prefix
                     --  name within one source unit are a translation
                     --  failure (the cross-unit identical-base allowance is
                     --  enforced by the driver).
                     for P in U.Path_Names.First_Index ..
                              U.Path_Names.Last_Index loop
                        if SU."=" (U.Path_Names.Element (P), Nm) then
                           raise Syntax_Error with
                             "duplicate `@path` prefix '"
                             & SU.To_String (Nm)
                             & "' (§10.5) at line" & Positive'Image (Line);
                        end if;
                     end loop;
                     U.Path_Names.Append (Nm);
                     U.Path_Bases.Append (Base);
                  end;
               end;
               if C.Cur.Kind = Punct_Semi then
                  Advance (C);
               end if;
            when Dir_At_Trap =>
               --  §7.10.1 `@trap { ... }` handler. At most one per
               --  translation unit.
               if U.Has_Trap_Handler then
                  raise Syntax_Error with
                    "multiple @trap handlers in one translation unit "
                    & "(§7.10.1) at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);
               U.Has_Trap_Handler := True;
               Parse_Block_Stmts (C, U.Trap_Handler);
            when Tok_Asm =>
               --  §5.13 top-level inline assembly — emitted verbatim into the
               --  text section. Operand-less only (bootstrap).
               U.Top_Asm.Append (C.Cur.Lexeme);
               Advance (C);
               if C.Cur.Kind = Punct_Semi then
                  Advance (C);
               end if;
            when Kw_Struct =>
               U.Structs.Append (Parse_Struct_Decl (C));
            when Kw_Enum =>
               U.Enums.Append (Parse_Enum_Decl (C));
            when Kw_Impl =>
               Parse_Impl_Decl
                 (C, U.Fns, U.Trait_Impls, U.Gen_Methods, U.Traits);
            when Kw_Trait =>
               Parse_Trait_Decl (C, U.Traits);
            when Punct_RBrace =>
               --  §10.6 closing brace of a `module` body (flattened).
               if Module_Depth = 0 then
                  raise Syntax_Error with
                    "unexpected '}' at top level at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Module_Depth := Module_Depth - 1;
               Advance (C);
            when Kw_Static =>
               --  §5.4 `static [mut] NAME: T = expr ;`.
               U.Statics.Append (Parse_Static_Decl (C));
            when Kw_Module =>
               --  §10.6 `module name { … }` — a transparent namespace wrapper;
               --  its declarations flatten into the unit. `pub module` too.
               Advance (C);   --  `module`
               declare
                  Nm : constant SU.Unbounded_String :=
                    Take_Ident (C, "module name");
                  pragma Unreferenced (Nm);
               begin null; end;
               Expect (C, Punct_LBrace, "'{' to open module body");
               Module_Depth := Module_Depth + 1;
            when Kw_Use =>
               --  §5.12.2 `use path;` — unqualified name introduction. In the
               --  single-unit bootstrap every declaration is already in one
               --  flat scope, so a `use` is consumed and has no effect (it
               --  becomes meaningful only with the module model, §10).
               Advance (C);
               while C.Cur.Kind /= Punct_Semi
                 and then C.Cur.Kind /= Tok_EOF
               loop
                  Advance (C);
               end loop;
               Expect (C, Punct_Semi, "';' after `use`");
            when Kw_Type =>
               --  §5.8 `type NAME = type ;` — alias declaration. The
               --  substitution happens at later use sites (Parse_Type),
               --  so nothing is recorded in the translation unit.
               Advance (C);
               declare
                  A : Alias_Entry;
               begin
                  A.Name := Take_Ident (C, "alias name after 'type'");
                  --  §5.8 generic alias `type Name.<T, U> = ...`.
                  if C.Cur.Kind = Punct_Dot
                    and then Peek_Tok (C).Kind = Op_Lt
                  then
                     Advance (C);   --  '.'
                     Advance (C);   --  '<'
                     loop
                        A.Params.Append
                          (Take_Ident (C, "alias type parameter"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                     end loop;
                     Expect (C, Op_Gt, "'>' to close alias parameters");
                  end if;
                  Expect (C, Punct_Eq, "'=' in type alias");
                  A.Target := Parse_Type (C);
                  Expect (C, Punct_Semi, "';' after type alias");
                  C.Aliases.Append (A);
               end;
            when others =>
               raise Syntax_Error with
                 "expected top-level declaration, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
         end case;
      end loop;
      if Module_Depth > 0 then
         raise Syntax_Error with
           "unterminated `module` (missing '}', spec 10.6)";
      end if;
      return U;
   end Parse_Unit;

end Kurt.Parser;
