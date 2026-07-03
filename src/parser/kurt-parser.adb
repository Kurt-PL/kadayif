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
   is separate;

   --  §5.8 deep-copy a type, substituting each named type matching a generic
   --  alias parameter with the corresponding argument. Used to expand a
   --  generic alias instance `Name.<Args>` against its template.
   function Copy_Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is separate;

   function Parse_Type (C : in out Cursor) return Type_Access is separate;

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
   is separate;

   procedure Parse_Param_List
     (C             : in out Cursor;
      Params        : out Param_Vectors.Vector;
      Allow_Unnamed : Boolean)
   is separate;

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
         when Op_CaretCaret => Op := B_LXor;
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
         when B_LAnd        => return 20;   --  §7.2.2 level 14
         when B_LXor        => return 18;   --  level 15 (between && and ||)
         when B_LOr         => return 15;   --  level 16
      end case;
   end Binding_Power;

   --  Body appears with the statement parsers below; needed here for the
   --  §6.9 `airside { ... }` block expression.
   procedure Parse_Block_Stmts
     (C : in out Cursor; Stmts : out Stmt_Vectors.Vector);

   --  §7.4 parse a variant pattern's payload destructuring `{ ... }` into
   --  the pattern P: a bare `ident` is a positional binding; `field = ident`
   --  binds the named field. Assumes the opening `{` is the current token.
   procedure Parse_Payload_Binds (C : in out Cursor; P : in out Pattern) is
   begin
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               N1 : constant SU.Unbounded_String :=
                 Take_Ident (C, "payload binding");
            begin
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);   --  '='
                  P.Bind_Fields.Append (N1);
                  P.Bindings.Append (Take_Ident (C, "renamed binding"));
               else
                  P.Bind_Fields.Append (SU.Null_Unbounded_String);
                  P.Bindings.Append (N1);
               end if;
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");
   end Parse_Payload_Binds;

   function Parse_Primary (C : in out Cursor) return Expr_Access is separate;

   function Parse_Postfix (C : in out Cursor; Start : Expr_Access)
      return Expr_Access
   is separate;

   --  Unary prefix operators (§6.3, prec 5). Bootstrap: `*` deref, `-` neg,
   --  `!` not, and §8.1 reference creation `&[raw] [mods] place` / `$place`.
   function Parse_Unary (C : in out Cursor) return Expr_Access is separate;

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
   is separate;

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
   is separate;

   --  Natural to string with no leading space.
   function Trim_Img (N : Natural) return String is
      Raw : constant String := Natural'Image (N);
   begin
      return Raw (Raw'First + 1 .. Raw'Last);
   end Trim_Img;

   function Parse_Stmt (C : in out Cursor) return Stmt_Access is separate;

   ----------------------------------------------------------------------
   --  fn header / proto / decl
   ----------------------------------------------------------------------

   procedure Parse_Fn_Header
     (C             : in out Cursor;
      Allow_Unnamed : Boolean;
      H             : out Fn_Header)
   is separate;

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

   function Parse_Dyn_Decl (C : in out Cursor) return Dyn_Decl is separate;

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
   is separate;

   ----------------------------------------------------------------------
   --  trait declaration (§9.3). Bootstrap subset: method signatures and
   --  default methods. The `selftype` placeholder in signatures stays
   --  abstract here; impl blocks substitute the concrete type.
   ----------------------------------------------------------------------

   procedure Parse_Trait_Decl
     (C : in out Cursor; Traits : in out Trait_Vectors.Vector)
   is separate;

   ----------------------------------------------------------------------
   --  Top-level dispatch
   ----------------------------------------------------------------------

   --  struct_declaration = "struct" IDENT "{" field { "," field } "}"
   --  field = IDENT ":" type            (§5.5, bootstrap subset)
   function Parse_Struct_Decl (C : in out Cursor) return Struct_Decl is separate;

   --  enum_declaration = "enum" IDENT "{" variant { "," variant } "}"
   --  variant = IDENT [ "=" integer_literal ]    (§5.6, unit variants)
   --  Discriminants default to 0,1,2,... continuing from the last value.
   function Parse_Enum_Decl (C : in out Cursor) return Enum_Decl is separate;

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
      Extra_Names : Path_Segments.Vector := Path_Segments.Empty_Vector;
      Super_Word  : String := "")
   is separate;

   ----------------------------------------------------------------------

   procedure Resolve_Aliases
     (U              : in out Translation_Unit;
      Alias_Names    : Path_Segments.Vector;
      Alias_Prefixes : Path_Segments.Vector)
   is separate;

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit
   is separate;

end Kurt.Parser;
