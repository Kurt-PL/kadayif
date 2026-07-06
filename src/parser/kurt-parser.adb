with Ada.Strings.Fixed;
with Ada.Unchecked_Conversion;
with Interfaces;

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
      --  §10.6 nesting depth of `module { ... }` bodies currently open
      --  around the token being parsed; 0 at source-unit top level. Lets a
      --  `super` path head be rejected outside any module.
      Module_Depth : Natural := 0;
      --  §6.10/§6.10.2 nesting depth of translation-time-evaluated regions
      --  currently open around the token being parsed: the body of an
      --  `xlatime { ... }` block, or a `const`/`static` initializer
      --  expression (§6.10.2's "implicit xlatime"). `if xlatime`/
      --  `if !xlatime` consult this (> 0 means the surrounding context is
      --  itself translation-time evaluation, so `xlatime` is TRUE) to pick
      --  which branch is kept and which is discarded unchecked. Zero at an
      --  ordinary (execution-time) fn body, where `xlatime` is FALSE.
      Xlatime_Depth : Natural := 0;
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
   is separate;

   --  §8.4.3 `lifetime_body` grammar shared by the subroutine and the
   --  composite-type forms of `with lifetime` — called with the cursor
   --  just past the `lifetime` keyword:
   --      'a 'b                  (single chain, braces optional)
   --      { 'a 'b, 'c 'd }       (multiple chains)
   --  Each chain becomes one Path_Segments.Vector of lifetime names,
   --  appended to Chains in source order.
   procedure Parse_Lifetime_Body
     (C : in out Cursor; Chains : in out Lifetime_Chain_Vectors.Vector)
   is separate;

   --  §8.4.3 `with lifetime` ordering constraints, on a subroutine or a
   --  composite-type declaration:
   --      with lifetime 'a 'b              (single chain, braces optional)
   --      with lifetime { 'a 'b, 'c 'd }   (multiple chains)
   --  On subroutines the bootstrap validates the shape and erases it (no
   --  outlives checking); on structs/enums the chains are retained by the
   --  caller (see Parse_Struct_Decl/Parse_Enum_Decl) to govern field
   --  destruction order. Pre: the current token is `with` and the
   --  following identifier is `lifetime`.
   procedure Parse_Lifetime_Clause (C : in out Cursor) is separate;

   --  Whether the cursor sits at a `with lifetime` clause (`lifetime` is an
   --  ordinary identifier, so this distinguishes it from `with destruct`
   --  etc. by lookahead).
   function At_Lifetime_Clause (C : in out Cursor) return Boolean is
   begin
      return C.Cur.Kind = Kw_With
        and then Peek_Tok (C).Kind = Tok_Ident
        and then SU.To_String (Peek_Tok (C).Lexeme) = "lifetime";
   end At_Lifetime_Clause;

   --  §5.9 generic type-parameter names shall be distinct. Called right
   --  after parsing a struct/enum generic clause, at translation time the
   --  fn-header equivalent runs in Kurt.Sema.Check (over U.Fns/U.Gen_Fns);
   --  struct/enum generic templates are not similarly visible to Sema
   --  after Kurt.Mono.Monomorphize lifts them out of U.Structs/U.Enums, so
   --  this check is done here, at parse time, instead.
   procedure Check_Unique_Generic_Names
     (Owner : String; G : Generic_Param_Vectors.Vector)
   is
   begin
      for I in G.First_Index .. G.Last_Index loop
         for J in G.First_Index .. I - 1 loop
            if SU.To_String (G.Element (J).Name)
                 = SU.To_String (G.Element (I).Name)
            then
               raise Syntax_Error with
                 "duplicate generic parameter '"
                 & SU.To_String (G.Element (I).Name)
                 & "' in '" & Owner & "' (spec 5.9)";
            end if;
         end loop;
      end loop;
   end Check_Unique_Generic_Names;

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

   --  Forward-declared here (ahead of its "natural" position below, in the
   --  Expressions section) so Parse_Type's subunit -- which needs to parse
   --  a general expression in `[T; N]`'s length position, spec 4.7 -- has
   --  visibility to it. The completion ("is separate") stays at its
   --  original position.
   function Parse_Expr (C : in out Cursor) return Expr_Access;

   function Parse_Type (C : in out Cursor) return Type_Access is separate;

   --  Optional generic parameter clause on a subroutine (§5.9):
   --  `.< T [: bound { '+' bound }], ... >`. Bounds are builtin bound
   --  names (§9.8) recorded for the type-erasure check in Kurt.Sema.
   procedure Parse_Opt_Generic_Params_Bounded
     (C : in out Cursor; Params : out Generic_Param_Vectors.Vector)
   is separate;

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

   --  §9.9 closure expression (body defined after Parse_Block_Stmts).
   function Parse_Closure
     (C : in out Cursor; Xfer : Boolean) return Expr_Access;

   function Token_To_Binop (K : Token_Kind; Op : out Binary_Op) return Boolean is separate;

   --  Higher = tighter binding. Mirrors §6 precedence table:
   --    spec prec 7  (* / % *| /|)        => bp 70
   --    spec prec 8  (*@, non-assoc)      => bp 65
   --    spec prec 9  (+ - +| -|)          => bp 60
   --    spec prec 10 (+@, non-assoc)      => bp 55
   --    spec prec 15 (== != < > <= >=)    => bp 30
   --  `*@`/`+@` each occupy their own level and are non-associative
   --  (Non_Assoc below); every other level here is leading-to-following.
   function Binding_Power (Op : Binary_Op) return Natural is
   begin
      case Op is
         when B_Mul | B_Div | B_Mod | B_Sat_Mul | B_Sat_Div => return 70;
         when B_Wide_Mul    => return 65;   --  level 8
         when B_Add | B_Sub | B_Sat_Add | B_Sat_Sub => return 60;
         when B_Wide_Add    => return 55;   --  level 10
         when B_Shl | B_Shr => return 50;   --  level 11
         when B_And         => return 45;   --  level 12
         when B_Xor         => return 40;   --  level 13
         when B_Or          => return 35;   --  level 14
         when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge => return 30;  --  15
         when B_LAnd        => return 20;   --  §7.2.2 level 16
         when B_LXor        => return 18;   --  level 17 (between && and ||)
         when B_LOr         => return 15;   --  level 18
      end case;
   end Binding_Power;

   --  Body appears with the statement parsers below; needed here for the
   --  §6.9 `airside { ... }` block expression.
   procedure Parse_Block_Stmts
     (C : in out Cursor; Stmts : out Stmt_Vectors.Vector);

   --  §5.10/§7.4 parse a single match/let-else pattern (no top-level `|` --
   --  callers collect or-pattern alternatives themselves). Shared by
   --  Prim_Match and, recursively, Parse_Payload_Binds (item(a) nested
   --  payload sub-patterns, spec 7.4). Forward-declared (mutual recursion
   --  with Parse_Payload_Binds); the separate body is given after it below.
   function Parse_Match_Pattern (C : in out Cursor) return Pattern;

   --  §7.4 parse a variant pattern's payload destructuring `{ ... }` into
   --  the pattern P: a bare `ident` is a positional binding; `field = ident`
   --  binds the named field; a slot written as a full nested pattern (e.g.
   --  `res::Yes { v }`) recurses via Parse_Match_Pattern (item(a), spec
   --  7.4). Assumes the opening `{` is the current token.
   procedure Parse_Payload_Binds (C : in out Cursor; P : in out Pattern) is separate;

   function Parse_Match_Pattern (C : in out Cursor) return Pattern is separate;

   function Parse_Primary (C : in out Cursor) return Expr_Access is separate;

   function Parse_Postfix (C : in out Cursor; Start : Expr_Access)
      return Expr_Access
   is separate;

   --  Unary prefix operators (§6.3, prec 5). Bootstrap: `*` deref, `-` neg,
   --  `!` not, and §8.1 reference creation `&[raw] [mods] place` / `$place`.
   function Parse_Unary (C : in out Cursor) return Expr_Access is separate;

   --  Cast operators `as` / `as ?` (§6.8, prec 6 — between unary and
   --  multiplicative). `as!` (airside reinterpret) is deferred.
   function Parse_Cast (C : in out Cursor) return Expr_Access is separate;

   function Is_Cmp (Op : Binary_Op) return Boolean is
     (Op in B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge);

   --  §6.4.3 widening arithmetic (`+@`, `*@`) — each occupies its own
   --  precedence level and is non-associative (Non_Assoc below), unlike
   --  the leading-to-following levels around it.
   function Is_Wide (Op : Binary_Op) return Boolean is
     (Op in B_Wide_Add | B_Wide_Mul);

   --  §6.4.3/§6.6: an operator whose precedence TIER forbids chaining --
   --  comparisons (all one shared tier) and each widening operator (its
   --  own singleton tier). Two operators sharing a Binding_Power that is
   --  Non_Assoc shall not appear back-to-back without parentheses.
   function Non_Assoc (Op : Binary_Op) return Boolean is
     (Is_Cmp (Op) or else Is_Wide (Op));

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

   --  §8.7 compare-and-swap: `target >.< expected then new` (eq-CAS) and
   --  `target >!< expected then new` (ne-CAS), at the lowest binding power
   --  (the operands are full binary expressions). Non-associative.
   function Parse_Expr (C : in out Cursor) return Expr_Access is separate;

   ----------------------------------------------------------------------
   --  Statements / blocks
   ----------------------------------------------------------------------

   function Parse_Stmt (C : in out Cursor) return Stmt_Access;

   --  Parse a condition expression with struct-literal suppression so
   --  the following '{' is read as a block, not a struct literal.
   function Parse_Cond (C : in out Cursor) return Expr_Access is separate;

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

   function Parse_Fn_Decl (C : in out Cursor) return Fn_Decl is separate;

   function Parse_Fn_Proto (C : in out Cursor) return Fn_Proto is separate;

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
   function Parse_Const_Decl (C : in out Cursor) return Const_Decl is separate;

   --  §5.4 `static [mut] NAME: T = expr ;`.
   function Parse_Static_Decl (C : in out Cursor) return Static_Decl is separate;

   procedure Merge_Unit
     (Into : in out Translation_Unit; From : Translation_Unit) is separate;

   ----------------------------------------------------------------------
   --  §10.3 namespace mangling (see kurt-parser.ads for the design note).
   ----------------------------------------------------------------------

   function Snapshot (U : Translation_Unit) return Rename_From is separate;

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
      Pub_Source     : Translation_Unit;
      Cur_Prefix     : String;
      Alias_Names    : Path_Segments.Vector;
      Alias_Prefixes : Path_Segments.Vector;
      NS_Names       : Path_Segments.Vector;
      NS_Pubs        : Bool_Vectors.Vector)
   is separate;

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit
   is separate;

   ----------------------------------------------------------------------
   --  §5.3/§5.4/§6.10 small-integer xlatime folding (see kurt-parser.ads).
   ----------------------------------------------------------------------

   function Fold_Int_Expr
     (U     : Translation_Unit;
      E     : Expr_Access;
      Value : out Long_Long_Integer) return Boolean
   is separate;

end Kurt.Parser;
