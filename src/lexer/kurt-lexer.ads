--  Kadayif bootstrap lexer.
--  Scope: enough to tokenise first.kr and hello.kr.
--
--  Spec references §3.2, §3.3, §3.4.1, §3.4.5, §3.4.7, §3.5, §3.6.
--  The full lexer (raw strings, i# prefix, all keywords/operators,
--  every @-directive, digit separators, multi-radix literals, etc.)
--  is deferred. See kadayif/design.md §2.

with Ada.Strings.Unbounded;

package Kurt.Lexer is

   package SU renames Ada.Strings.Unbounded;

   type Token_Kind is
     (Tok_EOF,
      Tok_Ident,
      Tok_Int_Lit,
      Tok_Float_Lit,   --  value in Float_V, type suffix in Int_Suffix
      Tok_String_Lit,  --  payload in Str_Bytes (post-escape resolution)
      Tok_Char_Lit,    --  §3.5.4 character literal; cell value in Int_V
      Tok_Label,       --  §7.9 loop/block label `'name` (name in Lexeme)
      Tok_Hash_Wild,   --  #wild#  (§3.6, single indivisible token)
      Tok_Hash,        --  #       (§5.10 binding pattern `name # sub`)
      Tok_Asm,         --  asm { … } raw instruction body (§6.11, lexeme=body)
      --  Keywords (§3.3.1)
      Kw_Fn,
      Kw_Return,
      Kw_As,
      Kw_As_Bang,        --  `as!` airside reinterpret cast (§3.7, §6.8.11)
      Kw_Pub,
      Kw_Extern,
      Kw_Variadic,
      Kw_Airside,
      Kw_Let,
      Kw_Mut,
      Kw_If,
      Kw_Then,
      Kw_Else,
      Kw_While,
      Kw_Loop,           --  `loop { ... }` (§7.5.2)
      Kw_Break,
      Kw_Continue,
      Kw_Express,        --  `express` block-level exit-with-value (§7.8)
      Kw_Uninit,         --  `uninit` uninitialized value introduction (§6.1.8)
      Kw_Struct,
      Kw_Enum,
      Kw_Match,
      Kw_With,
      Kw_Impl,           --  inherent implementation block (§9.1)
      Kw_Trait,          --  trait declaration (§9.3)
      Kw_Dyn,            --  `dyn Trait` trait-object type (§9.5)
      Kw_Const,          --  associated constant (§9.3.2)
      --  §3.3.1 explicit-by-declaration keywords (do not appear in EBNF as
      --  double-quoted terminals).
      Kw_True,
      Kw_False,
      Kw_Cellbits,       --  cell-width keyword (§4.2.1, replaces CELL_BITS)
      Kw_Never,          --  `never` diverging return type (§4.10, §7.11)
      Kw_Xlatime,        --  `xlatime` translation-time evaluation (§6.10)
      --  Reference sigils (§4.9, §8.1). The `raw` qualifier in `&raw T`
      --  is a normal identifier; the parser splices the two tokens.
      Op_Amp,            --  &
      Op_Dollar,         --  $
      Op_Star,           --  *  (dereference / multiplication)
      --  Binary operators (§6) — bootstrap subset.
      Op_Plus,           --  +
      Op_Minus,          --  -
      Op_Slash,          --  /
      Op_Percent,        --  %
      --  Saturating arithmetic (§6.4.2)
      Op_PlusBar,        --  +|
      Op_MinusBar,       --  -|
      Op_StarBar,        --  *|
      Op_SlashBar,       --  /|
      --  Widening arithmetic (§6.4.3)
      Op_PlusAt,         --  +@
      Op_StarAt,         --  *@
      --  Compound assignment (§6.7)
      Op_PlusEq,         --  +=
      Op_MinusEq,        --  -=
      Op_StarEq,         --  *=
      Op_SlashEq,        --  /=
      Op_PercentEq,      --  %=
      Op_AmpEq,          --  &=
      Op_BarEq,          --  |=
      Op_CaretEq,        --  ^=
      Op_ShlEq,          --  <<=
      Op_ShrEq,          --  >>=
      Op_PlusBarEq,      --  +|=  (§3.6: saturating-op + '=')
      Op_MinusBarEq,     --  -|=
      Op_StarBarEq,      --  *|=
      Op_SlashBarEq,     --  /|=
      Op_EqEq,           --  ==
      Op_BangEq,         --  !=
      Op_Lt,             --  <
      Op_Gt,             --  >
      Op_Le,             --  <=
      Op_Ge,             --  >=
      Op_Bar,            --  |  (contract failure-binding separator / bit OR)
      --  Contract logical operators (§7.2.2)
      Op_AmpAmp,         --  &&  (short-circuit AND)
      Op_BarBar,         --  ||  (short-circuit OR)
      Op_Question,       --  ?  (discriminant cast target)
      --  Compare-and-swap (§8.7)
      Op_EqCas,          --  >.<  (swap if equal)
      Op_NeCas,          --  >!<  (swap if not equal)
      --  Bitwise / shift (§6.5). `&` is Op_Amp (shared with ref sigil).
      Op_Caret,          --  ^  (bitwise / contract XOR)
      Op_Shl,            --  <<
      Op_Shr,            --  >>
      Op_Bang,           --  !  (bitwise NOT / contract polarity)
      --  Punctuation
      Punct_Eq,          --  =  (assignment / initialiser)
      Punct_LParen,      --  (
      Punct_RParen,      --  )
      Punct_LBrace,      --  {
      Punct_RBrace,      --  }
      Punct_LBracket,    --  [  (array types / literals / indexing, §4.6)
      Punct_RBracket,    --  ]
      Punct_Arrow,       --  ->
      Punct_LArrow,      --  <-  (contract extraction)
      Punct_Semi,        --  ;
      Punct_Comma,       --  ,
      Punct_Colon,       --  :
      Punct_ColonColon,  --  ::
      Punct_Dot,         --  .
      Op_DotDot,         --  ..   (exclusive range, §4.8)
      Op_DotDotEq,       --  ..=  (inclusive range, §4.8)
      Op_Ellipsis,       --  ...  (rest pattern / variadic, §7.4.2)
      --  Directives (§10.3, §8.5.3)
      Dir_At_Dyn,
      Dir_At_Add,        --  @add "path"  source import (§10.2)
      Dir_At_Path,       --  @path "base" as name  search-path prefix (§10.5)
      Dir_At_Trap,       --  @trap termination primitive / handler (§7.10)
      Dir_At_Guard,      --  @guard fence family (§8.5.3)
      Dir_At_Volatile,   --  @volatile fence family (§8.5.3)
      Dir_At_Size,       --  T@size   type intrinsic (§6.12)
      Dir_At_Align,      --  T@align  type intrinsic (§6.12)
      Dir_At_Offset,     --  T@offset(field) type intrinsic (§6.12)
      Dir_At_Name,       --  T@name   name intrinsic (§6.12.2)
      Dir_At_Inline,     --  @inline    subroutine inlining hint (§5.14)
      Dir_At_No_Inline,  --  @no_inline subroutine inlining prohibition
      Dir_At_Symbol,     --  @symbol "name"  external symbol override (§5.15)
      Dir_At_LBracket,   --  @[   annotation open  (§5.16)
      Dir_At_RBracket);  --  ]@   annotation close (§5.16)

   type Token is record
      Kind      : Token_Kind   := Tok_EOF;
      Lexeme    : SU.Unbounded_String;
      Int_V     : Long_Long_Integer := 0;
      --  Value of a Tok_Float_Lit (§3.4.2).
      Float_V   : Long_Float := 0.0;
      --  Numeric type suffix (§3.4.1/§3.4.2), e.g. "si4" / "fe8m23"; empty
      --  if absent. Shared by integer and floating-point literals.
      Int_Suffix : SU.Unbounded_String;
      --  Post-escape byte sequence for Tok_String_Lit. Each Character
      --  in the string corresponds to one source-encoding byte. Escapes
      --  defined in §3.4.7 are resolved by the lexer.
      Str_Bytes : SU.Unbounded_String;
      Line      : Positive     := 1;
      Col       : Positive     := 1;
   end record;

   type Lexer is tagged limited private;

   procedure Init (L : out Lexer; Source : String);
   function  Next_Token (L : in out Lexer) return Token;

   --  §10.7 introduce a translation-time flag from the external mechanism
   --  (e.g. a `-f NAME` command-line option). Call before lexing.
   procedure Define_Flag (L : in out Lexer; Name : String);

   Translation_Failure : exception;

private

   type Lexer is tagged limited record
      Src  : SU.Unbounded_String;
      Pos  : Positive := 1;
      Line : Positive := 1;
      Col  : Positive := 1;
      --  §10.7 active translation-time flags, stored space-delimited and
      --  space-bracketed (" a b "), so membership is a substring test.
      Flags : SU.Unbounded_String := SU.To_Unbounded_String (" ");
      --  §10.8 line-branch support. When a `@flag_if(...) body @` line branch
      --  is taken, this holds the source position of the closing `@`; the
      --  main token loop consumes that `@` (and skips any remaining line
      --  branches of the chain) when lexing reaches it. Zero when inactive.
      Line_Close : Natural := 0;
   end record;

end Kurt.Lexer;
