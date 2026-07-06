--  Kadayif bootstrap parser: recursive-descent / Pratt, producing the
--  AST consumed by Kurt.Sema / Kurt.Mono / Kurt.Codegen.
--
--  Covers declarations (§5: fn/let/mut/const/static/struct/enum/type
--  alias/use, generic clauses with bounds), types (§4: named, refs with
--  modifiers, tuples, arrays/slices, ranges, subroutine pointers and
--  invocables, `dyn Trait`), expressions (§6, precedence-climbing,
--  casts, intrinsics), statements/control flow (§7: if/if let/match/
--  while/while let/loop/labels/express), traits/impls (§9), closures
--  (§9.9), and programme structure (§10: @add/@dyn/@path/module).

with Ada.Strings.Unbounded;
with Ada.Containers.Vectors;

with Kurt.Lexer;

package Kurt.Parser is

   package SU renames Ada.Strings.Unbounded;

   ----------------------------------------------------------------------
   --  Types (§4 — minimal subset)
   ----------------------------------------------------------------------

   type AST_Type;
   type Type_Access is access AST_Type;

   package Type_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Type_Access);

   --  Forward-declared early (completed below) so T_Array can hold an
   --  unresolved array-length expression (Len_Expr, spec 4.7/6.1.6).
   type Expr_Node;
   type Expr_Access is access Expr_Node;

   type Type_Kind is
     (T_Named, T_Ref, T_Tuple, T_Array, T_Dyn, T_Fn);
   type Ref_Sigil is (R_Shared, R_Excl, R_Raw);

   --  §8.1 store-discipline modifier: `mut`, `atomic`, and `guard` are
   --  pairwise mutually exclusive; RS_None is a load-only reference.
   type Ref_Store is (RS_None, RS_Mut, RS_Atomic, RS_Guard);

   type AST_Type (Kind : Type_Kind := T_Named) is record
      case Kind is
         when T_Named =>
            Name : SU.Unbounded_String;
            --  Generic arguments, e.g. the `si4, si4` of `verdict.<si4, si4>`.
            --  Empty for a plain named type or a generic parameter.
            Args : Type_Vectors.Vector;
         when T_Ref =>
            Sigil      : Ref_Sigil := R_Shared;
            --  §8.1 modifiers between the sigil and the referent type.
            R_Volatile : Boolean   := False;
            R_Store    : Ref_Store := RS_None;
            --  §8.4 optional lifetime annotation `&'name T` (`'static`,
            --  `'const`, or a user name); consumed by §8.4.3 field-
            --  destruction ordering, otherwise erased (no representation).
            R_Life     : SU.Unbounded_String := SU.Null_Unbounded_String;
            Target     : Type_Access;
         when T_Tuple =>
            --  §4.7 anonymous tuple `.{T, T, ...}` (positional fields).
            Elems : Type_Vectors.Vector;
         when T_Array =>
            --  §4.7 fixed-size array `[T; N]` (`Len > 0`). `Len = 0` is
            --  the `[T]` bracket of a slice reference (§8.1.4): under the
            --  spec's grammar `[T]` exists only inside a slice-reference
            --  production, never as a standalone type, so a bare
            --  `T_Array (Len = 0)` outside a T_Ref target is rejected by
            --  sema (params/returns/fields/payloads/bindings).
            Elem : Type_Access;
            Len  : Cell_Count := 0;
            --  §4.7/§6.1.6: N need not be a bare literal (`const`/arithmetic
            --  permitted); Kurt.Mono.Monomorphize.Visit_Type folds it into
            --  Len ahead of any Kurt.Layout.Size_Of query.
            Len_Expr : Expr_Access := null;
         when T_Dyn =>
            --  §9.5 trait object `dyn Trait`. Only meaningful as a
            --  reference referent; `&dyn Trait` is a fat reference
            --  (value ptr + dispatch-table ptr).
            Trait_Name : SU.Unbounded_String;
         when T_Fn =>
            --  §4.10 subroutine pointer `[extern[(iface)]] [variadic]
            --  [airside] fn (T...) [-> U]`. A pointer-sized value (not a
            --  reference). Parameter names are informational only, so only
            --  the parameter types are kept. Fn_Ret null => void (or never
            --  when Fn_Never). Fn_Extern empty => the native invocation
            --  interface (as do `extern` / `extern(native)`).
            Fn_Params   : Type_Vectors.Vector;
            Fn_Ret      : Type_Access;
            Fn_Variadic : Boolean := False;
            Fn_Airside  : Boolean := False;
            Fn_Never    : Boolean := False;
            Fn_Extern   : SU.Unbounded_String;
            --  §9.9.2 invocable type syntax. Fn_Invocable distinguishes
            --  `/.T/ -> U` (accepts subroutine pointers and non-`xfer`
            --  closures, invocable any number of times) from the plain
            --  subroutine-pointer `fn(T) -> U`. Fn_Xfer marks the consuming
            --  form `xfer /.T/ -> U` (accepts `xfer` closures too, invocable
            --  at most once, acquires `with destruct`). Both are represented
            --  as a pointer-sized value like `fn`.
            Fn_Invocable : Boolean := False;
            Fn_Xfer      : Boolean := False;
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Forward declarations so Expr/Stmt can refer to each other and
   --  to vectors of themselves.
   ----------------------------------------------------------------------

   --  (Expr_Node/Expr_Access are forward-declared earlier, with Type_Access.)
   package Expr_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Expr_Access);

   package Path_Segments is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => SU.Unbounded_String,
      "="          => SU."=");

   --  §8.4.3 `with lifetime` chain(s): 'a 'b 'c asserts 'a >= 'b >= 'c.
   package Lifetime_Chain_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Path_Segments.Vector,
      "="          => Path_Segments."=");

   --  §10.3/§10.4/§10.6 parallel pub-flag vectors (one Boolean per entry
   --  of a matching Path_Segments.Vector: Add_Names/Module_Names/etc.).
   package Bool_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Boolean);

   --  §5.12.2 `use path::name;` — one full qualified path per imported
   --  bare name (Translation_Unit.Use_Paths, parallel to Use_Names).
   package Segment_Path_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Path_Segments.Vector,
      "="          => Path_Segments."=");

   type Stmt_Node;
   type Stmt_Access is access Stmt_Node;

   package Stmt_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Stmt_Access);

   ----------------------------------------------------------------------
   --  Expressions (§6 — bootstrap subset)
   ----------------------------------------------------------------------

   type Expr_Kind is
     (E_Int_Lit,
      E_Float_Lit,
      E_Bool_Lit,
      E_String_Lit,
      E_Path,
      E_Field,
      E_Call,
      E_If,
      E_Binary,
      E_Deref,
      E_Struct_Lit,
      E_Variant_New,
      E_Match,
      E_Cast,
      E_Unary,
      E_Tuple_Lit,
      E_Question,     --  `e?` contract propagation (§6.2.4, §7.2.4)
      E_Ref,          --  address-of / reference creation `&[mods] place` (§8.1)
      E_Extract,      --  `contract e else [.id] fallback` (§7.2.3)
      E_CAS,          --  compare-and-swap `t >.< exp then new` (§8.7)
      E_Array_Lit,    --  `[a, b, c]` / repeat `[v; N]` (§6.1.6)
      E_Dyn_Cast,     --  implicit `&T → &dyn Trait` coercion (§9.5)
      E_Slice_Cast,   --  implicit `&[T; N] → &[T]` coercion (§4.6)
      E_Type_Intrinsic,  --  `T@size` / `T@align` / `T@offset(f)` (§6.12)
      E_Uninit,           --  `uninit` uninitialized value (§6.1.8)
      E_Closure,          --  `/.params/ <- e` / `/.params/ { ... }` (§9.9)
      E_Destruct,         --  `destruct(e)` / `undestruct(e)` (§8.4, §8.11)
      E_Airside_Blk,      --  `airside { ... }` block expression (§6.9)
      E_Loop);            --  `loop { ... }` as an expression (§7.7)
      --  Note: Kurt has no `[]` indexing operator (§6.2). Element access
      --  is `*(arr.ptr + i)` (raw reference arithmetic, §8.6.4) or the
      --  library `.at()` method. `..`/`..=` are pattern-only tokens
      --  (§3.7); no value-level range type exists.

   --  §6.12 layout intrinsic operations (bootstrap subset).
   type Type_Intrinsic_Op is (TI_Size, TI_Align, TI_Offset);

   --  Match patterns (bootstrap subset: enum variant path, integer
   --  literal, numeric range, the anonymous-struct (tuple) pattern
   --  `.{ ... }`, or the `#wild#` catch-all). Or-patterns (`p | q`) are
   --  desugared at parse time into one arm per alternative, so they need
   --  no dedicated kind here.
   type Pattern_Kind is
     (Pat_Variant, Pat_Int, Pat_Wild, Pat_Range, Pat_Slice, Pat_Tuple);

   --  §7.4.2 a slice-pattern element: bind a name, compare an integer
   --  literal, ignore (`#wild#`), or the rest marker `...`.
   type Slice_Elem_Kind is (SE_Bind, SE_Int, SE_Wild, SE_Rest);
   type Slice_Elem is record
      Kind  : Slice_Elem_Kind := SE_Wild;
      Name  : SU.Unbounded_String;          --  SE_Bind
      Int_V : Long_Long_Integer := 0;       --  SE_Int
   end record;

   package Slice_Elem_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Slice_Elem);

   --  Item(a) forward: a payload binding slot may itself be a full nested
   --  pattern (`verdict::Pass { res::Yes { v } }`) instead of a plain name.
   --  Indirected through an access type since Pattern is not yet complete.
   type Pattern;
   type Pattern_Access is access Pattern;
   package Pattern_Access_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Pattern_Access);

   type Pattern is record
      Kind     : Pattern_Kind := Pat_Wild;
      Path     : Path_Segments.Vector;  --  Pat_Variant: Enum::Variant
      Int_V    : Long_Long_Integer := 0;  --  Pat_Int; Pat_Range lower bound
      --  §5.10 range pattern `lo..hi` / `lo..=hi` (numeric, refutable).
      Range_Hi   : Long_Long_Integer := 0;
      Range_Incl : Boolean := False;  --  Pat_Range: `..=` (true) vs `..`
      --  Pat_Variant payload bindings, positional (e.g. `{ w, h }`).
      Bindings : Path_Segments.Vector;
      --  §7.4 parallel to Bindings: rename entry's source field name (else
      --  empty = positional).
      Bind_Fields : Path_Segments.Vector;
      --  §5.10 `name # sub`: matched value bound to Bind_Name (empty = none).
      Bind_Name : SU.Unbounded_String;
      --  §5.10.1 `#wild#(name)` (Pat_Wild only): the raw representation of
      --  the matched value is bound to Wild_Bind as a `&[ui1]` cell slice.
      --  Empty = the bare, discarding `#wild#` form. Distinct from
      --  Bind_Name (`name # #wild#`), which binds at the original type.
      Wild_Bind : SU.Unbounded_String;
      --  §7.4.2 Pat_Slice elements (in order); at most one SE_Rest.
      Slice_Elems : Slice_Elem_Vectors.Vector;
      --  §7.4.2 this Pat_Slice was written as a string-literal pattern
      --  (`"GET"`), which is legal only against a `ui1`-element scrutinee.
      From_String : Boolean := False;
      --  §5.10.2 the payload-binds clause ended with `...`: fields not
      --  mentioned are ignored. Without it, omitting a field is a TF.
      Has_Rest : Boolean := False;
      --  §7.4 item(a): parallel to Bindings; slot K's nested sub-pattern
      --  when that slot was written as a full pattern (not a plain name --
      --  Bindings(K) is then empty). Null entry/absent index = plain bind.
      Sub_Pats : Pattern_Access_Vectors.Vector;
   end record;

   package Pattern_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Pattern);

   --  §9.9 a closure parameter `name: T` (Param is declared later, after
   --  Expr_Node, so closures use this lightweight pair).
   type Closure_Param is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
   end record;

   package Closure_Param_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Closure_Param);

   --  A struct-literal field initialiser: `name = expr`.
   type Field_Init is record
      Name : SU.Unbounded_String;
      Val  : Expr_Access;
   end record;

   package Field_Init_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Field_Init);

   --  A match arm: `pattern [if guard] = expr`. (Block-body arms deferred.)
   --  §7.4: an optional guard clause restricts matching — the arm is selected
   --  only when the pattern matches AND the guard evaluates to `true`.
   type Match_Arm is record
      Pat      : Pattern;
      Guard    : Expr_Access := null;  --  §7.4 optional `if` guard; null = none
      Arm_Body : Expr_Access;
   end record;

   package Match_Arm_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Match_Arm);

   type Binary_Op is
     (B_Add, B_Sub, B_Mul, B_Div, B_Mod,
      --  Saturating variants (§6.4.2): +| -| *| /|
      B_Sat_Add, B_Sat_Sub, B_Sat_Mul, B_Sat_Div,
      --  Bitwise / shift (§6.5): & | ^ << >>
      B_And, B_Or, B_Xor, B_Shl, B_Shr,
      --  Widening variants (§6.4.3): +@ *@  — result type .{T, T}
      B_Wide_Add, B_Wide_Mul,
      B_Eq, B_Ne, B_Lt, B_Gt, B_Le, B_Ge,
      --  Contract logical operators (§7.2.2): `&&` / `||` short-circuit and
      --  `^^` (both operands evaluated). All yield bool. Distinct from the
      --  bitwise `^` (B_Xor) — `^^` combines `contract`-typed operands.
      B_LAnd, B_LOr, B_LXor);

   --  Unary prefix operators (§6.3). Bootstrap: negation, bitwise NOT.
   type Unary_Op is (U_Neg, U_Not);

   type Expr_Node (Kind : Expr_Kind := E_Int_Lit) is record
      --  Filled by Kurt.Sema during type analysis; null before then.
      Sem_Ty : Type_Access := null;
      --  §6.6: set when this expression was written inside explicit
      --  parentheses, so the mixed comparison/bitwise constraint treats it
      --  as an opaque group (parentheses are otherwise transparent).
      Was_Paren : Boolean := False;
      case Kind is
         when E_Int_Lit =>
            Int_V      : Long_Long_Integer := 0;
            Int_Suffix : SU.Unbounded_String;  --  e.g. "si4"; empty = none
         when E_Float_Lit =>
            Float_V      : Long_Float := 0.0;
            Float_Suffix : SU.Unbounded_String;  --  e.g. "fe8m23"; empty=none
            --  §3.5.2: 0 = ordinary, 1 = `0nan`, 2 = `0inf` (non-finite
            --  values travel as this tag, never as a Long_Float).
            Float_Special : Natural := 0;
         when E_Bool_Lit =>
            Bool_V : Boolean := False;
         when E_String_Lit =>
            Str_Bytes : SU.Unbounded_String;
         when E_Path =>
            Segments    : Path_Segments.Vector;
            --  §6.1.1 trait forced by a qualified path root
            --  `(Type as Trait)::item`; empty for an ordinary path.
            Path_Trait  : SU.Unbounded_String;
            --  §5.9.2 explicit generic arguments on a callee path,
            --  e.g. the `si4` of `max.<si4>(a, b)`. Consumed by
            --  Kurt.Mono (instantiation); empty otherwise.
            P_Type_Args : Type_Vectors.Vector;
            --  §9.3.2 associated-const access `Type::NAME`: Kurt.Sema
            --  resolves it to the impl's value expression, which codegen
            --  lowers in place. Null for ordinary paths.
            P_Assoc_Val : Expr_Access := null;
            --  §4.10: set by Kurt.Sema when this bare path names a
            --  subroutine used as a value — a subroutine pointer. Codegen
            --  then emits the subroutine's address rather than a load.
            P_Is_Fn_Ptr : Boolean := False;
            --  §8.8.2: set by Kurt.Sema when this bare binding is a transfer
            --  (move) source. Codegen skips the source's scope-exit
            --  destructor (the destruction obligation moved).
            P_Is_Move : Boolean := False;
         when E_Field =>
            F_Recv : Expr_Access;
            F_Name : SU.Unbounded_String;
            --  §9.2.1 trait forced by a qualified method `(e as Trait).m()`;
            --  empty for an ordinary `e.m()`.
            F_Trait : SU.Unbounded_String;
         when E_Call =>
            C_Callee : Expr_Access;
            C_Args   : Expr_Vectors.Vector;
            --  §4.10: set when the callee is a subroutine-pointer value,
            --  so codegen emits an indirect call (`blr`).
            C_Indirect : Boolean := False;
            --  §9.9 set by Kurt.Sema when the callee is a capturing-closure
            --  value: names the lifted subroutine `$clo_N` to call directly,
            --  passing the address of the callee binding as the hidden
            --  `self` (the capture environment).
            C_Clo_Lift : SU.Unbounded_String;
         when E_If =>
            I_Cond : Expr_Access;
            I_Then : Expr_Access;
            I_Else : Expr_Access;
         when E_Binary =>
            B_Op  : Binary_Op;
            B_Lhs : Expr_Access;
            B_Rhs : Expr_Access;
         when E_Deref =>
            D_Inner : Expr_Access;
         when E_Struct_Lit =>
            SL_Name   : SU.Unbounded_String;          --  struct type name
            SL_Fields : Field_Init_Vectors.Vector;
         when E_Variant_New =>
            VN_Enum    : SU.Unbounded_String;         --  enum type name
            VN_Variant : SU.Unbounded_String;         --  variant name
            VN_Fields  : Field_Init_Vectors.Vector;   --  named payload inits
         when E_Match =>
            M_Scrut : Expr_Access;
            M_Arms  : Match_Arm_Vectors.Vector;
         when E_Cast =>
            --  `expr as type`, `expr as ?`, `expr as! type` (§6.8).
            Cast_Inner : Expr_Access;
            Cast_Ty    : Type_Access := null;  --  null for `as ?`
            Cast_Disc  : Boolean := False;     --  `as ?` discriminant extract
            Cast_Bang  : Boolean := False;     --  `as!` bitwise reinterpret
         when E_Unary =>
            U_Op      : Unary_Op;
            U_Operand : Expr_Access;
         when E_Tuple_Lit =>
            TL_Elems : Expr_Vectors.Vector;
         when E_Question =>
            Q_Inner : Expr_Access;
         when E_Ref =>
            --  §8.1: reference-creation expression. The place is a binding
            --  path or field access; the result is `sigil [mods] T`.
            Rf_Sigil    : Ref_Sigil := R_Shared;
            Rf_Volatile : Boolean   := False;
            Rf_Store    : Ref_Store := RS_None;
            Rf_Place    : Expr_Access;
         when E_Extract =>
            --  §7.2.3: Ex_Inner shall satisfy `contract`. On success this
            --  expression's value is Ex_Inner's success payload; on
            --  failure, Ex_Err (empty = none) binds the failure payload
            --  within Ex_Fallback alone, and Ex_Fallback's value (or
            --  divergence) is the result instead.
            Ex_Inner    : Expr_Access;
            Ex_Err      : SU.Unbounded_String;
            Ex_Fallback : Expr_Access;
         when E_CAS =>
            --  §8.7: `target >.< expected then new` (eq-CAS) or `>!<`
            --  (ne-CAS). Result type is verdict.<T, T>.
            CAS_Tgt : Expr_Access;
            CAS_Exp : Expr_Access;
            CAS_New : Expr_Access;
            CAS_Ne  : Boolean := False;   --  True for `>!<`
         when E_Array_Lit =>
            --  §6.1.6: element list, or repeat form `[v; N]` when
            --  AL_Repeat_Expr is non-null (AL_Elems then holds the single
            --  v). N need not be a bare literal -- Infer_Array_Lit
            --  resolves it via Kurt.Parser.Fold_Int_Expr into AL_Repeat.
            AL_Elems       : Expr_Vectors.Vector;
            AL_Repeat      : Cell_Count := 0;
            AL_Repeat_Expr : Expr_Access := null;
         when E_Dyn_Cast =>
            --  §9.5 implicit `&T → &dyn Trait` coercion. Materialises the
            --  fat reference { ptr = inner, dtable = &dtable(T, Trait) }.
            --  DC_Inner is the `&T` reference expression; DC_Conc names
            --  the concrete type T; DC_Trait names the trait.
            DC_Inner : Expr_Access;
            DC_Conc  : SU.Unbounded_String;
            DC_Trait : SU.Unbounded_String;
         when E_Slice_Cast =>
            --  §4.6 implicit `&[T; N] → &[T]` coercion. Materialises the
            --  fat reference { ptr = inner (array address), len = N }.
            SC_Inner : Expr_Access;
            SC_Len   : Cell_Count := 0;
         when E_Type_Intrinsic =>
            --  §6.12 layout intrinsics. Implicitly xlatime: sema/codegen
            --  fold them to `uaddr` constants. Bootstrap subset: the
            --  type operand is a named type, ops are size/align/offset.
            TI_Ty    : Type_Access;
            TI_Op    : Type_Intrinsic_Op := TI_Size;
            TI_Field : SU.Unbounded_String;   --  TI_Offset only
         when E_Uninit =>
            null;   --  §6.1.8: no payload; type comes from the assignment
         when E_Closure =>
            --  §9.9 closure expression. Clo_Body is the block body; the
            --  short form `/.p/ <- e` is desugared at parse time into a
            --  single `return e;`. Clo_Fn_Name is the implementation-anonymous
            --  subroutine the closure lowers to (filled by codegen). The
            --  bootstrap lowers non-capturing closures (those that reference
            --  no enclosing binding) to a plain subroutine usable as `fn`.
            Clo_Params  : Closure_Param_Vectors.Vector;
            Clo_Ret     : Type_Access := null;   --  null = inferred
            Clo_Body    : Stmt_Vectors.Vector;
            Clo_Xfer    : Boolean := False;
            Clo_Fn_Name : SU.Unbounded_String;
            --  §9.9.3 captured bindings (free variables referencing the
            --  enclosing scope). Filled syntactically by Kurt.Mono (names);
            --  Kurt.Sema fills each capture's type from the creating scope.
            --  Empty => a non-capturing closure (a plain subroutine pointer).
            --  Clo_Env_Name is the anonymous capture-struct type
            --  `$clo_N$env`; the closure value has this type when capturing.
            Clo_Caps     : Closure_Param_Vectors.Vector;
            Clo_Env_Name : SU.Unbounded_String;
         when E_Destruct =>
            --  §8.4/§8.11: `destruct(e)` runs e's destructor immediately;
            --  `undestruct(e)` reclaims storage without running it (airside).
            --  Both consume (invalidate) the operand binding; type is void.
            DT_Inner : Expr_Access;
            DT_Undo  : Boolean := False;   --  True for `undestruct`
         when E_Airside_Blk =>
            --  §6.9/§7.8 a brace block in an expression position. Its value
            --  is yielded by a trailing `express`; with none, `void`.
            --  (Bootstrap: only the trailing-`express` form yields a value —
            --  an early `express` from a nested position is not supported.)
            --  `AB_Airside` distinguishes `airside { … }` (§6.9, enters the
            --  airside region) from a plain `{ … }` express block (§7.8).
            AB_Stmts   : Stmt_Vectors.Vector;
            AB_Airside : Boolean := True;
            AB_Label   : SU.Unbounded_String;  --  §7.9 block label; empty=none
         when E_Loop =>
            --  §7.7 `loop { … }` as an expression. Its value is supplied by
            --  a `break expr` targeting it; an infinite loop with no such
            --  break has type `never`.
            Loop_Body : Stmt_Vectors.Vector;
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Statements (§7 — bootstrap subset)
   ----------------------------------------------------------------------

   type Stmt_Kind is
     (S_Return,         --  "return" expr ";"
      S_Expr,           --  expr ";"
      S_Airside_Block,  --  "airside" "{" stmts "}"  (no trailing ";")
      S_Let,            --  "let" IDENT [: type] "=" expr ";"
      S_Mut,            --  "mut" IDENT [: type] [= expr] ";"
      S_Assign,         --  place "=" expr ";"
      S_While,          --  "while" cond "{" stmts "}"
      S_If,             --  "if" cond "{" stmts "}" ["else" ("{"...} | if)]
      S_Break,          --  "break" [expr] ";"   (§7.7 optional loop value)
      S_Continue,       --  "continue" ";"
      S_Express,        --  "express" expr ";"   (§7.8 block exit-with-value)
      S_Fence,          --  "@guard"/"@volatile" [".start"|".end"] (§8.5.3)
      S_Trap,           --  "@trap" ";"   termination primitive (§7.10)
      S_Asm);           --  "asm" "{" … "}"   inline assembly (§6.11)

   --  §8.5.3 fence forms: forward boundary, backward boundary, or the
   --  fully ordered standalone form.
   type Fence_Form is (FF_Full, FF_Start, FF_End);

   type Stmt_Node (Kind : Stmt_Kind := S_Return) is record
      case Kind is
         when S_Return =>
            R_Val : Expr_Access;
         when S_Expr =>
            E_Val : Expr_Access;
         when S_Airside_Block =>
            A_Stmts : Stmt_Vectors.Vector;
         when S_Let | S_Mut =>
            L_Name : SU.Unbounded_String;
            L_Ty   : Type_Access;    --  null if inferred
            L_Init : Expr_Access;    --  null: deferred init (S_Mut/S_Let)
            --  Tuple destructuring `let .{a, b} = e;` (§4.7). When
            --  non-empty, the names bind the tuple's positional fields and
            --  L_Name is unused.
            L_Tuple_Names : Path_Segments.Vector;
            --  §5.2.1 refutable let-else: `let Enum::V { binds } = e else
            --  { diverge };`. On a match the payload binds for the rest of
            --  the enclosing scope; on a mismatch the (diverging) else block
            --  runs. L_Init is the scrutinee.
            L_Is_Refut : Boolean := False;
            L_Refut_Pat : Pattern;
            L_Else      : Stmt_Vectors.Vector;
            --  §5.3: statement-position `const NAME: T = expr;` (Kind =
            --  S_Let, so already single-assignment). Check_Let further
            --  requires an xlatime-foldable initializer, like a top-level
            --  `const` -- but (bootstrap limitation) its value is not
            --  usable in an array-length position `[T; N]`.
            L_Is_Const : Boolean := False;
         when S_Assign =>
            Asn_Lhs : Expr_Access;
            Asn_Rhs : Expr_Access;
         when S_While =>
            W_Cond  : Expr_Access;
            W_Body  : Stmt_Vectors.Vector;
            W_Then  : Stmt_Vectors.Vector;  --  §7.5.3 step block; may be empty
            W_Label : SU.Unbounded_String;  --  §7.9 `'name:` loop label; empty=none
            --  §7.5.1 `while let PAT = e { }`: W_Cond is the scrutinee, tested
            --  on each iteration; the loop exits when the pattern fails to
            --  match. Mirrors `if let` (SI_Is_Let / SI_Let_Pat).
            W_Is_Let  : Boolean := False;
            W_Let_Pat : Pattern;
            --  §7.5.1 `while cond -> v { }`: W_Cond is a contract value tested
            --  each iteration; on the success variant its payload binds to
            --  W_Succ_Bind in the body, on the failure variant the loop exits.
            --  (`while` provides `-> v` but not `| e`.)
            W_Is_Contract : Boolean := False;
            W_Succ_Bind   : SU.Unbounded_String;
         when S_If =>
            SI_Cond : Expr_Access;
            SI_Then : Stmt_Vectors.Vector;
            SI_Else : Stmt_Vectors.Vector;  --  empty when no else
            --  Contract-binding form `if e -> v | err { } else { }` (§7):
            --  the cond is a contract value; on success its payload binds
            --  to SI_Succ_Bind in the then-block, on failure to
            --  SI_Fail_Bind in the else-block.
            SI_Is_Contract : Boolean := False;
            SI_Succ_Bind   : SU.Unbounded_String;
            SI_Fail_Bind   : SU.Unbounded_String;  --  empty if no `| err`
            --  §7.3.3 `if let PAT = e { } else { }`: SI_Cond is the
            --  scrutinee, SI_Let_Pat the refutable variant pattern (with
            --  positional payload bindings). The bootstrap requires the
            --  scrutinee to be a binding (a place), like `?` and `if ->`.
            SI_Is_Let  : Boolean := False;
            SI_Let_Pat : Pattern;
         when S_Break =>
            --  Optional value form `break expr;` (§7.7). null = no value.
            Brk_Val   : Expr_Access;
            --  §7.9 `break 'label [expr];` target loop label; empty = innermost.
            Brk_Label : SU.Unbounded_String;
         when S_Continue =>
            --  §7.9 `continue 'label;` target loop label; empty = innermost.
            Cont_Label : SU.Unbounded_String;
         when S_Express =>
            Xp_Val   : Expr_Access;
            Xp_Label : SU.Unbounded_String;  --  §7.9 target block label
         when S_Fence =>
            --  §8.5.3: Fn_Guard selects @guard (execution fence, hardware
            --  barrier) over @volatile (translation fence, no instruction).
            Fn_Guard : Boolean := True;
            Fn_Form  : Fence_Form := FF_Full;
         when S_Trap =>
            --  §7.10 `@trap;` — diverging termination primitive; no fields.
            null;
         when S_Asm =>
            --  §6.11 inline assembly — the raw instruction body, emitted
            --  verbatim, plus optional `with { … }` operand constraints.
            --  Bootstrap: operand targets are concrete registers (e.g. x0),
            --  referenced directly in the body. `in(REG)=e` loads e into REG
            --  before the body; `out(REG)->name` stores REG into the place
            --  after; `io(REG)=e->name` does both; `clobber(...)` is recorded
            --  but unused (the non-optimizing codegen keeps no live registers
            --  across statements).
            Asm_Body      : SU.Unbounded_String;
            Asm_In_Regs   : Path_Segments.Vector;
            Asm_In_Exprs  : Expr_Vectors.Vector;
            Asm_Out_Regs  : Path_Segments.Vector;
            Asm_Out_Names : Path_Segments.Vector;
            Asm_Clobbers  : Path_Segments.Vector;
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Parameters and fn header
   ----------------------------------------------------------------------

   type Param is record
      Name   : SU.Unbounded_String;  --  empty for prototype unnamed
      Ty     : Type_Access;
      Is_Mut : Boolean := False;     --  §5.1 `mut name: T` mutable parameter
   end record;

   package Param_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Param);

   --  §5.9 generic parameter with optional builtin bounds, e.g.
   --  `.<T: numeric, U>`. An empty Bounds vector is an unconstrained
   --  parameter — an opaque layout under the type-erasure semantics.
   type Generic_Param is record
      Name   : SU.Unbounded_String;
      Bounds : Path_Segments.Vector;
   end record;

   package Generic_Param_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Generic_Param);

   --  §5.1 header. Spec ordering:
   --      [ pub | extern[(iface)] ] [ variadic[(name:T)] ] [ airside ]
   --      fn IDENT '(' params ')' [ '->' type ]
   type Fn_Header is record
      Name           : SU.Unbounded_String;
      Generic_Params : Generic_Param_Vectors.Vector;  --  .<T[: bound], ...>
      Params         : Param_Vectors.Vector;
      Return_Type : Type_Access;     --  null => void (or never, see Is_Never)
      Is_Pub      : Boolean := False;
      Is_Extern   : Boolean := False;
      --  §5.1.2 `extern(iface)` invocation interface name; "" = native.
      Extern_Iface : SU.Unbounded_String;
      Is_Variadic : Boolean := False;
      Is_Airside  : Boolean := False;
      --  §4.10/§7.11 `-> never`: diverges, yields no value (like `void`);
      --  Return_Type stays null.
      Is_Never    : Boolean := False;
      --  §5.14 inlining directives; the bootstrap performs no inlining,
      --  so these are recorded/checked but have no codegen effect.
      Is_Inline    : Boolean := False;  --  @inline
      Is_No_Inline : Boolean := False;  --  @no_inline
      --  §5.15 `@symbol "name"`: external symbol override; empty = derive
      --  the external name from the identifier. Valid only with `extern`
      --  or inside a `@dyn` block.
      Symbol_Name  : SU.Unbounded_String;
      --  variadic(name: T): retained for future codegen; ignored now.
      Variadic_Name : SU.Unbounded_String;
      Variadic_Ty   : Type_Access;
      --  §9.9 set on a subroutine lifted from a closure expression. When its
      --  Return_Type is null, sema infers it from the body's `return` (the
      --  short/standard closure forms omit the return type).
      Is_Closure   : Boolean := False;
   end record;

   type Fn_Decl is record
      Header     : Fn_Header;
      Body_Stmts : Stmt_Vectors.Vector;
   end record;
   subtype Fn_Proto is Fn_Header;

   package Fn_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Fn_Decl);
   package Proto_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Fn_Proto);

   ----------------------------------------------------------------------
   --  @dyn declarations (§10.3 — bootstrap subset)
   ----------------------------------------------------------------------

   type Dyn_Decl is record
      Alias  : SU.Unbounded_String;
      Is_Pub : Boolean := False;
      Items  : Proto_Vectors.Vector;
      --  §10.4 bound form `@dyn [prefix::]"path" as name`: the source path
      --  identifying the opaque code. Empty = unbound (host link mechanism).
      Bound_Path : SU.Unbounded_String;
   end record;

   package Dyn_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Dyn_Decl);

   ----------------------------------------------------------------------
   --  struct declarations (§5.5 — bootstrap subset: named fields only,
   --  no modifiers, defaults, generics, or with-clauses yet)
   ----------------------------------------------------------------------

   type Struct_Field is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
      --  §5.5.1 field modifiers.
      Is_Mut     : Boolean := False;  --  `mut` — field is atomically storable
      Is_Pub     : Boolean := False;  --  `pub` — field is externally visible
      Is_Airside : Boolean := False;  --  `airside` — airside-only field
      --  §5.5.3 default-value expression (`= expr`); null when the field has
      --  no default and must be supplied in every composite literal.
      Default : Expr_Access := null;
   end record;

   package Struct_Field_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Struct_Field);

   type Struct_Decl is record
      Name           : SU.Unbounded_String;
      --  §10.3: visible under a `@add`-ing unit's namespace only if `pub`.
      Is_Pub         : Boolean := False;
      --  §5.9: `.<T[: bound ['lifetime]], ...>` — parsed/recorded here;
      --  instantiation enforcement is out of scope (type erasure).
      Generic_Params : Generic_Param_Vectors.Vector;
      Fields         : Struct_Field_Vectors.Vector;
      Repr_Packed    : Boolean := False;   --  §4.11.4 `with repr(packed)`
      Align_N        : Cell_Count := 0;    --  §4.11.5 `with align(N)`; 0=none
      --  §8.11 `with destruct [block]`: an uncopyable type with transfer
      --  semantics. Destruct_Block is the optional destructor body (its
      --  `self` is `$selftype`); empty when omitted.
      Has_Destruct   : Boolean := False;
      Destruct_Block : Stmt_Vectors.Vector;
      --  §8.10 `with concurrent [!]transfer / [!]reference` context-safety
      --  markers. The positive forms grant the property; the `!` forms block
      --  propagation. A positive and its negation on the same type is a
      --  translation failure (checked at the declaration).
      Conc_Transfer    : Boolean := False;
      Conc_No_Transfer : Boolean := False;
      Conc_Reference   : Boolean := False;
      Conc_No_Reference : Boolean := False;
      --  §9.9 closure environment: non-empty names the lifted subroutine
      --  `$clo_N(self, params...)` a closure value of this type invokes.
      Clo_Lift : SU.Unbounded_String := SU.Null_Unbounded_String;
      --  §8.4.3 `with lifetime` chains; governs field destruction order.
      Lifetime_Chains : Lifetime_Chain_Vectors.Vector;
   end record;

   package Struct_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Struct_Decl);

   ----------------------------------------------------------------------
   --  enum declarations (§5.6 — bootstrap subset: unit variants only,
   --  optional explicit discriminant value)
   ----------------------------------------------------------------------

   type Enum_Variant is record
      Name    : SU.Unbounded_String;
      Value   : Long_Long_Integer;  --  resolved (or canonical) discriminant
      Is_Wild : Boolean := False;   --  declared `= #wild#` / `#wild#(V)`
      Wild_Canon : Boolean := False; --  parenthesised `#wild#(V)` form
      Auto_Disc  : Boolean := False; --  §5.7 needs occupied-set auto-assignment
      Payload : Struct_Field_Vectors.Vector;  --  named fields; empty = unit
   end record;

   package Enum_Variant_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Enum_Variant);

   type Enum_Decl is record
      Name           : SU.Unbounded_String;
      Is_Pub         : Boolean := False;   --  §10.3
      --  §5.9: see Struct_Decl.Generic_Params.
      Generic_Params : Generic_Param_Vectors.Vector;
      Is_Contract    : Boolean := False;       --  declared `with contract`
      --  §7.2 `!contract` inverts polarity (#wild# = success); the optional
      --  `-> inv_type` pair (null = none) is symmetry-checked in Validate_Enums.
      Contract_Inv   : Boolean := False;
      Inv_Type       : Type_Access := null;
      Discrim_Ty     : Type_Access := null;    --  `with discrim(T)` (§4.11.3)
      Repr_Packed    : Boolean := False;    --  §4.11.3 `with repr(packed)`
      --  §4.11.2: an explicit numeric discriminant value on any variant
      --  disqualifies the void-discriminant special case.
      Any_Explicit   : Boolean := False;
      Variants       : Enum_Variant_Vectors.Vector;
      --  §8.11 `with destruct [block]` (see Struct_Decl).
      Has_Destruct   : Boolean := False;
      Destruct_Block : Stmt_Vectors.Vector;
      --  §8.10 `with concurrent` markers (see Struct_Decl).
      Conc_Transfer    : Boolean := False;
      Conc_No_Transfer : Boolean := False;
      Conc_Reference   : Boolean := False;
      Conc_No_Reference : Boolean := False;
      --  §8.4.3 `with lifetime` chains (see Struct_Decl).
      Lifetime_Chains : Lifetime_Chain_Vectors.Vector;
   end record;

   package Enum_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Enum_Decl);

   ----------------------------------------------------------------------
   --  Translation unit
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   --  trait declarations (§9.3 — bootstrap subset: method signatures and
   --  default methods. Associated types/consts and supertraits deferred.)
   ----------------------------------------------------------------------

   type Trait_Method is record
      Sig       : Fn_Header;          --  self param + others + return
      Has_Body  : Boolean := False;   --  default method?
      Body_Stmts : Stmt_Vectors.Vector;
   end record;

   package Trait_Method_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Trait_Method);

   --  §9.3.2 associated constant: `const NAME: type [= default];`. In a
   --  trait the default is optional; an impl always provides a value.
   type Assoc_Const is record
      Name      : SU.Unbounded_String;
      Ty        : Type_Access;
      Val       : Expr_Access;        --  null if no default (trait side)
      Has_Val   : Boolean := False;
   end record;

   package Assoc_Const_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Assoc_Const);

   --  §9.3.1 associated type. On a trait: `type Item [= Default];` (Ty is the
   --  default, null = required). On an impl: `type Item = Concrete;` (Ty is
   --  the concrete type).
   type Assoc_Type is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access := null;
   end record;

   package Assoc_Type_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Assoc_Type);

   type Trait_Decl is record
      Name        : SU.Unbounded_String;
      Is_Pub      : Boolean := False;   --  §10.3

      Methods     : Trait_Method_Vectors.Vector;
      Consts      : Assoc_Const_Vectors.Vector;
      Assoc_Types : Assoc_Type_Vectors.Vector;   --  §9.3.1 `type Item [= D];`
      --  §9.3.3 direct supertraits (`with { selftype: Bar + Baz }`), in
      --  declaration order. Each occupies a Zone-B dispatch-table field.
      Supertraits : Path_Segments.Vector;
   end record;

   package Trait_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Trait_Decl);

   --  An `impl Type as Trait` record — the methods are also lowered into
   --  Fns as `Type$method`; this records the (Type, Trait) pair so the
   --  checker and dispatch-table emitter can find them.
   type Trait_Impl is record
      Ty_Name    : SU.Unbounded_String;
      Trait_Name : SU.Unbounded_String;
      Methods    : Path_Segments.Vector;  --  method names provided
      Consts     : Assoc_Const_Vectors.Vector;  --  associated-const values
      Assoc_Types : Assoc_Type_Vectors.Vector;  --  §9.3.1 `type Item = C;`
   end record;

   package Trait_Impl_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Trait_Impl);

   --  §9.1 / §9.4 generic implementation `impl(P...) Owner.<P...> [as Trait]`.
   --  The method is a template: its body keeps the `selftype` placeholder and
   --  references the impl parameters `Gen_Params`. Kurt.Mono specialises it
   --  per concrete owner instance (e.g. `Box$si4$get`) when that instance
   --  is generated, substituting the impl parameters and rewriting `selftype`
   --  to the mangled owner instance name.
   type Gen_Method is record
      Owner      : SU.Unbounded_String;          --  generic base, e.g. "Box"
      Trait_Name : SU.Unbounded_String;          --  empty => inherent
      Gen_Params : Generic_Param_Vectors.Vector; --  the `impl(...)` list
      Method     : Fn_Decl;        --  Header.Name = bare method name
   end record;

   package Gen_Method_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Gen_Method);

   --  §5.3 top-level translation-time constant.
   type Const_Decl is record
      Name   : SU.Unbounded_String;
      Is_Pub : Boolean := False;   --  §10.3
      Ty     : Type_Access;
      Init   : Expr_Access;
   end record;

   package Const_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Const_Decl);

   --  §5.4 global binding (`static` / `static mut`).
   type Static_Decl is record
      Name   : SU.Unbounded_String;
      Is_Mut : Boolean := False;
      Is_Pub : Boolean := False;   --  §10.3
      Ty     : Type_Access;
      Init   : Expr_Access;
   end record;

   package Static_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Static_Decl);

   --  §9.8.5 a deferred `destruct` / `!destruct` bound obligation: at
   --  instantiation time Kurt.Mono cannot yet consult the layout model
   --  (Kurt.Layout.Register runs after it), so each destruct-family bound
   --  on a generic parameter is recorded against the concrete argument
   --  and validated by Kurt.Sema once the unit is registered.
   type Bound_Check is record
      Bound : SU.Unbounded_String;   --  "destruct" or "!destruct"
      Ty    : Type_Access;           --  the concrete type argument
      Param : SU.Unbounded_String;   --  the generic parameter's name
      Ctx   : SU.Unbounded_String;   --  the instantiated template's name
   end record;

   package Bound_Check_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Bound_Check);

   type Translation_Unit is record
      Fns        : Fn_Vectors.Vector;
      Dyns       : Dyn_Vectors.Vector;
      Structs    : Struct_Vectors.Vector;
      Enums      : Enum_Vectors.Vector;
      Traits     : Trait_Vectors.Vector;
      Trait_Impls : Trait_Impl_Vectors.Vector;
      Consts     : Const_Vectors.Vector;    --  §5.3
      Statics    : Static_Vectors.Vector;   --  §5.4
      Gen_Methods : Gen_Method_Vectors.Vector;  --  §9.1/§9.4 generic impl
      --  §5.9 generic subroutine templates, lifted out of Fns by
      --  Kurt.Mono. Checked once by Kurt.Sema under the type-erasure
      --  rule (§5.9.2); never lowered by codegen — only their
      --  monomorphised instances (back in Fns) are.
      Gen_Fns : Fn_Vectors.Vector;
      --  §5.9 generic struct/enum templates, lifted out of Structs/Enums
      --  by Kurt.Mono the same way Gen_Fns is. Kept so Kurt.Sema can
      --  resolve a field access on `self` inside a never-instantiated
      --  impl(...)  method template (see U.Gen_Methods and Kurt.Sema.
      --  Check.Infer.Infer_Field) -- otherwise this data would simply be
      --  discarded once Kurt.Mono.Monomorphize returns, since only
      --  concrete/generated declarations stay in Structs/Enums.
      Gen_Structs : Struct_Vectors.Vector;
      Gen_Enums   : Enum_Vectors.Vector;
      --  §9.8.5 deferred destruct-family bound obligations (see
      --  Bound_Check above); appended by Kurt.Mono, validated by
      --  Kurt.Sema.
      Bound_Checks : Bound_Check_Vectors.Vector;
      --  §7.10.1 the single `@trap { ... }` handler for this translation
      --  unit, if one is declared. At most one is permitted.
      Has_Trap_Handler : Boolean := False;
      Trap_Handler     : Stmt_Vectors.Vector;
      --  §10.2/§10.3 `@add [prefix::]"path" as name;` source imports declared
      --  in this unit, in source order. Adds holds the path; Add_Prefixes the
      --  parallel `@path` prefix (empty = none); Add_Names the mandatory
      --  namespace identifier used to access the import as `name::item`.
      Adds         : Path_Segments.Vector;
      Add_Prefixes : Path_Segments.Vector;
      Add_Names    : Path_Segments.Vector;
      --  §10.3 `@add pub ... as name;` — whether each entry's namespace
      --  identifier is itself re-exported to importers of this source
      --  unit (parallel to Add_Names/Adds/Add_Prefixes).
      Add_Pubs     : Bool_Vectors.Vector;
      --  §10.5 `@path "base" as name;` search-path prefixes (parallel).
      Path_Names : Path_Segments.Vector;
      Path_Bases : Path_Segments.Vector;
      --  §5.13 top-level `asm { … }` blocks, emitted verbatim into the text
      --  section (raw bodies, in declaration order).
      Top_Asm : Path_Segments.Vector;
      --  §10.6 the mangled prefixes of every `module` closed in this unit,
      --  innermost first (e.g. "a$b" then "a" for `module a { module b …`).
      --  Each doubles as its own namespace alias so `a::b::item` collapses
      --  to `a$b$item` through the ordinary alias machinery.
      Module_Names : Path_Segments.Vector;
      --  §10.6 whether each Module_Names entry was declared `pub module`
      --  (parallel to Module_Names). Governs whether the namespace step is
      --  reachable from an importing source unit; same-unit access is
      --  unaffected either way (see Kurt.Parser.Resolve_Aliases).
      Module_Pubs : Bool_Vectors.Vector;
      --  §5.12.2 `use path::name;` declarations local to this source unit
      --  (not merged -- like Adds, fully resolved and consumed by
      --  Kurt.Parser.Resolve_Aliases before this unit is merged into its
      --  importer). Use_Names holds each imported BARE identifier;
      --  Use_Paths holds the full path it was written against (before
      --  alias resolution).
      Use_Names : Path_Segments.Vector;
      Use_Paths : Segment_Path_Vectors.Vector;
   end record;

   --  §10.2 merge an imported unit's declarations into Into (appends every
   --  declaration vector). The trap handler and `Adds` are not merged.
   procedure Merge_Unit
     (Into : in out Translation_Unit; From : Translation_Unit);

   --  §10.3 namespace mangling. A single walker handles both directions:
   --
   --  1. Apply_Namespace(U, Prefix): called on a `@add`-ed unit's own AST,
   --     right before it is merged into its importer. Every name U itself
   --     declares (struct/enum/trait/fn/const/static) is prefixed
   --     `Prefix$name` (matching the existing `Type$method` impl-mangling
   --     scheme), and every reference to those names *within U's own AST*
   --     is rewritten to match, so U stays internally self-consistent.
   --     Only `pub`-marked declarations remain externally reachable; non-pub
   --     ones are still renamed (for internal consistency) but Resolve_Aliases
   --     below refuses to reach them from outside.
   --
   --  2. Resolve_Aliases(U, Alias_Names, Alias_Prefixes): called once on the
   --     fully-merged top-level unit. A 2-segment reference `alias::item`
   --     (value path, or a `Head::Item` compound type name) where `alias`
   --     matches an `@add ... as alias;` site is rewritten to the single
   --     mangled name `prefix$item` — reusing all of the ordinary
   --     single-segment resolution machinery unchanged. A 3+-segment
   --     reference `alias::Head::Rest` collapses the first two segments into
   --     `prefix$Head` and keeps the remainder, so a qualified enum path or
   --     similar nested access still resolves against the renamed
   --     declaration. Both operations no-op instead of mangling a name
   --     that doesn't need it, so it is safe to call unconditionally.
   --  Starting index (1-based, into the *current* length of the matching
   --  Translation_Unit vector) for a slice-restricted Apply_Namespace call —
   --  used for `module name { ... }`, whose declarations are a SLICE of the
   --  enclosing file's vectors (appended while the module body was parsed),
   --  not a whole separate unit. Defaults (all 1) rename the entire unit,
   --  matching the `@add` use.
   type Rename_From is record
      Fns, Gen_Fns, Structs, Enums, Traits, Trait_Impls, Consts, Statics,
        Gen_Methods : Positive := 1;
   end record;

   --  Current lengths of U's namespaceable vectors, suitable as a
   --  `Rename_From` snapshot marking "everything from here on".
   function Snapshot (U : Translation_Unit) return Rename_From;

   --  `Super_Word` names the path head this rename pass CONSUMES instead of
   --  mangling: a `module` close pass consumes one leading `super` (stepping
   --  a reference out to the enclosing scope, §10.6); the whole-file `@add`
   --  pass consumes a leading `srcroot`. Empty = no head is consumed.
   procedure Apply_Namespace
     (U           : in out Translation_Unit;
      NS_Prefix   : String;
      From        : Rename_From := (others => 1);
      Extra_Names : Path_Segments.Vector := Path_Segments.Empty_Vector;
      Super_Word  : String := "");

   --  §10.3/§10.4/§10.6 resolve every `alias::item` reference in U's own
   --  (not-yet-merged, not-yet-mangled) AST against U's per-source-unit
   --  alias table -- see the design note above Rename_From, and the
   --  implementation note at the top of kurt-parser-resolve_aliases.adb for
   --  the full per-unit-scoping rationale (§10.3's alias-privacy rule).
   --
   --  Pub_Source is the accumulated translation unit so far (every source
   --  unit U itself `@add`s, already merged and mangled) -- used only to
   --  look up whether a resolved cross-unit target is itself `pub`
   --  (Check_Pub); U's own not-yet-merged declarations are not consulted
   --  (a source unit's own names are always usable from within itself,
   --  regardless of `pub`).
   --
   --  Cur_Prefix is the mangling prefix Kurt.Layout.Register_File_Prefix
   --  was just given for U ("" for the root unit) -- used to tell a
   --  same-source-unit `@dyn` symbol access apart from a cross-unit one
   --  (spec 10.4: a non-`pub` `@dyn` symbol is visible within its own
   --  source unit regardless of the enclosing namespace's own `pub`).
   --
   --  Alias_Names/Alias_Prefixes is U's own per-unit alias table: its own
   --  `@add`/`@dyn` sites, its own `module` namespaces (self-mapped), and
   --  anything transitively inherited from a `pub`-marked import (§10.3
   --  `@add pub` re-export / §10.4 `@dyn pub`).
   --
   --  NS_Names/NS_Pubs is the flat, whole-programme registry of every
   --  `module`'s fully mangled namespace prefix and whether it was
   --  declared `pub module` (§10.6) -- consulted for the segment
   --  immediately following an already-resolved cross-unit alias step.
   procedure Resolve_Aliases
     (U              : in out Translation_Unit;
      Pub_Source     : Translation_Unit;
      Cur_Prefix     : String;
      Alias_Names    : Path_Segments.Vector;
      Alias_Prefixes : Path_Segments.Vector;
      NS_Names       : Path_Segments.Vector;
      NS_Pubs        : Bool_Vectors.Vector);

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit;

   --  §5.3/§5.4/§6.10: fold an integer xlatime-evaluable expression to its
   --  Long_Long_Integer value -- literals, unary minus, + - * / % & | ^
   --  << >>, and a path to a top-level integer `const` (via U.Consts,
   --  recursively). False on div/shift errors, overflow, or over-deep
   --  const recursion (§6.10's evaluation limit). Shared by
   --  Kurt.Sema.Check (spec 5.3/5.4) and Kurt.Mono.Monomorphize (spec
   --  4.7/6.1.6) instead of parallel folders.
   function Fold_Int_Expr
     (U : Translation_Unit; E : Expr_Access; Value : out Long_Long_Integer)
      return Boolean;

   Syntax_Error : exception;

end Kurt.Parser;
