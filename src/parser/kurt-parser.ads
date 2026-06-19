--  Kadayif bootstrap parser.
--
--  Coverage: first.kr and hello.kr.
--    * top-level fn definition with parameter list and a body of return /
--      expression / airside-block statements
--    * @dyn declaration with fn prototypes (incl. variadic / pub)
--    * minimal type expressions: NAME, `&` [raw] T, `$` T
--    * minimal expressions: int literal, string literal, path
--      (`a::b::c`), field access (`e.f`), call (`f(args)`)
--
--  Spec references: §3, §5.1, §5.1.2, §6, §7, §10.3.

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

   type Type_Kind is
     (T_Named, T_Ref, T_Tuple, T_Array, T_Dyn, T_Range, T_Fn);
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
            --  `'const`, or a user/inferred name). Lifetimes are a
            --  compile-time discipline with no representation, so the
            --  bootstrap records the name for diagnostics and erases it.
            R_Life     : SU.Unbounded_String := SU.Null_Unbounded_String;
            Target     : Type_Access;
         when T_Tuple =>
            --  §4.7 anonymous tuple `.{T, T, …}` (positional fields).
            Elems : Type_Vectors.Vector;
         when T_Array =>
            --  §4.6 array. `Len > 0` is the fixed-size array `[T; N]`;
            --  `Len = 0` is the unsized slice `[T]` (only valid as a
            --  reference target — `&[T]` is a fat reference).
            Elem : Type_Access;
            Len  : Natural := 0;
         when T_Dyn =>
            --  §9.5 trait object `dyn Trait`. Only meaningful as a
            --  reference referent; `&dyn Trait` is a fat reference
            --  (value ptr + dispatch-table ptr).
            Trait_Name : SU.Unbounded_String;
         when T_Range =>
            --  §4.8 built-in range type. `range_ex.<T>` (exclusive) and
            --  `range_in.<T>` (inclusive) are intrinsic two-field aggregates
            --  { start: T, end: T }, handled structurally like `[T; N]` —
            --  no declaration, no monomorphisation.
            Rng_Inclusive : Boolean := False;
            Rng_Elem      : Type_Access;
         when T_Fn =>
            --  §4.10 subroutine pointer `[extern[(iface)]] [variadic]
            --  [airside] fn (T…) [-> U]`. A pointer-sized value (not a
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
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Forward declarations so Expr/Stmt can refer to each other and
   --  to vectors of themselves.
   ----------------------------------------------------------------------

   type Expr_Node;
   type Expr_Access is access Expr_Node;

   package Expr_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Expr_Access);

   package Path_Segments is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => SU.Unbounded_String,
      "="          => SU."=");

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
      E_CAS,          --  compare-and-swap `t >.< exp <- new` (§8.7)
      E_Array_Lit,    --  `[a, b, c]` / repeat `[v; N]` (§6.1.6)
      E_Dyn_Cast,     --  implicit `&T → &dyn Trait` coercion (§9.5)
      E_Slice_Cast,   --  implicit `&[T; N] → &[T]` coercion (§4.6)
      E_Type_Intrinsic,  --  `T@size` / `T@align` / `T@offset(f)` (§6.12)
      E_Uninit,           --  `uninit` uninitialized value (§6.1.8)
      E_Destruct,         --  `destruct(e)` / `undestruct(e)` (§8.4, §8.11)
      E_Range);           --  `a..b` / `a..=b` range literal (§4.8)
      --  Note: Kurt has no `[]` indexing operator (§6.2). Element access
      --  is `*(arr.ptr + i)` (raw reference arithmetic, §8.6.4) or the
      --  library `.at()` method.

   --  §6.12 layout intrinsic operations (bootstrap subset).
   type Type_Intrinsic_Op is (TI_Size, TI_Align, TI_Offset);

   --  Match patterns (bootstrap subset: enum variant path, integer
   --  literal, or the `#wild#` catch-all).
   type Pattern_Kind is (Pat_Variant, Pat_Int, Pat_Wild);

   type Pattern is record
      Kind     : Pattern_Kind := Pat_Wild;
      Path     : Path_Segments.Vector;  --  Pat_Variant: Enum::Variant
      Int_V    : Long_Long_Integer := 0;  --  Pat_Int
      --  Pat_Variant payload bindings, positional (e.g. `{ w, h }`).
      Bindings : Path_Segments.Vector;
   end record;

   --  A struct-literal field initialiser: `name = expr`.
   type Field_Init is record
      Name : SU.Unbounded_String;
      Val  : Expr_Access;
   end record;

   package Field_Init_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Field_Init);

   --  A match arm: `pattern = expr`. (Block-body arms deferred.)
   type Match_Arm is record
      Pat      : Pattern;
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
      --  Contract logical operators (§7.2.2): && || — short-circuit,
      --  result bool. (Contract `^` reuses B_Xor, disambiguated by type.)
      B_LAnd, B_LOr);

   --  Unary prefix operators (§6.3). Bootstrap: negation, bitwise NOT.
   type Unary_Op is (U_Neg, U_Not);

   type Expr_Node (Kind : Expr_Kind := E_Int_Lit) is record
      --  Filled by Kurt.Sema during type analysis; null before then.
      Sem_Ty : Type_Access := null;
      case Kind is
         when E_Int_Lit =>
            Int_V      : Long_Long_Integer := 0;
            Int_Suffix : SU.Unbounded_String;  --  e.g. "si4"; empty = none
         when E_Float_Lit =>
            Float_V      : Long_Float := 0.0;
            Float_Suffix : SU.Unbounded_String;  --  e.g. "fe8m23"; empty=none
         when E_Bool_Lit =>
            Bool_V : Boolean := False;
         when E_String_Lit =>
            Str_Bytes : SU.Unbounded_String;
         when E_Path =>
            Segments    : Path_Segments.Vector;
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
         when E_Call =>
            C_Callee : Expr_Access;
            C_Args   : Expr_Vectors.Vector;
            --  §4.10: set by Kurt.Sema when the callee is a
            --  subroutine-pointer value rather than a named subroutine, so
            --  codegen emits an indirect call (`blr`).
            C_Indirect : Boolean := False;
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
         when E_CAS =>
            --  §8.7: `target >.< expected <- new` (eq-CAS) or `>!<`
            --  (ne-CAS). Result type is verdict.<T, T>.
            CAS_Tgt : Expr_Access;
            CAS_Exp : Expr_Access;
            CAS_New : Expr_Access;
            CAS_Ne  : Boolean := False;   --  True for `>!<`
         when E_Array_Lit =>
            --  §6.1.6: element list, or repeat form `[v; N]` when
            --  AL_Repeat is non-zero (AL_Elems then holds the single v).
            AL_Elems  : Expr_Vectors.Vector;
            AL_Repeat : Natural := 0;
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
            SC_Len   : Natural := 0;
         when E_Type_Intrinsic =>
            --  §6.12 layout intrinsics. Implicitly xlatime: sema/codegen
            --  fold them to `uaddr` constants. Bootstrap subset: the
            --  type operand is a named type, ops are size/align/offset.
            TI_Ty    : Type_Access;
            TI_Op    : Type_Intrinsic_Op := TI_Size;
            TI_Field : SU.Unbounded_String;   --  TI_Offset only
         when E_Uninit =>
            null;   --  §6.1.8: no payload; type comes from the assignment
         when E_Destruct =>
            --  §8.4/§8.11: `destruct(e)` runs e's destructor immediately;
            --  `undestruct(e)` reclaims storage without running it (airside).
            --  Both consume (invalidate) the operand binding; type is void.
            DT_Inner : Expr_Access;
            DT_Undo  : Boolean := False;   --  True for `undestruct`
         when E_Range =>
            --  §4.8 range literal: low/high bounds and exclusivity. Its type
            --  is the intrinsic T_Range, resolved by sema from the operands.
            Rg_Lo        : Expr_Access;
            Rg_Hi        : Expr_Access;
            Rg_Inclusive : Boolean := False;
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
      S_Extract,        --  "let" v "<-" e "else" [err] "{" … "}" ";"
      S_Break,          --  "break" [expr] ";"   (§7.7 optional loop value)
      S_Continue,       --  "continue" ";"
      S_Express,        --  "express" expr ";"   (§7.8 block exit-with-value)
      S_Fence,          --  "@guard"/"@volatile" [".start"|".end"] (§8.5.3)
      S_Trap);          --  "@trap" ";"   termination primitive (§7.10)

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
            L_Init : Expr_Access;    --  null permitted for S_Mut
            --  Tuple destructuring `let .{a, b} = e;` (§4.7). When
            --  non-empty, the names bind the tuple's positional fields and
            --  L_Name is unused.
            L_Tuple_Names : Path_Segments.Vector;
         when S_Assign =>
            Asn_Lhs : Expr_Access;
            Asn_Rhs : Expr_Access;
         when S_While =>
            W_Cond  : Expr_Access;
            W_Body  : Stmt_Vectors.Vector;
            W_Then  : Stmt_Vectors.Vector;  --  §7.5.3 step block; may be empty
            W_Label : SU.Unbounded_String;  --  §7.9 `'name:` loop label; empty=none
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
            --  scrutinee to be a binding (a place), like `<-` and `if ->`.
            SI_Is_Let  : Boolean := False;
            SI_Let_Pat : Pattern;
         when S_Extract =>
            X_Bind : SU.Unbounded_String;       --  success binding
            X_Expr : Expr_Access;               --  contract value
            X_Err  : SU.Unbounded_String;       --  failure binding (else)
            X_Else : Stmt_Vectors.Vector;       --  else block (diverging)
         when S_Break =>
            --  Optional value form `break expr;` (§7.7). null = no value.
            Brk_Val   : Expr_Access;
            --  §7.9 `break 'label [expr];` target loop label; empty = innermost.
            Brk_Label : SU.Unbounded_String;
         when S_Continue =>
            --  §7.9 `continue 'label;` target loop label; empty = innermost.
            Cont_Label : SU.Unbounded_String;
         when S_Express =>
            Xp_Val : Expr_Access;
         when S_Fence =>
            --  §8.5.3: Fn_Guard selects @guard (execution fence, hardware
            --  barrier) over @volatile (translation fence, no instruction).
            Fn_Guard : Boolean := True;
            Fn_Form  : Fence_Form := FF_Full;
         when S_Trap =>
            --  §7.10 `@trap;` — diverging termination primitive; no fields.
            null;
      end case;
   end record;

   ----------------------------------------------------------------------
   --  Parameters and fn header
   ----------------------------------------------------------------------

   type Param is record
      Name : SU.Unbounded_String;  --  empty for prototype unnamed
      Ty   : Type_Access;
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
      Generic_Params : Generic_Param_Vectors.Vector;  --  .<T[: bound], …>
      Params         : Param_Vectors.Vector;
      Return_Type : Type_Access;     --  null => void (or never, see Is_Never)
      Is_Pub      : Boolean := False;
      Is_Extern   : Boolean := False;
      Is_Variadic : Boolean := False;
      Is_Airside  : Boolean := False;
      --  §4.10/§7.11 `-> never`: the subroutine diverges and yields no
      --  value. Lowered like `void` (no implicit return needed); a call to
      --  it is a diverging expression. Return_Type stays null.
      Is_Never    : Boolean := False;
      --  §5.14 inlining directives. Hints to the transformation pipeline;
      --  the bootstrap performs no inlining, so they are recorded (and
      --  their constraints checked) but otherwise have no codegen effect.
      Is_Inline    : Boolean := False;  --  @inline
      Is_No_Inline : Boolean := False;  --  @no_inline
      --  §5.15 `@symbol "name"`: external symbol override; empty = derive
      --  the external name from the identifier. Valid only with `extern`
      --  or inside a `@dyn` block.
      Symbol_Name  : SU.Unbounded_String;
      --  variadic(name: T): retained for future codegen; ignored now.
      Variadic_Name : SU.Unbounded_String;
      Variadic_Ty   : Type_Access;
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
      --  §5.5.3 default-value expression (`= expr`); null when the field has
      --  no default and must be supplied in every composite literal.
      Default : Expr_Access := null;
   end record;

   package Struct_Field_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Struct_Field);

   type Struct_Decl is record
      Name           : SU.Unbounded_String;
      Generic_Params : Path_Segments.Vector;
      Fields         : Struct_Field_Vectors.Vector;
      Repr_Packed    : Boolean := False;   --  §4.11.4 `with repr(packed)`
      Align_N        : Natural := 0;       --  §4.11.5 `with align(N)`; 0=none
      --  §8.11 `with destruct [block]`: an uncopyable type with transfer
      --  semantics. Destruct_Block is the optional destructor body (its
      --  `self` is `$self_t`); empty when omitted.
      Has_Destruct   : Boolean := False;
      Destruct_Block : Stmt_Vectors.Vector;
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
      Payload : Struct_Field_Vectors.Vector;  --  named fields; empty = unit
   end record;

   package Enum_Variant_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Enum_Variant);

   type Enum_Decl is record
      Name           : SU.Unbounded_String;
      Generic_Params : Path_Segments.Vector;
      Is_Contract    : Boolean := False;       --  declared `with contract`
      Discrim_Ty     : Type_Access := null;    --  `with discrim(T)` (§4.11.3)
      Variants       : Enum_Variant_Vectors.Vector;
      --  §8.11 `with destruct [block]` (see Struct_Decl).
      Has_Destruct   : Boolean := False;
      Destruct_Block : Stmt_Vectors.Vector;
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

   type Trait_Decl is record
      Name        : SU.Unbounded_String;
      Methods     : Trait_Method_Vectors.Vector;
      Consts      : Assoc_Const_Vectors.Vector;
      --  §9.3.3 direct supertraits (`with { self_t: Bar + Baz }`), in
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
   end record;

   package Trait_Impl_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Trait_Impl);

   --  §9.1 / §9.4 generic implementation `impl(P…) Owner.<P…> [as Trait]`.
   --  The method is a template: its body keeps the `self_t` placeholder and
   --  references the impl parameters `Gen_Params`. Kurt.Mono specialises it
   --  per concrete owner instance (e.g. `Box$si4$get`) when that instance
   --  is generated, substituting the impl parameters and rewriting `self_t`
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
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
      Init : Expr_Access;
   end record;

   package Const_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Const_Decl);

   --  §5.4 global binding (`static` / `static mut`).
   type Static_Decl is record
      Name   : SU.Unbounded_String;
      Is_Mut : Boolean := False;
      Ty     : Type_Access;
      Init   : Expr_Access;
   end record;

   package Static_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Static_Decl);

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
      --  §7.10.1 the single `@trap { … }` handler for this translation
      --  unit, if one is declared. At most one is permitted.
      Has_Trap_Handler : Boolean := False;
      Trap_Handler     : Stmt_Vectors.Vector;
   end record;

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit;

   Syntax_Error : exception;

end Kurt.Parser;
