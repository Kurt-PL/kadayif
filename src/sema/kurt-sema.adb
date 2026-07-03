with Ada.Text_IO;
with Ada.Strings.Unbounded;
with Ada.Containers.Vectors;

with Kurt.Layout;
with Kurt.Borrow;

package body Kurt.Sema is

   package IO renames Ada.Text_IO;
   package SU renames Ada.Strings.Unbounded;

   use Kurt.Parser;
   use type Kurt.Borrow.Node_Id;
   use type Kurt.Borrow.Perm_State;

   ----------------------------------------------------------------------
   --  Built-in type constructors (§4). The bootstrap models types with
   --  the parser's AST_Type, so equality is structural on names/sigils.
   ----------------------------------------------------------------------

   function Mk_Named (N : String) return Type_Access is
     (new AST_Type'(Kind => T_Named,
                    Name => SU.To_Unbounded_String (N),
                    Args => <>));

   --  §4.10/§7.11 the `never` type: the result type of a diverging
   --  expression (a `-> never` call). Modelled as the reserved named type
   --  "never"; it is uninhabited, assignable to any target, and dropped in
   --  type unification.
   function Is_Never_Ty (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Named
      and then SU.To_String (T.Name) = "never");

   --  Canonicalise float type aliases (mirrors Kurt.Parser.Canon_Float).
   function Canon_Float (N : String) return String is
     (if    N = "f16"  then "fe5m10"
      elsif N = "bf16" then "fe8m7"
      elsif N = "f32"  then "fe8m23"
      elsif N = "f64"  then "fe11m52"
      elsif N = "f128" then "fe15m112"
      elsif N = "f256" then "fe19m236"
      else  N);

   function Mk_Raw_Ref (Target : Type_Access) return Type_Access is
     (new AST_Type'(Kind => T_Ref, Sigil => R_Raw,
                    R_Volatile => False, R_Store => RS_None,
                    R_Life => SU.Null_Unbounded_String,
                    Target => Target));

   function Mk_Ref
     (Sigil    : Ref_Sigil;
      Volatile : Boolean;
      Store    : Ref_Store;
      Target   : Type_Access) return Type_Access is
     (new AST_Type'(Kind => T_Ref, Sigil => Sigil,
                    R_Volatile => Volatile, R_Store => Store,
                    R_Life => SU.Null_Unbounded_String,
                    Target => Target));

   --  Integer type holding a discriminant of the given cell width and
   --  signedness (§4.11.3 auto-sizing; signed when any declared value
   --  is negative or `discrim(T)` names a signed type).
   function Disc_Ty_Name (Sz : Natural; Signed : Boolean) return String is
     (case Sz is
         when 1      => (if Signed then "si1" else "ui1"),
         when 2      => (if Signed then "si2" else "ui2"),
         when 4      => (if Signed then "si4" else "ui4"),
         when others => (if Signed then "si8" else "ui8"));

   function Image (T : Type_Access) return String is
   begin
      if T = null then
         return "<unknown>";
      end if;
      case T.Kind is
         when T_Named =>
            return SU.To_String (T.Name);
         when T_Ref =>
            return (case T.Sigil is
                       when R_Shared => "&",
                       when R_Excl   => "$",
                       when R_Raw    => "&raw ")
                   & (if T.R_Volatile then "volatile " else "")
                   & (case T.R_Store is
                         when RS_None   => "",
                         when RS_Mut    => "mut ",
                         when RS_Atomic => "atomic ",
                         when RS_Guard  => "guard ")
                   & Image (T.Target);
         when T_Tuple =>
            declare
               R : SU.Unbounded_String := SU.To_Unbounded_String (".{");
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  if I /= T.Elems.First_Index then
                     SU.Append (R, ", ");
                  end if;
                  SU.Append (R, Image (T.Elems.Element (I)));
               end loop;
               SU.Append (R, "}");
               return SU.To_String (R);
            end;
         when T_Array =>
            declare
               L : constant String := T.Len'Image;
            begin
               return "[" & Image (T.Elem) & ";"
                 & L & "]";
            end;
         when T_Dyn =>
            return "dyn " & SU.To_String (T.Trait_Name);
         when T_Fn =>
            declare
               R : SU.Unbounded_String;
            begin
               if SU.Length (T.Fn_Extern) > 0 then
                  SU.Append (R, "extern(" & SU.To_String (T.Fn_Extern) & ") ");
               end if;
               if T.Fn_Variadic then
                  SU.Append (R, "variadic ");
               end if;
               if T.Fn_Airside then
                  SU.Append (R, "airside ");
               end if;
               SU.Append (R, "fn(");
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  if I /= T.Fn_Params.First_Index then
                     SU.Append (R, ", ");
                  end if;
                  SU.Append (R, Image (T.Fn_Params.Element (I)));
               end loop;
               SU.Append (R, ")");
               if T.Fn_Never then
                  SU.Append (R, " -> never");
               elsif T.Fn_Ret /= null then
                  SU.Append (R, " -> " & Image (T.Fn_Ret));
               end if;
               return SU.To_String (R);
            end;
      end case;
   end Image;

   function Is_Integer_Type (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      declare
         N : constant String := SU.To_String (T.Name);
      begin
         return N = "ui1" or else N = "ui2" or else N = "ui4"
             or else N = "ui8" or else N = "ui16" or else N = "ui32"
             or else N = "si1" or else N = "si2" or else N = "si4"
             or else N = "si8" or else N = "si16" or else N = "si32"
             or else N = "uaddr" or else N = "saddr";
      end;
   end Is_Integer_Type;

   function Is_Void_Type (T : Type_Access) return Boolean is
   begin
      return T /= null and then T.Kind = T_Named and then SU.To_String (T.Name) = "void";
   end Is_Void_Type;

   function Is_Float_Type (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      declare
         N : constant String := SU.To_String (T.Name);
      begin
         return N = "fe5m10" or else N = "fe8m7" or else N = "fe8m23"
             or else N = "fe11m52" or else N = "fe15m112"
             or else N = "fe19m236";
      end;
   end Is_Float_Type;

   function Is_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref);

   --  §9.5: a `&dyn Trait` fat reference.
   function Is_Dyn_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref
      and then T.Target /= null and then T.Target.Kind = T_Dyn);

   --  §4.6: a `&[T]` slice fat reference (ref to an unsized array).
   function Is_Slice_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref
      and then T.Target /= null and then T.Target.Kind = T_Array
      and then T.Target.Len = 0);

   --  §4.6: a bare dynamically-sized array `[T]` (Len = 0, not behind a ref).
   --  Permitted only as a reference target; forbidden as a value-position
   --  type (binding / parameter / return / field / element).
   function Is_Unsized_Arr (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Array and then T.Len = 0);

   --  §9.5: a bare `dyn Trait` (not behind a reference) — like `[T]` it has no
   --  static size and is forbidden in value positions.
   function Is_Dyn_Bare (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Dyn);

   --  A type that may not appear in a value position (§4.6 / §9.5).
   function Is_Unsized_Value (T : Type_Access) return Boolean is
     (Is_Unsized_Arr (T) or else Is_Dyn_Bare (T));

   function Is_Uaddr (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Named
      and then SU.To_String (T.Name) = "uaddr");

   --  Forward declaration: structural type equality (defined below).
   function Same_Type (A, B : Type_Access) return Boolean;

   --  §8.5.2: atomic operations are restricted to unsigned integer types
   --  (`ui1`–`ui32`, `uaddr`).
   function Is_Unsigned_Int_Type (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      declare
         N : constant String := SU.To_String (T.Name);
      begin
         return N = "ui1" or else N = "ui2" or else N = "ui4"
             or else N = "ui8" or else N = "ui16" or else N = "ui32"
             or else N = "uaddr";
      end;
   end Is_Unsigned_Int_Type;

   --  §6.5: the unsigned integer type of a given size in cells — the
   --  contextual type of an unsuffixed shift-count literal.
   function Unsigned_Of_Size (Size : Natural) return Type_Access is
      S : constant String := Natural'Image (Size);
   begin
      return new AST_Type'
        (Kind => T_Named,
         Name => SU.To_Unbounded_String ("ui" & S (S'First + 1 .. S'Last)),
         Args => Kurt.Parser.Type_Vectors.Empty_Vector);
   end Unsigned_Of_Size;

   --  §8.1.3 sigil strength rank along the descending chain
   --  `$T(4) → &mut T(3) → &T(2) → &raw T(1) → uaddr(0)`. A storable
   --  shared reference (`&mut`/`&atomic`/`&guard`) ranks 3; a load-only
   --  `&T` ranks 2.
   function Ref_Rank (T : Type_Access) return Natural is
   begin
      if Is_Uaddr (T) then
         return 0;
      elsif T = null or else T.Kind /= T_Ref then
         return 99;   --  not part of the chain
      end if;
      case T.Sigil is
         when R_Raw    => return 1;
         when R_Excl   => return 4;
         when R_Shared =>
            return (if T.R_Store = RS_None then 2 else 3);
      end case;
   end Ref_Rank;

   --  §8.1.3 reference cast classification. Outcome: 0 = permitted,
   --  1 = permitted but requires airside, 2 = translation failure.
   function Ref_Cast_Outcome (Src, Tgt : Type_Access) return Natural is
      RS : constant Natural := Ref_Rank (Src);
      RT : constant Natural := Ref_Rank (Tgt);
   begin
      if RS = 99 or else RT = 99 then
         return 2;   --  not a reference-chain cast
      end if;
      --  Referent type is preserved by `as` (§8.1.3); a change needs as!.
      if Src.Kind = T_Ref and then Tgt.Kind = T_Ref
        and then not Same_Type (Src.Target, Tgt.Target)
      then
         return 2;
      end if;
      --  §8.5.2: atomic/guard references are restricted to unsigned
      --  integer referents — a cast cannot manufacture an atomic
      --  reference to any other type.
      if Tgt.Kind = T_Ref and then Tgt.R_Store in RS_Atomic | RS_Guard
        and then not Is_Unsigned_Int_Type (Tgt.Target)
      then
         return 2;
      end if;
      if RS > RT then
         return 0;                    --  descending: landside
      elsif RS = RT then
         --  Same rank. Storable-shared (rank 3) store-discipline matrix:
         --  mut→atomic/guard OK, atomic↔guard OK, atomic/guard→mut TF.
         if RS = 3 then
            declare
               A : constant Ref_Store := Src.R_Store;
               B : constant Ref_Store := Tgt.R_Store;
            begin
               if A = B then
                  return 0;
               elsif A = RS_Mut then
                  return 0;           --  mut upgrades to atomic/guard
               elsif (A = RS_Atomic and then B = RS_Guard)
                 or else (A = RS_Guard and then B = RS_Atomic)
               then
                  return 0;           --  ordering level change
               else
                  return 2;           --  atomic/guard → mut: TF
               end if;
            end;
         end if;
         return 0;                    --  same rank, volatile-only change
      else
         --  Ascending.
         if RS = 0 and then RT = 1 then
            return 0;                  --  uaddr → &raw: landside
         elsif RS = 1 then
            return 1;                  --  &raw → &/&mut/$: airside
         else
            return 2;                  --  &T→&mut, &T→$, &mut→$: TF
         end if;
      end if;
   end Ref_Cast_Outcome;

   --  §7.2: a type satisfies `contract` iff it is a contract enum.
   --  `bool` (= verdict.<void, void>) is special-cased — the bootstrap
   --  models it as a built-in scalar, not a registered enum.
   function Is_Contract_Ty (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Named
      and then (SU.To_String (T.Name) = "bool"
                or else Kurt.Layout.Is_Contract_Enum
                          (SU.To_String (T.Name))));

   --  §7.2.2 a contract type whose success and failure variants both carry
   --  no payload (`bool` = verdict.<void, void>, or a unit-variant contract
   --  enum). Required of both `^^` operands.
   function Contract_Payloads_Void (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      declare
         EN : constant String := SU.To_String (T.Name);
      begin
         if EN = "bool" then
            return True;
         end if;
         return Kurt.Layout.Variant_Field_Count
                  (EN, Kurt.Layout.Contract_Success_Variant (EN)) = 0
           and then Kurt.Layout.Variant_Field_Count
                  (EN, Kurt.Layout.Contract_Fail_Variant (EN)) = 0;
      end;
   end Contract_Payloads_Void;

   --  Whether a value of type Source may initialise / be assigned to a
   --  place of type Target. Bootstrap rule: identical types only.
   --  null on either side means "unknown" (a prior error) — skip.
   function Assignable (Target, Source : Type_Access) return Boolean;

   function Same_Type (A, B : Type_Access) return Boolean is
   begin
      if A = null or else B = null then
         return A = B;
      end if;
      if A.Kind /= B.Kind then
         return False;
      end if;
      case A.Kind is
         when T_Named =>
            return SU.To_String (A.Name) = SU.To_String (B.Name);
         when T_Ref =>
            return A.Sigil = B.Sigil
              and then A.R_Volatile = B.R_Volatile
              and then A.R_Store = B.R_Store
              and then Same_Type (A.Target, B.Target);
         when T_Tuple =>
            if Natural (A.Elems.Length) /= Natural (B.Elems.Length) then
               return False;
            end if;
            for I in A.Elems.First_Index .. A.Elems.Last_Index loop
               if not Same_Type (A.Elems.Element (I), B.Elems.Element (I))
               then
                  return False;
               end if;
            end loop;
            return True;
         when T_Array =>
            return A.Len = B.Len and then Same_Type (A.Elem, B.Elem);
         when T_Dyn =>
            return SU.To_String (A.Trait_Name)
              = SU.To_String (B.Trait_Name);
         when T_Fn =>
            --  §4.10: identity is the invocation interface, variadic status,
            --  airside, the parameter types, and the return type.
            if SU.To_String (A.Fn_Extern) /= SU.To_String (B.Fn_Extern)
              or else A.Fn_Variadic /= B.Fn_Variadic
              or else A.Fn_Airside /= B.Fn_Airside
              or else A.Fn_Never /= B.Fn_Never
              or else A.Fn_Invocable /= B.Fn_Invocable
              or else A.Fn_Xfer /= B.Fn_Xfer
              or else Natural (A.Fn_Params.Length)
                        /= Natural (B.Fn_Params.Length)
            then
               return False;
            end if;
            for I in A.Fn_Params.First_Index .. A.Fn_Params.Last_Index loop
               if not Same_Type (A.Fn_Params.Element (I),
                                 B.Fn_Params.Element (I))
               then
                  return False;
               end if;
            end loop;
            return Same_Type (A.Fn_Ret, B.Fn_Ret);
      end case;
   end Same_Type;

   function Assignable (Target, Source : Type_Access) return Boolean is
   begin
      if Is_Never_Ty (Source) then
         --  §7.11: a diverging expression is accepted in place of any T.
         return True;
      end if;
      if Target = null or else Source = null then
         return True;  --  unknown; a separate diagnostic already fired
      end if;
      --  §9.9.2 invocable-type coercion ladder. A more permissive target
      --  accepts a less-capturing source when the parameter and return types
      --  match: `fn(T)->U`  ⊑  `/.T/->U`  ⊑  `xfer /.T/->U`. The plain
      --  subroutine pointer flows into either invocable type; a non-`xfer`
      --  invocable flows into the `xfer` form; never the reverse (a capturing
      --  value shall not narrow to a subroutine pointer).
      if Target.Kind = T_Fn and then Source.Kind = T_Fn
        and then (Target.Fn_Invocable /= Source.Fn_Invocable
                  or else Target.Fn_Xfer /= Source.Fn_Xfer)
      then
         declare
            --  Rank: plain fn = 0, `/.T/` = 1, `xfer /.T/` = 2.
            function Rank (T : Type_Access) return Natural is
              (if not T.Fn_Invocable then 0 elsif not T.Fn_Xfer then 1 else 2);
            Match : Boolean :=
              Natural (Target.Fn_Params.Length)
                = Natural (Source.Fn_Params.Length)
              and then SU.To_String (Target.Fn_Extern)
                         = SU.To_String (Source.Fn_Extern)
              and then Target.Fn_Variadic = Source.Fn_Variadic
              and then Target.Fn_Airside = Source.Fn_Airside
              and then Same_Type (Target.Fn_Ret, Source.Fn_Ret);
         begin
            if Match then
               for I in Target.Fn_Params.First_Index ..
                        Target.Fn_Params.Last_Index
               loop
                  if not Same_Type (Target.Fn_Params.Element (I),
                                    Source.Fn_Params.Element (I))
                  then
                     Match := False;
                  end if;
               end loop;
            end if;
            return Match and then Rank (Source) <= Rank (Target);
         end;
      end if;
      return Same_Type (Target, Source);
   end Assignable;

   ----------------------------------------------------------------------
   --  Signature table (Phase 1) and scope (Phase 2)
   ----------------------------------------------------------------------

   type Sig is record
      Name        : SU.Unbounded_String;
      Params      : Param_Vectors.Vector;
      Ret         : Type_Access;
      Is_Variadic : Boolean := False;
      Is_Never    : Boolean := False;   --  §4.10 `-> never`
   end record;

   package Sig_Vec is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Sig);

   type SBinding is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
      --  §2.2.1/§5.1: a `let` binding is single-assignment (immutable after
      --  initialisation); a `mut` binding and a `mut` parameter are mutable.
      --  Defaults to mutable so payload aliases / extract bindings (which are
      --  writable in the bootstrap) need no per-site annotation.
      Is_Mut : Boolean := True;
   end record;

   package SBind_Vec is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => SBinding);

   --  §8.8.2 a binding invalidated by a transfer (move) of a `destruct`
   --  value. Depth is the scope length at the move, for liveness pruning.
   type Moved_Bind is record
      Name  : SU.Unbounded_String;
      Depth : Natural := 0;
   end record;

   package Moved_Vec is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Moved_Bind);

   ----------------------------------------------------------------------
   procedure Check
     (U           : in out Kurt.Parser.Translation_Unit;
      Error_Count : out Natural)
   is
      Errors  : Natural := 0;
      Sigs    : Sig_Vec.Vector;
      Scope   : SBind_Vec.Vector;
      --  §5.17 base index (into Scope) of the current lexical block: a name
      --  declared at-or-above this index is in the *same* scope (a duplicate
      --  declaration = TF); a same-named binding below it is an outer
      --  declaration, which the inner one legally shadows.
      Block_Base : Natural := 0;
      Cur_Ret : Type_Access;
      --  §8.2/§8.3 reference derivation tree for the body being analysed.
      Borrows : Kurt.Borrow.Tree;
      --  §8.8.2 bindings invalidated by a transfer (move).
      Moved   : Moved_Vec.Vector;
      --  §6.1.8/§2.6: airside nesting depth for the statement being
      --  checked. Raised inside an `airside { ... }` block and for the whole
      --  body of an `airside fn`. `uninit` is valid only when this is > 0.
      In_Airside : Natural := 0;
      --  §10.4: mangled names of every subroutine declared in a `@dyn`
      --  block. Invoking one is permitted only within an `airside` region.
      Dyn_Fn_Names : Path_Segments.Vector;
      --  §6.9/§7.8: the expected type flowing into the innermost enclosing
      --  block expression's trailing `express` (steers integer-literal
      --  typing exactly like a `let` annotation would). Null when the
      --  statement being checked is not inside a block expression.
      Express_Expected : Type_Access := null;
      --  §7.9: loop labels currently in scope, innermost last. A `break`/
      --  `continue` with a label shall name one of these.
      Label_Stack : Path_Segments.Vector;
      In_Loop     : Natural := 0;   --  §7.7 plain break/continue need a loop
      --  §5.9.2 type-erasure context: the generic parameters of the
      --  template currently being checked (empty for concrete fns). A
      --  generic subroutine is checked ONCE against the abstract
      --  parameters — never per instantiation — so an operation on `T`
      --  is legal only if T's bounds license it.
      Cur_Generics : Generic_Param_Vectors.Vector;

      procedure Error (Msg : String) is
      begin
         Errors := Errors + 1;
         IO.Put_Line (IO.Standard_Error, "kadayif: type error: " & Msg);
      end Error;

      function Find_Sig (Name : String; Found : out Sig) return Boolean is
      begin
         for I in Sigs.First_Index .. Sigs.Last_Index loop
            if SU.To_String (Sigs.Element (I).Name) = Name then
               Found := Sigs.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Sig;

      function Lookup_Scope (Name : String) return Type_Access is
      begin
         for I in reverse Scope.First_Index .. Scope.Last_Index loop
            if SU.To_String (Scope.Element (I).Name) = Name then
               return Scope.Element (I).Ty;
            end if;
         end loop;
         return null;
      end Lookup_Scope;

      --  §2.2.1: nearest binding's mutability (innermost scope wins, matching
      --  Lookup_Scope's shadowing order). Found is set False when no local
      --  binding of that name exists.
      function Lookup_Scope_Mut
        (Name : String; Found : out Boolean) return Boolean is
      begin
         for I in reverse Scope.First_Index .. Scope.Last_Index loop
            if SU.To_String (Scope.Element (I).Name) = Name then
               Found := True;
               return Scope.Element (I).Is_Mut;
            end if;
         end loop;
         Found := False;
         return False;
      end Lookup_Scope_Mut;

      --  §5.4: whether Name denotes a top-level static binding (and
      --  whether it is `static mut`). Local bindings shadow statics, so
      --  callers check Lookup_Scope first.
      function Find_Static_Decl
        (Name : String; Is_Mut : out Boolean) return Boolean is
      begin
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            if SU.To_String (U.Statics.Element (I).Name) = Name then
               Is_Mut := U.Statics.Element (I).Is_Mut;
               return True;
            end if;
         end loop;
         Is_Mut := False;
         return False;
      end Find_Static_Decl;

      --  §9.3: look up a method signature `M_Name` in trait `Tr_Name`.
      --  Returns the method's signature header (Found set) or leaves
      --  Found False. Searches U.Traits.
      procedure Lookup_Trait_Method
        (Tr_Name, M_Name : String;
         Sig_Out         : out Fn_Header;
         Found           : out Boolean)
      is
      begin
         Found := False;
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            if SU.To_String (U.Traits.Element (I).Name) = Tr_Name then
               declare
                  Tr : Trait_Decl renames U.Traits.Element (I);
               begin
                  for J in Tr.Methods.First_Index ..
                           Tr.Methods.Last_Index
                  loop
                     if SU.To_String (Tr.Methods.Element (J).Sig.Name)
                          = M_Name
                     then
                        Sig_Out := Tr.Methods.Element (J).Sig;
                        Found := True;
                        return;
                     end if;
                  end loop;
               end;
            end if;
         end loop;
      end Lookup_Trait_Method;

      --  §9.3.2: the value expression of associated const Name in the
      --  `impl Ty_Name as <trait>` block (null if none).
      function Find_Impl_Const
        (Ty_Name, Name : String) return Expr_Access
      is
      begin
         for I in U.Trait_Impls.First_Index ..
                  U.Trait_Impls.Last_Index
         loop
            if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
            then
               declare
                  TI : Trait_Impl renames U.Trait_Impls.Element (I);
               begin
                  for J in TI.Consts.First_Index .. TI.Consts.Last_Index
                  loop
                     if SU.To_String (TI.Consts.Element (J).Name) = Name
                     then
                        return TI.Consts.Element (J).Val;
                     end if;
                  end loop;
                  --  §9.3.2 the impl omitted the const — fall back to the
                  --  trait's default value, if the trait declares one.
                  for T in U.Traits.First_Index .. U.Traits.Last_Index loop
                     if SU.To_String (U.Traits.Element (T).Name)
                          = SU.To_String (TI.Trait_Name)
                     then
                        for K in U.Traits.Element (T).Consts.First_Index ..
                                 U.Traits.Element (T).Consts.Last_Index loop
                           if SU.To_String
                                (U.Traits.Element (T).Consts.Element (K).Name)
                                = Name
                             and then U.Traits.Element (T).Consts.Element (K)
                                        .Has_Val
                           then
                              return U.Traits.Element (T).Consts.Element (K)
                                       .Val;
                           end if;
                        end loop;
                     end if;
                  end loop;
               end;
            end if;
         end loop;
         return null;
      end Find_Impl_Const;

      --  §9.3.2: the declared type of associated const Name in any trait
      --  named by generic parameter Gen's bounds (selftype → Gen). Found
      --  is set when located.
      procedure Find_Bound_Const
        (Gen, Name : String; Ty_Out : out Type_Access; Found : out Boolean)
      is
      begin
         Found := False;
         Ty_Out := null;
         for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
            if SU.To_String (Cur_Generics.Element (I).Name) = Gen then
               declare
                  B : Path_Segments.Vector renames
                    Cur_Generics.Element (I).Bounds;
               begin
                  for J in B.First_Index .. B.Last_Index loop
                     for T in U.Traits.First_Index .. U.Traits.Last_Index
                     loop
                        if SU.To_String (U.Traits.Element (T).Name)
                             = SU.To_String (B.Element (J))
                        then
                           declare
                              Tr : Trait_Decl renames
                                U.Traits.Element (T);
                           begin
                              for K in Tr.Consts.First_Index ..
                                       Tr.Consts.Last_Index
                              loop
                                 if SU.To_String
                                      (Tr.Consts.Element (K).Name) = Name
                                 then
                                    Ty_Out := Tr.Consts.Element (K).Ty;
                                    Found := True;
                                    return;
                                 end if;
                              end loop;
                           end;
                        end if;
                     end loop;
                  end loop;
               end;
            end if;
         end loop;
      end Find_Bound_Const;

      --  Substitute the `selftype` placeholder with concrete type Conc in
      --  a (freshly copied) type, e.g. a trait method's return type.
      function Subst_Self_T (T, Conc : Type_Access) return Type_Access is
      begin
         if T = null then
            return null;
         end if;
         case T.Kind is
            when T_Named =>
               if SU.To_String (T.Name) = "selftype" then
                  return Conc;
               end if;
               return T;
            when T_Ref =>
               return Mk_Ref (T.Sigil, T.R_Volatile, T.R_Store,
                              Subst_Self_T (T.Target, Conc));
            when others =>
               return T;
         end case;
      end Subst_Self_T;

      --  §9.4: does concrete type Ty_Name implement Trait Tr_Name?
      function Type_Implements (Ty_Name, Tr_Name : String) return Boolean is
      begin
         for I in U.Trait_Impls.First_Index ..
                  U.Trait_Impls.Last_Index
         loop
            if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
              and then SU.To_String
                (U.Trait_Impls.Element (I).Trait_Name) = Tr_Name
            then
               return True;
            end if;
         end loop;
         return False;
      end Type_Implements;

      --  Is Nm the name of a declared trait?
      function Is_Trait_Name (Nm : String) return Boolean is
      begin
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            if SU.To_String (U.Traits.Element (I).Name) = Nm then
               return True;
            end if;
         end loop;
         return False;
      end Is_Trait_Name;

      --  §9.2.1 resolve the mangled symbol of a method / associated item on a
      --  concrete type. An inherent `Type$item` takes priority; in its absence
      --  a unique trait impl gives `Type$Trait$item`. `Want_Trait` (non-empty)
      --  forces that trait directly — `(e as Trait).item`. Ambiguous is set
      --  when two or more trait impls provide the item and there is no inherent
      --  one and no forced trait.
      procedure Resolve_Item_Symbol
        (Ty_Name, Item, Want_Trait : String;
         Symbol     : out SU.Unbounded_String;
         Found      : out Boolean;
         Ambiguous  : out Boolean)
      is
         Dummy : Sig;
      begin
         Symbol := SU.Null_Unbounded_String;
         Found := False;
         Ambiguous := False;
         if Want_Trait /= "" then
            Symbol := SU.To_Unbounded_String
              (Ty_Name & "$" & Want_Trait & "$" & Item);
            Found := Find_Sig (SU.To_String (Symbol), Dummy);
            return;
         end if;
         if Find_Sig (Ty_Name & "$" & Item, Dummy) then
            Symbol := SU.To_Unbounded_String (Ty_Name & "$" & Item);
            Found := True;
            return;
         end if;
         declare
            Count : Natural := 0;
         begin
            for I in U.Trait_Impls.First_Index ..
                     U.Trait_Impls.Last_Index loop
               if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
               then
                  declare
                     Cand : constant String := Ty_Name & "$"
                       & SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                       & "$" & Item;
                  begin
                     if Find_Sig (Cand, Dummy) then
                        Count := Count + 1;
                        Symbol := SU.To_Unbounded_String (Cand);
                     end if;
                  end;
               end if;
            end loop;
            if Count = 1 then
               Found := True;
            elsif Count >= 2 then
               Ambiguous := True;
               Symbol := SU.Null_Unbounded_String;
            end if;
         end;
      end Resolve_Item_Symbol;

      --  §9.3 / §5.9: if generic parameter Gen carries a trait bound
      --  whose trait declares method M_Name, return its signature.
      procedure Find_Bound_Method
        (Gen, M_Name : String;
         Sig_Out     : out Fn_Header;
         Found       : out Boolean)
      is
      begin
         Found := False;
         for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
            if SU.To_String (Cur_Generics.Element (I).Name) = Gen then
               declare
                  B : Path_Segments.Vector renames
                    Cur_Generics.Element (I).Bounds;
               begin
                  for J in B.First_Index .. B.Last_Index loop
                     Lookup_Trait_Method
                       (SU.To_String (B.Element (J)), M_Name,
                        Sig_Out, Found);
                     if Found then
                        return;
                     end if;
                  end loop;
               end;
            end if;
         end loop;
      end Find_Bound_Method;

      --  Whether T names a generic parameter of the enclosing template.
      function Is_Generic_Param_Ty (T : Type_Access) return Boolean is
      begin
         if T = null or else T.Kind /= T_Named then
            return False;
         end if;
         for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
            if SU.To_String (Cur_Generics.Element (I).Name)
                 = SU.To_String (T.Name)
            then
               return True;
            end if;
         end loop;
         return False;
      end Is_Generic_Param_Ty;

      --  §5.9/§9.8: arithmetic and comparison on a generic parameter
      --  require a `numeric`, `integer`, or `primitive` bound. An
      --  unconstrained parameter is an opaque layout.
      function Generic_Arith_OK (T : Type_Access) return Boolean is
      begin
         if T = null or else T.Kind /= T_Named then
            return False;
         end if;
         for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
            if SU.To_String (Cur_Generics.Element (I).Name)
                 = SU.To_String (T.Name)
            then
               declare
                  B : constant Path_Segments.Vector :=
                    Cur_Generics.Element (I).Bounds;
               begin
                  for J in B.First_Index .. B.Last_Index loop
                     declare
                        N : constant String := SU.To_String (B.Element (J));
                     begin
                        if N = "numeric" or else N = "integer"
                          or else N = "primitive"
                        then
                           return True;
                        end if;
                     end;
                  end loop;
                  return False;
               end;
            end if;
         end loop;
         return False;
      end Generic_Arith_OK;

      --  §8.11.1 destruct-satisfaction (declared + propagation) is computed
      --  once in Kurt.Layout, which holds the unit's struct/enum decls.
      function Satisfies_Destruct (T : Type_Access) return Boolean
        renames Kurt.Layout.Satisfies_Destruct;

      function Is_Moved (Name : String) return Boolean is
      begin
         for M of Moved loop
            if SU.To_String (M.Name) = Name then
               return True;
            end if;
         end loop;
         return False;
      end Is_Moved;

      procedure Mark_Moved (Name : String) is
      begin
         if not Is_Moved (Name) then
            Moved.Append
              ((Name  => SU.To_Unbounded_String (Name),
                Depth => Natural (Scope.Length)));
         end if;
      end Mark_Moved;

      --  §9.9.3: an aggregate capture (struct / tuple / array / payload enum)
      --  must be bound into the closure body by reference to its env field —
      --  it cannot be loaded as a register value, and a `with destruct`
      --  capture must not be copied into a second owner.
      function Cap_By_Ref (T : Type_Access) return Boolean is
      begin
         if T = null then
            return False;
         end if;
         case T.Kind is
            when T_Tuple | T_Array =>
               return True;
            when T_Named =>
               declare
                  N : constant String := SU.To_String (T.Name);
               begin
                  return Kurt.Layout.Is_Struct (N)
                    or else (Kurt.Layout.Is_Enum (N)
                             and then Kurt.Layout.Enum_Has_Payload (N));
               end;
            when others =>
               return False;
         end case;
      end Cap_By_Ref;

      --  §8.8.2: if E is a bare binding of a `destruct` type used as a
      --  transfer source, invalidate it (use-after-move becomes a failure).
      procedure Maybe_Move (E : Expr_Access) is
      begin
         if E /= null and then E.Kind = E_Path
           and then Natural (E.Segments.Length) = 1
         then
            declare
               Name : constant String :=
                 SU.To_String (E.Segments.Last_Element);
            begin
               if Satisfies_Destruct (Lookup_Scope (Name)) then
                  Mark_Moved (Name);
                  E.P_Is_Move := True;   --  codegen skips its scope-exit drop
               end if;
            end;
         end if;
      end Maybe_Move;

      --  §7.4 the type of the K-th payload binding of a variant pattern: by
      --  the named field when the entry is a `field = binding` rename, else
      --  by position K.
      function Pat_Field_Ty
        (Pat : Kurt.Parser.Pattern; Scrut : Type_Access;
         VN : String; K : Positive) return Type_Access is
      begin
         if K <= Natural (Pat.Bind_Fields.Length)
           and then SU.Length (Pat.Bind_Fields.Element (K)) > 0
         then
            return Kurt.Layout.Variant_Field_Type_By_Name
              (Scrut, VN, SU.To_String (Pat.Bind_Fields.Element (K)));
         end if;
         return Kurt.Layout.Variant_Field_Type (Scrut, VN, K);
      end Pat_Field_Ty;

      --  Body appears with the statement checks below; needed here for the
      --  §6.9 `airside { ... }` block expression (its body is statements).
      procedure Check_Block (Stmts : Stmt_Vectors.Vector);

      --------------------------------------------------------------------
      --  Infer a type for E, attach it to E.Sem_Ty, and return it.
      --  Expected flows downward (mainly to steer integer-literal type).
      --------------------------------------------------------------------
      function Infer (E : Expr_Access; Expected : Type_Access)
         return Type_Access
      is
      begin
         case E.Kind is
            when E_Int_Lit =>
               --  §3.4.1: a type suffix fixes the type; otherwise take
               --  the expected integer type, else default to saddr.
               --  §3.4.1 also permits an integer literal in a float
               --  context (e.g. `let x: fe8m23 = 42;` => 42.0).
               if SU.Length (E.Int_Suffix) > 0 then
                  E.Sem_Ty := Mk_Named (SU.To_String (E.Int_Suffix));
               elsif Is_Integer_Type (Expected)
                 or else Is_Float_Type (Expected)
               then
                  E.Sem_Ty := Expected;
               else
                  E.Sem_Ty := Mk_Named ("saddr");
               end if;
               return E.Sem_Ty;

            when E_Float_Lit =>
               --  §3.4.2: a suffix fixes the type; else an expected float
               --  type; else default fe11m52.
               if SU.Length (E.Float_Suffix) > 0 then
                  E.Sem_Ty := Mk_Named (Canon_Float
                    (SU.To_String (E.Float_Suffix)));
               elsif Is_Float_Type (Expected) then
                  E.Sem_Ty := Expected;
               else
                  E.Sem_Ty := Mk_Named ("fe11m52");
               end if;
               return E.Sem_Ty;

            when E_Bool_Lit =>
               --  §3.4.3 bool literal: type is the built-in alias `bool`.
               E.Sem_Ty := Mk_Named ("bool");
               return E.Sem_Ty;

            when E_String_Lit =>
               --  Slice &[ui1] fat reference. NB §3.5.5 specifies the type
               --  as `&[ui1; N]` (a thin reference to a sized array), but the
               --  bootstrap represents a string literal as a fat slice
               --  (ptr+len, the `Len => 0` sentinel). Carrying the true N in
               --  the type would require switching the whole string-literal
               --  representation to a thin sized-array reference — deferred.
               E.Sem_Ty := Mk_Ref (R_Shared, False, RS_None,
                                   new AST_Type'(Kind => T_Array,
                                                 Elem => Mk_Named ("ui1"),
                                                 Len  => 0));
               return E.Sem_Ty;

            when E_Path =>
               if Natural (E.Segments.Length) = 1 then
                  declare
                     Name : constant String :=
                       SU.To_String (E.Segments.Last_Element);
                     T    : Type_Access := Lookup_Scope (Name);
                  begin
                     --  §8.8.2: a binding shall not be used after it has been
                     --  transferred (moved).
                     if Is_Moved (Name) then
                        Error ("use of '" & Name & "' after it was "
                               & "transferred (moved) (spec 8.8.2)");
                     end if;
                     if T = null then
                        --  §5.3: a const name is replaced by its
                        --  translation-time value at each use site.
                        for I in U.Consts.First_Index ..
                                 U.Consts.Last_Index
                        loop
                           if SU.To_String (U.Consts.Element (I).Name)
                             = Name
                           then
                              E.P_Assoc_Val := U.Consts.Element (I).Init;
                              E.Sem_Ty := U.Consts.Element (I).Ty;
                              return E.Sem_Ty;
                           end if;
                        end loop;
                        --  §5.4: a static binding (global object).
                        for I in U.Statics.First_Index ..
                                 U.Statics.Last_Index
                        loop
                           if SU.To_String (U.Statics.Element (I).Name)
                             = Name
                           then
                              --  §2.6: `static mut` access (read as well as
                              --  store) is an airside-only operation.
                              if U.Statics.Element (I).Is_Mut
                                and then In_Airside = 0
                              then
                                 Error ("access to `static mut` '" & Name
                                        & "' is permitted only in an "
                                        & "`airside` region (spec 2.6)");
                              end if;
                              T := U.Statics.Element (I).Ty;
                              E.Sem_Ty := T;
                              return T;
                           end if;
                        end loop;
                        --  §4.10: a bare subroutine name used as a value is
                        --  a subroutine pointer; its type is built from the
                        --  signature. (As a call callee the name is resolved
                        --  in E_Call, not here.)
                        declare
                           FS : Sig;
                        begin
                           if Find_Sig (Name, FS) then
                              declare
                                 FP : constant Type_Access :=
                                   new AST_Type (Kind => T_Fn);
                              begin
                                 for I in FS.Params.First_Index ..
                                          FS.Params.Last_Index
                                 loop
                                    FP.Fn_Params.Append
                                      (FS.Params.Element (I).Ty);
                                 end loop;
                                 FP.Fn_Ret      := FS.Ret;
                                 FP.Fn_Variadic := FS.Is_Variadic;
                                 FP.Fn_Never    := FS.Is_Never;
                                 E.P_Is_Fn_Ptr  := True;
                                 E.Sem_Ty       := FP;
                                 return FP;
                              end;
                           end if;
                        end;
                        Error ("unknown identifier '" & Name & "'");
                     end if;
                     E.Sem_Ty := T;
                     return T;
                  end;
               elsif Natural (E.Segments.Length) = 2 then
                  --  `Enum::Variant` evaluates to a value of the enum.
                  declare
                     EN : constant String :=
                       SU.To_String (E.Segments.First_Element);
                     VN : constant String :=
                       SU.To_String (E.Segments.Last_Element);
                  begin
                     if Kurt.Layout.Is_Enum (EN)
                       and then Kurt.Layout.Has_Variant (EN, VN)
                     then
                        E.Sem_Ty := Mk_Named (EN);
                        return E.Sem_Ty;
                     --  Generic enum: the concrete instance comes from the
                     --  expected type (post-monomorphisation).
                     elsif Expected /= null and then Expected.Kind = T_Named
                       and then Kurt.Layout.Is_Enum
                                  (SU.To_String (Expected.Name))
                       and then Kurt.Layout.Has_Variant
                                  (SU.To_String (Expected.Name), VN)
                     then
                        E.Sem_Ty := Expected;
                        return E.Sem_Ty;
                     end if;
                     --  §9.3.2 associated-const access `Type::NAME`.
                     --  Concrete type: inline the impl's value expression.
                     declare
                        CV : constant Expr_Access :=
                          Find_Impl_Const (EN, VN);
                     begin
                        if CV /= null then
                           E.P_Assoc_Val := CV;
                           E.Sem_Ty := Infer (CV, Expected);
                           return E.Sem_Ty;
                        end if;
                     end;
                     --  Generic parameter: `T::NAME` in a template. The
                     --  value is resolved per instance; here only the type
                     --  (selftype → T) is needed for checking.
                     declare
                        CT  : Type_Access;
                        OKc : Boolean;
                     begin
                        Find_Bound_Const (EN, VN, CT, OKc);
                        if OKc then
                           E.Sem_Ty := Subst_Self_T
                             (CT, Mk_Named (EN));
                           return E.Sem_Ty;
                        end if;
                     end;
                  end;
                  --  Otherwise a namespaced call callee (handled in E_Call).
                  E.Sem_Ty := null;
                  return null;
               else
                  E.Sem_Ty := null;
                  return null;
               end if;

            when E_Field =>
               declare
                  RT  : constant Type_Access := Infer (E.F_Recv, null);
                  --  §6.2.5 reference transparency: field access through
                  --  a reference reaches the referent's fields.
                  RTD : constant Type_Access :=
                    (if Is_Ref (RT) then RT.Target else RT);
                  FN  : constant String := SU.To_String (E.F_Name);
               begin
                  if FN = "?" then
                     Error ("access to padding field '?' is prohibited (spec 5.5.2)");
                  end if;
                  if FN = "ptr" then
                     --  Fat-pointer view (§4.6.1): `.ptr` is &raw elem.
                     if E.F_Recv.Kind = E_String_Lit then
                        E.Sem_Ty := Mk_Raw_Ref (Mk_Named ("ui1"));
                     elsif RT /= null and then RT.Kind = T_Array then
                        E.Sem_Ty := Mk_Raw_Ref (RT.Elem);
                     elsif RTD /= null and then RTD.Kind = T_Array then
                        --  through a reference, e.g. a `&[T]` slice
                        E.Sem_Ty := Mk_Raw_Ref (RTD.Elem);
                     elsif Is_Ref (RT) then
                        E.Sem_Ty := Mk_Raw_Ref (RT.Target);
                     else
                        E.Sem_Ty := Mk_Raw_Ref (Mk_Named ("ui1"));
                     end if;
                  elsif FN = "len" then
                     E.Sem_Ty := Mk_Named ("uaddr");
                  elsif RTD /= null and then RTD.Kind = T_Named
                    and then Kurt.Layout.Is_Struct (SU.To_String (RTD.Name))
                  then
                     declare
                        FT : constant Type_Access :=
                          Kurt.Layout.Field_Type
                            (SU.To_String (RTD.Name), FN);
                     begin
                        if FT = null then
                           Error ("struct '" & SU.To_String (RTD.Name)
                                  & "' has no field '" & FN & "'");
                        end if;
                        E.Sem_Ty := FT;
                     end;
                  elsif RT /= null and then RT.Kind = T_Tuple then
                     --  §6.2.2 tuple field by index `.0`, `.1`, ...
                     declare
                        Idx : constant Integer := Integer'Value (FN);
                     begin
                        if Idx < 0 or else Idx >= Natural (RT.Elems.Length)
                        then
                           Error ("tuple index" & Idx'Image
                                  & " out of range for '" & Image (RT) & "'");
                           E.Sem_Ty := null;
                        else
                           E.Sem_Ty :=
                             Kurt.Layout.Tuple_Field_Type (RT, Idx);
                        end if;
                     exception
                        when Constraint_Error =>
                           Error ("tuple field must be an integer index, "
                                  & "got '." & FN & "'");
                           E.Sem_Ty := null;
                     end;
                  else
                     Error ("unsupported field '." & FN & "'");
                     E.Sem_Ty := null;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Call =>
               --  §10.4 a subroutine declared in a `@dyn` block may be
               --  invoked only within an `airside` region. The callee is a
               --  single-segment path holding the mangled `alias$item` name.
               if In_Airside = 0
                 and then E.C_Callee.Kind = E_Path
                 and then Natural (E.C_Callee.Segments.Length) = 1
               then
                  declare
                     CN : constant String :=
                       SU.To_String (E.C_Callee.Segments.Last_Element);
                  begin
                     for I in Dyn_Fn_Names.First_Index
                              .. Dyn_Fn_Names.Last_Index loop
                        if SU.To_String (Dyn_Fn_Names.Element (I)) = CN then
                           declare
                              Disp : SU.Unbounded_String;   --  `alias::item`
                           begin
                              for K in CN'Range loop
                                 if CN (K) = '$' then
                                    SU.Append (Disp, "::");
                                 else
                                    SU.Append (Disp, CN (K));
                                 end if;
                              end loop;
                              Error ("`@dyn` subroutine '" & SU.To_String (Disp)
                                     & "' may be invoked only within an "
                                     & "`airside` region (spec 10.4)");
                           end;
                           exit;
                        end if;
                     end loop;
                  end;
               end if;
               --  §6.2.3 method invocation: `e.m(args)` resolves to the
               --  inherent method `T$m` and desugars to a plain call with
               --  the receiver as first argument (§6.2.6 auto-referencing:
               --  a non-reference receiver is wrapped in `&`/`$` to match
               --  the self parameter; a reference receiver passes through).
               if E.C_Callee.Kind = E_Field then
                  --  §6.2.3 qualified method invocation `(e as Trait).m(args)`:
                  --  the receiver is a cast to a *trait* name. Validate that
                  --  e's concrete type implements the trait and that the trait
                  --  declares the method, then strip the cast so resolution
                  --  proceeds against e's concrete type (the trait method is
                  --  mangled identically to the inherent `Type$m`).
                  if E.C_Callee.F_Recv.Kind = E_Cast
                    and then not E.C_Callee.F_Recv.Cast_Bang
                    and then not E.C_Callee.F_Recv.Cast_Disc
                    and then E.C_Callee.F_Recv.Cast_Ty /= null
                    and then E.C_Callee.F_Recv.Cast_Ty.Kind = T_Named
                    and then Is_Trait_Name
                               (SU.To_String (E.C_Callee.F_Recv.Cast_Ty.Name))
                  then
                     declare
                        QTrait : constant String :=
                          SU.To_String (E.C_Callee.F_Recv.Cast_Ty.Name);
                        QInner : constant Expr_Access :=
                          E.C_Callee.F_Recv.Cast_Inner;
                        QMName : constant String :=
                          SU.To_String (E.C_Callee.F_Name);
                        QT  : constant Type_Access := Infer (QInner, null);
                        QTT : constant Type_Access :=
                          (if Is_Ref (QT) then QT.Target else QT);
                        MSig : Fn_Header;
                        MOK  : Boolean;
                     begin
                        if QTT /= null and then QTT.Kind = T_Named then
                           if not Type_Implements
                                    (SU.To_String (QTT.Name), QTrait)
                           then
                              Error ("type '" & SU.To_String (QTT.Name)
                                     & "' does not implement trait '" & QTrait
                                     & "' in qualified method `(e as " & QTrait
                                     & ").` (spec 6.2.3)");
                           else
                              Lookup_Trait_Method (QTrait, QMName, MSig, MOK);
                              if not MOK then
                                 Error ("trait '" & QTrait
                                        & "' has no method '" & QMName
                                        & "' (spec 6.2.3)");
                              end if;
                           end if;
                        end if;
                        --  Strip the trait cast and force the trait so
                        --  resolution selects `Type$Trait$method`.
                        E.C_Callee.F_Recv := QInner;
                        E.C_Callee.F_Trait :=
                          SU.To_Unbounded_String (QTrait);
                     end;
                  end if;
                  declare
                     Recv : constant Expr_Access := E.C_Callee.F_Recv;
                     RT   : constant Type_Access := Infer (Recv, null);
                     RTT  : constant Type_Access :=
                       (if Is_Ref (RT) then RT.Target else RT);
                     S    : Sig;
                  begin
                     --  §9.5 dynamic dispatch: a method call on a
                     --  `&dyn Trait` receiver. Validated against the trait
                     --  signature; the callee is left as E_Field so
                     --  codegen emits an indirect dispatch-table call.
                     if RTT /= null and then RTT.Kind = T_Dyn then
                        declare
                           MSig : Fn_Header;
                           MOK  : Boolean;
                        begin
                           Lookup_Trait_Method
                             (SU.To_String (RTT.Trait_Name),
                              SU.To_String (E.C_Callee.F_Name), MSig, MOK);
                           if not MOK then
                              Error ("trait '"
                                     & SU.To_String (RTT.Trait_Name)
                                     & "' has no method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "' (spec 9.5)");
                              E.Sem_Ty := null;
                              return null;
                           end if;
                           --  §9.5 object-safety: a generic method cannot be
                           --  dispatched through a `&dyn` fat reference.
                           if not MSig.Generic_Params.Is_Empty then
                              Error ("method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "' of trait '"
                                     & SU.To_String (RTT.Trait_Name)
                                     & "' is generic and is not object-safe; "
                                     & "it cannot be called through `&dyn` "
                                     & "(spec 9.5)");
                              E.Sem_Ty := null;
                              return null;
                           end if;
                           for K in E.C_Args.First_Index ..
                                    E.C_Args.Last_Index
                           loop
                              declare
                                 Ig : constant Type_Access :=
                                   Infer (E.C_Args.Element (K), null);
                                 pragma Unreferenced (Ig);
                              begin null; end;
                           end loop;
                           E.Sem_Ty := MSig.Return_Type;
                           return E.Sem_Ty;
                        end;
                     end if;

                     --  §5.9/§9.3 type erasure: a method call on a generic
                     --  parameter is licensed by a trait bound. Validated
                     --  abstractly here against the trait signature; the
                     --  monomorphised instance resolves it to a concrete
                     --  `Type$method` via the path below. The template node
                     --  is left un-desugared (templates are never lowered).
                     if RTT /= null and then RTT.Kind = T_Named
                       and then Is_Generic_Param_Ty (RTT)
                     then
                        declare
                           MSig  : Fn_Header;
                           MOK   : Boolean;
                        begin
                           Find_Bound_Method
                             (SU.To_String (RTT.Name),
                              SU.To_String (E.C_Callee.F_Name), MSig, MOK);
                           if not MOK then
                              Error ("no trait bound on '" & Image (RTT)
                                     & "' provides method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "' (spec 9.3)");
                              E.Sem_Ty := null;
                              return null;
                           end if;
                           for K in E.C_Args.First_Index ..
                                    E.C_Args.Last_Index
                           loop
                              declare
                                 Ig : constant Type_Access :=
                                   Infer (E.C_Args.Element (K), null);
                                 pragma Unreferenced (Ig);
                              begin null; end;
                           end loop;
                           E.Sem_Ty :=
                             Subst_Self_T (MSig.Return_Type, RTT);
                           return E.Sem_Ty;
                        end;
                     end if;
                     if RTT /= null and then RTT.Kind = T_Named then
                        declare
                           Sym   : SU.Unbounded_String;
                           Fnd   : Boolean;
                           Amb   : Boolean;
                        begin
                           --  §9.2.1 inherent first, else unique trait impl;
                           --  `(e as Trait).m()` forces F_Trait.
                           Resolve_Item_Symbol
                             (SU.To_String (RTT.Name),
                              SU.To_String (E.C_Callee.F_Name),
                              SU.To_String (E.C_Callee.F_Trait),
                              Sym, Fnd, Amb);
                           if Amb then
                              Error ("call to method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "' on '" & Image (RTT)
                                     & "' is ambiguous (provided by two or "
                                     & "more traits); disambiguate with "
                                     & "`(e as Trait)." & SU.To_String
                                       (E.C_Callee.F_Name) & "()` (spec 9.2.1)");
                              E.Sem_Ty := null;
                              return null;
                           elsif Fnd
                             and then Find_Sig (SU.To_String (Sym), S)
                           then
                              declare
                                 Self_Ty : constant Type_Access :=
                                   (if not S.Params.Is_Empty
                                    then S.Params.First_Element.Ty
                                    else null);
                                 Recv_Arg : Expr_Access;
                                 NP : constant Expr_Access :=
                                   new Expr_Node (Kind => E_Path);
                              begin
                                 if Is_Ref (RT) then
                                    Recv_Arg := Recv;
                                 else
                                    Recv_Arg :=
                                      new Expr_Node (Kind => E_Ref);
                                    Recv_Arg.Rf_Sigil :=
                                      (if Is_Ref (Self_Ty)
                                       then Self_Ty.Sigil else R_Shared);
                                    Recv_Arg.Rf_Place := Recv;
                                 end if;
                                 E.C_Args.Prepend (Recv_Arg);
                                 NP.Segments.Append (Sym);
                                 E.C_Callee := NP;
                              end;
                           else
                              Error ("type '" & Image (RTT)
                                     & "' has no method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "'"
                                     & (if SU.Length (E.C_Callee.F_Trait) > 0
                                        then " in trait '" & SU.To_String
                                          (E.C_Callee.F_Trait) & "'" else "")
                                     & " (spec 9.2.1)");
                              E.Sem_Ty := null;
                              return null;
                           end if;
                        end;
                     else
                        Error ("method receiver must be a named type, "
                               & "got '" & Image (RT) & "'");
                        E.Sem_Ty := null;
                        return null;
                     end if;
                  end;
               end if;

               --  §5.9: an un-instantiated generic invocation
               --  `f.<T, ...>(args)` can only appear inside a template —
               --  Kurt.Mono rewrites every concrete call site to the
               --  instance name. Check the arguments abstractly; the
               --  result type would need substitution and is left
               --  unknown (downstream checks skip null types).
               if E.C_Callee.Kind = E_Path
                 and then not E.C_Callee.P_Type_Args.Is_Empty
               then
                  for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                     declare
                        Ignore : constant Type_Access :=
                          Infer (E.C_Args.Element (I), null);
                        pragma Unreferenced (Ignore);
                     begin
                        null;
                     end;
                  end loop;
                  E.Sem_Ty := null;
                  return null;
               end if;

               declare
                  Callee : constant Expr_Access := E.C_Callee;
                  Name   : SU.Unbounded_String;
                  S      : Sig;
               begin
                  if Callee.Kind = E_Path
                    and then not Callee.Segments.Is_Empty
                  then
                     Name := Callee.Segments.Last_Element;
                     --  §6.1.1 associated subroutine `Type::fn(...)`: when the
                     --  final segment names no free subroutine but `Type$fn`
                     --  exists (Type = the preceding segment), resolve to the
                     --  associated function. No receiver is prepended (an
                     --  associated function has no `self`); a `self`-taking
                     --  method invoked this way receives its receiver as the
                     --  ordinary first argument.
                     if Natural (Callee.Segments.Length) >= 2 then
                        declare
                           Last_S : constant String := SU.To_String (Name);
                           Dummy  : Sig;
                        begin
                           if not Find_Sig (Last_S, Dummy) then
                              declare
                                 Tn : constant String := SU.To_String
                                   (Callee.Segments.Element
                                      (Callee.Segments.Last_Index - 1));
                                 Sym : SU.Unbounded_String;
                                 Fnd, Amb : Boolean;
                              begin
                                 --  §6.1.1: inherent `Type$fn`, else unique
                                 --  trait `Type$Trait$fn`; `Path_Trait` (from
                                 --  `(Type as Trait)::fn`) forces the trait.
                                 Resolve_Item_Symbol
                                   (Tn, Last_S,
                                    SU.To_String (Callee.Path_Trait),
                                    Sym, Fnd, Amb);
                                 if Amb then
                                    Error ("associated subroutine '" & Last_S
                                           & "' on '" & Tn & "' is ambiguous; "
                                           & "use `(" & Tn
                                           & " as Trait)::" & Last_S
                                           & "` (spec 9.2.1)");
                                 elsif Fnd then
                                    declare
                                       NP : constant Expr_Access :=
                                         new Expr_Node (Kind => E_Path);
                                    begin
                                       NP.Segments.Append (Sym);
                                       E.C_Callee := NP;
                                       Name := Sym;
                                    end;
                                 end if;
                              end;
                           end if;
                        end;
                     end if;
                  end if;

                  if Find_Sig (SU.To_String (Name), S) then
                     --  §6.2.1 argument-count check: a non-variadic call must
                     --  supply exactly one argument per parameter; a variadic
                     --  call must supply at least the fixed parameters.
                     declare
                        NA : constant Natural := Natural (E.C_Args.Length);
                        NP : constant Natural := Natural (S.Params.Length);
                     begin
                        if (S.Is_Variadic and then NA < NP)
                          or else (not S.Is_Variadic and then NA /= NP)
                        then
                           Error ("subroutine '" & SU.To_String (Name)
                                  & "' expects"
                                  & (if S.Is_Variadic then " at least" else "")
                                  & Natural'Image (NP) & " argument(s), got"
                                  & Natural'Image (NA) & " (spec 6.2.1)");
                        end if;
                     end;
                     --  Infer each argument, steering fixed-position
                     --  literals toward the declared parameter type.
                     for I in E.C_Args.First_Index .. E.C_Args.Last_Index
                     loop
                        declare
                           Pidx : constant Natural :=
                             S.Params.First_Index + (I - E.C_Args.First_Index);
                           Exp  : Type_Access := null;
                        begin
                           if Pidx <= S.Params.Last_Index then
                              Exp := S.Params.Element (Pidx).Ty;
                           end if;
                           declare
                              Arg_Ty : constant Type_Access :=
                                Infer (E.C_Args.Element (I), Exp);
                           begin
                              --  §9.5 implicit coercion: `&T → &dyn Trait`
                              --  when T implements Trait. Wrap the argument
                              --  in an E_Dyn_Cast so codegen builds the fat
                              --  reference (value ptr + dispatch table).
                              if Exp /= null and then Is_Dyn_Ref (Exp)
                                and then Is_Ref (Arg_Ty)
                                and then Arg_Ty.Target /= null
                                and then Arg_Ty.Target.Kind = T_Named
                                and then Type_Implements
                                  (SU.To_String (Arg_Ty.Target.Name),
                                   SU.To_String (Exp.Target.Trait_Name))
                              then
                                 declare
                                    DC : constant Expr_Access :=
                                      new Expr_Node (Kind => E_Dyn_Cast);
                                 begin
                                    DC.DC_Inner := E.C_Args.Element (I);
                                    DC.DC_Conc  := Arg_Ty.Target.Name;
                                    DC.DC_Trait := Exp.Target.Trait_Name;
                                    DC.Sem_Ty   := Exp;
                                    E.C_Args.Replace_Element (I, DC);
                                 end;
                              elsif Exp /= null and then Is_Slice_Ref (Exp)
                                and then Is_Ref (Arg_Ty)
                                and then Arg_Ty.Target /= null
                                and then Arg_Ty.Target.Kind = T_Array
                                and then Arg_Ty.Target.Len > 0
                                and then Same_Type (Exp.Target.Elem,
                                                    Arg_Ty.Target.Elem)
                              then
                                 --  §4.6 `&[T; N] → &[T]` coercion.
                                 declare
                                    SC : constant Expr_Access :=
                                      new Expr_Node (Kind => E_Slice_Cast);
                                 begin
                                    SC.SC_Inner := E.C_Args.Element (I);
                                    SC.SC_Len   := Arg_Ty.Target.Len;
                                    SC.Sem_Ty   := Exp;
                                    E.C_Args.Replace_Element (I, SC);
                                 end;
                              elsif Exp /= null
                                and then not Assignable (Exp, Arg_Ty)
                              then
                                 Error ("argument" & Integer'Image
                                          (I - E.C_Args.First_Index + 1)
                                        & " to '" & SU.To_String (Name)
                                        & "': expected '" & Image (Exp)
                                        & "' but got '" & Image (Arg_Ty)
                                        & "'");
                              end if;
                           end;
                        end;
                        --  §8.8.2: passing a `destruct`-typed binding as an
                        --  argument transfers it.
                        Maybe_Move (E.C_Args.Element (I));
                     end loop;
                     --  §7.11: a call to a `-> never` subroutine is a
                     --  diverging expression; its type is `never`.
                     if S.Is_Never then
                        E.Sem_Ty := Mk_Named ("never");
                     else
                        E.Sem_Ty := S.Ret;
                     end if;
                  else
                     --  §4.10: not a named subroutine — try an indirect call
                     --  through a subroutine-pointer-typed callee value.
                     declare
                        CT : constant Type_Access := Infer (Callee, null);
                        --  §9.9 a capturing-closure value (its type is the
                        --  anonymous env struct) is invoked through its lifted
                        --  subroutine, with the env address as hidden `self`.
                        Clo_Lift : SU.Unbounded_String;
                     begin
                        if CT /= null and then CT.Kind = T_Named then
                           for SI in U.Structs.First_Index ..
                                     U.Structs.Last_Index
                           loop
                              if SU.To_String (U.Structs.Element (SI).Name)
                                = SU.To_String (CT.Name)
                              then
                                 Clo_Lift := U.Structs.Element (SI).Clo_Lift;
                              end if;
                           end loop;
                        end if;
                        if SU.Length (Clo_Lift) > 0 then
                           --  Closure call: check args against the lifted
                           --  subroutine's parameters after `self`.
                           E.C_Clo_Lift := Clo_Lift;
                           declare
                              LS : Sig;
                              Has : constant Boolean :=
                                Find_Sig (SU.To_String (Clo_Lift), LS);
                           begin
                              for I in E.C_Args.First_Index ..
                                       E.C_Args.Last_Index
                              loop
                                 declare
                                    --  +1: skip the hidden `self` parameter.
                                    Pidx : constant Natural :=
                                      LS.Params.First_Index + 1
                                        + (I - E.C_Args.First_Index);
                                    Exp  : Type_Access := null;
                                 begin
                                    if Has and then Pidx <= LS.Params.Last_Index
                                    then
                                       Exp := LS.Params.Element (Pidx).Ty;
                                    end if;
                                    declare
                                       Arg_Ty : constant Type_Access :=
                                         Infer (E.C_Args.Element (I), Exp);
                                    begin
                                       if Exp /= null
                                         and then not Assignable (Exp, Arg_Ty)
                                       then
                                          Error ("argument" & Integer'Image
                                                   (I - E.C_Args.First_Index + 1)
                                                 & " to closure: expected '"
                                                 & Image (Exp) & "' but got '"
                                                 & Image (Arg_Ty) & "'");
                                       end if;
                                    end;
                                 end;
                              end loop;
                              E.Sem_Ty := (if Has then LS.Ret else null);
                           end;
                           --  §9.9.3: an `xfer` closure that owns `with
                           --  destruct` captures may be invoked at most once —
                           --  a second invocation would operate on already-
                           --  consumed capture storage. Its env struct is the
                           --  only closure kind that satisfies `destruct` (a
                           --  non-`xfer` closure cannot capture such bindings),
                           --  so treat invoking a bare in-scope closure binding
                           --  as transferring it; a second call to the same
                           --  name then fails the §8.8.2 use-after-transfer
                           --  check when its callee path is re-inferred.
                           if Callee.Kind = E_Path
                             and then Natural (Callee.Segments.Length) = 1
                             and then Satisfies_Destruct (CT)
                           then
                              Mark_Moved
                                (SU.To_String (Callee.Segments.Last_Element));
                           end if;
                        elsif CT /= null and then CT.Kind = T_Fn then
                           E.C_Indirect := True;
                           for I in E.C_Args.First_Index ..
                                    E.C_Args.Last_Index
                           loop
                              declare
                                 Pidx : constant Natural :=
                                   CT.Fn_Params.First_Index
                                     + (I - E.C_Args.First_Index);
                                 Exp  : Type_Access := null;
                              begin
                                 if Pidx <= CT.Fn_Params.Last_Index then
                                    Exp := CT.Fn_Params.Element (Pidx);
                                 end if;
                                 declare
                                    Arg_Ty : constant Type_Access :=
                                      Infer (E.C_Args.Element (I), Exp);
                                 begin
                                    if Exp /= null
                                      and then not Assignable (Exp, Arg_Ty)
                                    then
                                       Error ("argument" & Integer'Image
                                                (I - E.C_Args.First_Index + 1)
                                              & " to subroutine pointer: "
                                              & "expected '" & Image (Exp)
                                              & "' but got '" & Image (Arg_Ty)
                                              & "'");
                                    end if;
                                 end;
                              end;
                           end loop;
                           if CT.Fn_Never then
                              E.Sem_Ty := Mk_Named ("never");
                           else
                              E.Sem_Ty := CT.Fn_Ret;
                           end if;
                        else
                           Error ("call to unknown subroutine '"
                                  & SU.To_String (Name) & "'");
                           for I in E.C_Args.First_Index ..
                                    E.C_Args.Last_Index
                           loop
                              declare
                                 Ignore : constant Type_Access :=
                                   Infer (E.C_Args.Element (I), null);
                                 pragma Unreferenced (Ignore);
                              begin
                                 null;
                              end;
                           end loop;
                           E.Sem_Ty := null;
                        end if;
                     end;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Binary =>
               case E.B_Op is
                  when B_Add | B_Sub | B_Mul | B_Div | B_Mod
                     | B_Sat_Add | B_Sat_Sub | B_Sat_Mul | B_Sat_Div
                     | B_And | B_Or | B_Xor | B_Shl | B_Shr =>
                     declare
                        LT : constant Type_Access :=
                          Infer (E.B_Lhs, Expected);
                        RT : Type_Access;
                     begin
                        --  §6.5 `^` is the bitwise XOR (integer operands);
                        --  contract XOR is the distinct `^^` (B_LXor) below.
                        --  §5.9.2 type erasure: arithmetic on a generic
                        --  parameter needs an arithmetic bound, checked
                        --  here on the template — instantiations that
                        --  would individually succeed do not make the
                        --  template legal.
                        if Is_Generic_Param_Ty (LT)
                          and then not Generic_Arith_OK (LT)
                        then
                           Error ("unconstrained parameter '" & Image (LT)
                                  & "' is an opaque layout -- arithmetic "
                                  & "requires a numeric/integer/primitive "
                                  & "bound (spec 5.9)");
                        end if;
                        --  §6.4.2 saturating and §6.5 bitwise/shift operators
                        --  require integer operands; a float lead is a TF (and
                        --  would otherwise reach an unsupported codegen path).
                        if LT /= null and then Is_Float_Type (LT)
                          and then (E.B_Op in B_Sat_Add | B_Sat_Sub
                                      | B_Sat_Mul | B_Sat_Div
                                      | B_And | B_Or | B_Xor | B_Shl | B_Shr)
                        then
                           Error ((if E.B_Op in B_Sat_Add | B_Sat_Sub
                                     | B_Sat_Mul | B_Sat_Div
                                   then "saturating" else "bitwise/shift")
                                  & " operator requires an integer operand, "
                                  & "got float '" & Image (LT)
                                  & "' (spec 6.4.2 / 6.5)");
                        end if;
                        --  §6.5 the bitwise `&`/`|`/`^` require operands
                        --  satisfying `integer`. A concrete non-integer lead
                        --  (e.g. a `contract` type) is a TF — contract XOR is
                        --  the distinct `^^`. Generic parameters are checked
                        --  against their bound above (§5.9.2).
                        if LT /= null
                          and then E.B_Op in B_And | B_Or | B_Xor
                          and then not Is_Generic_Param_Ty (LT)
                          and then not Is_Integer_Type (LT)
                        then
                           Error ("bitwise operator requires operands "
                                  & "satisfying `integer`, got '" & Image (LT)
                                  & "'"
                                  & (if E.B_Op = B_Xor and then
                                        Is_Contract_Ty (LT)
                                     then "; contract XOR is `^^`" else "")
                                  & " (spec 6.5)");
                        end if;
                        --  Steer a literal rhs toward the lhs type, but
                        --  not when lhs is a reference (§8.6.4 raw
                        --  reference arithmetic: lead &raw T, follow uaddr).
                        if Is_Ref (LT) then
                           RT := Infer (E.B_Rhs, Mk_Named ("uaddr"));
                           if LT.Sigil /= R_Raw then
                              Error ("reference arithmetic requires a "
                                     & "`&raw` family lead operand, got '"
                                     & Image (LT) & "' (spec 8.6.4)");
                           elsif E.B_Op /= B_Add and then E.B_Op /= B_Sub
                           then
                              Error ("only '+' and '-' accept a reference "
                                     & "lead operand (spec 8.6.4)");
                           elsif RT /= null
                             and then not Is_Integer_Type (RT)
                           then
                              Error ("reference arithmetic follow operand "
                                     & "must be 'uaddr', got '" & Image (RT)
                                     & "' (spec 8.6.4)");
                           end if;
                           E.Sem_Ty := LT;       --  modifiers preserved
                        else
                           if E.B_Op in B_Shl | B_Shr then
                              --  §6.5: the shift count satisfies `primitive`
                              --  (unsigned) and has the same size as the
                              --  lead — so an unsuffixed literal count takes
                              --  the unsigned type of the lead's size.
                              RT := Infer
                                (E.B_Rhs,
                                 (if LT = null then null
                                  else Unsigned_Of_Size
                                    (Kurt.Layout.Size_Of (LT))));
                              if LT /= null and then RT /= null then
                                 if not Is_Unsigned_Int_Type (RT) then
                                    Error ("shift count must satisfy "
                                           & "`primitive` (unsigned); got '"
                                           & Image (RT) & "' (spec 6.5)");
                                 elsif Kurt.Layout.Size_Of (LT)
                                       /= Kurt.Layout.Size_Of (RT)
                                 then
                                    Error ("shift operands must have the "
                                           & "same size; got '" & Image (LT)
                                           & "' and '" & Image (RT)
                                           & "' (spec 6.5)");
                                 end if;
                              end if;
                           else
                              RT := Infer (E.B_Rhs, LT);
                              if LT /= null and then RT /= null
                                and then not Same_Type (LT, RT)
                              then
                                 --  §6.4/§6.5: both operands of a binary
                                 --  arithmetic / bitwise operator shall be
                                 --  the same type T.
                                 Error ("operands of a binary arithmetic "
                                        & "operator must be the same type; "
                                        & "got '" & Image (LT) & "' and '"
                                        & Image (RT) & "' (spec 6.4)");
                              end if;
                           end if;
                           E.Sem_Ty := LT;
                        end if;
                        return E.Sem_Ty;
                     end;

                  when B_Wide_Add | B_Wide_Mul =>
                     --  §6.4.3: result is the anonymous tuple .{T, T}.
                     declare
                        LT : constant Type_Access := Infer (E.B_Lhs, null);
                        RT : constant Type_Access := Infer (E.B_Rhs, LT);
                        Tup : constant Type_Access :=
                          new AST_Type (Kind => T_Tuple);
                        pragma Unreferenced (RT);
                     begin
                        if LT /= null and then not Is_Integer_Type (LT) then
                           Error ("widening operator requires an integer "
                                  & "operand, got '" & Image (LT) & "'");
                        end if;
                        Tup.Elems.Append (LT);
                        Tup.Elems.Append (LT);
                        E.Sem_Ty := Tup;
                        return E.Sem_Ty;
                     end;

                  when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge =>
                     declare
                        LT : constant Type_Access := Infer (E.B_Lhs, null);
                        RT : constant Type_Access := Infer (E.B_Rhs, LT);
                     begin
                        --  §6.6: both operands of a comparison shall be the
                        --  same type; different numeric types shall not be
                        --  compared without an explicit `as` cast.
                        if LT /= null and then RT /= null
                          and then not Same_Type (LT, RT)
                        then
                           Error ("operands of a comparison must be the "
                                  & "same type; got '" & Image (LT)
                                  & "' and '" & Image (RT) & "' (spec 6.6)");
                        end if;
                        --  §5.9.2 type erasure: comparison on a generic
                        --  parameter also needs an arithmetic bound.
                        if Is_Generic_Param_Ty (LT)
                          and then not Generic_Arith_OK (LT)
                        then
                           Error ("unconstrained parameter '" & Image (LT)
                                  & "' is an opaque layout -- comparison "
                                  & "requires a numeric/integer/primitive "
                                  & "bound (spec 5.9)");
                        end if;
                        --  §6.6: enums do not satisfy `numeric` and cannot
                        --  be compared with == != < > <= >= (bool is a
                        --  contract enum but only `==`/`!=` are usable
                        --  through contract polarity; the bootstrap accepts
                        --  bool through Is_Integer-like channels for now).
                        if LT /= null and then LT.Kind = T_Named
                          and then Kurt.Layout.Is_Enum (SU.To_String (LT.Name))
                          and then SU.To_String (LT.Name) /= "bool"
                        then
                           Error ("enum type '" & Image (LT)
                                  & "' is not numeric -- comparison "
                                  & "operators require numeric operands "
                                  & "(spec 6.6)");
                        end if;
                        E.Sem_Ty := Mk_Named ("bool");
                        return E.Sem_Ty;
                     end;

                  when B_LAnd | B_LOr | B_LXor =>
                     --  §7.2.2 logical operators: each operand satisfies
                     --  `contract`; the result is bool. `&&`/`||` short-
                     --  circuit; `^^` evaluates both. `^^` additionally
                     --  requires `void` success/failure payloads.
                     declare
                        LT  : constant Type_Access := Infer (E.B_Lhs, null);
                        RT  : constant Type_Access := Infer (E.B_Rhs, null);
                        Nm  : constant String :=
                          (case E.B_Op is
                              when B_LAnd => "&&",
                              when B_LOr  => "||",
                              when others => "^^");
                     begin
                        if not Is_Contract_Ty (LT) then
                           Error ("'" & Nm & "' requires operands satisfying "
                                  & "`contract`; lhs is '" & Image (LT)
                                  & "' (spec 7.2.2)");
                        end if;
                        if not Is_Contract_Ty (RT) then
                           Error ("'" & Nm & "' requires operands satisfying "
                                  & "`contract`; rhs is '" & Image (RT)
                                  & "' (spec 7.2.2)");
                        end if;
                        if E.B_Op = B_LXor
                          and then not (Contract_Payloads_Void (LT)
                                        and then Contract_Payloads_Void (RT))
                        then
                           Error ("'^^' requires both operands to have `void` "
                                  & "success and failure payloads (spec 7.2.2)");
                        end if;
                        E.Sem_Ty := Mk_Named ("bool");
                        return E.Sem_Ty;
                     end;
               end case;

            when E_If =>
               declare
                  CT : constant Type_Access :=
                    Infer (E.I_Cond, Mk_Named ("bool"));
                  TT : constant Type_Access := Infer (E.I_Then, Expected);
                  --  §7.11: a diverging `then` contributes no type; steer the
                  --  `else` by the surviving expected type, not by `never`.
                  ET : constant Type_Access :=
                    Infer (E.I_Else,
                           (if Is_Never_Ty (TT) then Expected else TT));
                  pragma Unreferenced (CT);
               begin
                  --  §7.11 unification: drop the diverging branch; the
                  --  result type comes from the non-diverging one (or is
                  --  itself `never` when both diverge).
                  if Is_Never_Ty (TT) then
                     E.Sem_Ty := ET;
                  elsif Is_Never_Ty (ET) then
                     E.Sem_Ty := TT;
                  else
                     if not Same_Type (TT, ET) then
                        Error ("if branches have differing types: '"
                               & Image (TT) & "' vs '" & Image (ET)
                               & "' (§7.1)");
                     end if;
                     E.Sem_Ty := TT;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Deref =>
               declare
                  IT : constant Type_Access := Infer (E.D_Inner, null);
               begin
                  if Is_Ref (IT) then
                     --  §2.6: dereferencing a `&raw` reference is an
                     --  airside-only operation. `&`/`$` derefs are landside.
                     if IT.Sigil = R_Raw and then In_Airside = 0 then
                        Error ("dereference of a `&raw` reference is "
                               & "permitted only in an `airside` region "
                               & "(spec 2.6)");
                     end if;
                     --  §2.6: `&mut T` access (load and store) is an
                     --  airside-only operation. This E_Deref case is
                     --  reached both for an rvalue load (`*m`) and for a
                     --  store target (the S_Assign LHS is inferred here),
                     --  so a single gate covers both directions. `$`
                     --  (R_Excl) and plain `&`/atomic/guard are not in the
                     --  §2.6 list and are not gated here.
                     if IT.Sigil = R_Shared and then IT.R_Store = RS_Mut
                       and then In_Airside = 0
                     then
                        Error ("load/store through a `&mut T` reference is "
                               & "permitted only in an `airside` region "
                               & "(spec 2.6)");
                     end if;
                     E.Sem_Ty := IT.Target;
                  else
                     Error ("dereference of non-reference type '"
                            & Image (IT) & "'");
                     E.Sem_Ty := null;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Struct_Lit =>
               declare
                  --  The literal's `Name {` may be a generic template
                  --  name (`Box`); the actual concrete struct comes from
                  --  the expected type (`Box$si4`) after monomorphisation.
                  SN : constant String :=
                    (if Expected /= null and then Expected.Kind = T_Named
                        and then Kurt.Layout.Is_Struct
                                   (SU.To_String (Expected.Name))
                     then SU.To_String (Expected.Name)
                     else SU.To_String (E.SL_Name));
               begin
                  if not Kurt.Layout.Is_Struct (SN) then
                     Error ("unknown struct type '" & SN & "'");
                  else
                     for I in E.SL_Fields.First_Index ..
                              E.SL_Fields.Last_Index
                     loop
                        declare
                           FI : constant Field_Init :=
                             E.SL_Fields.Element (I);
                           FT : constant Type_Access :=
                             Kurt.Layout.Field_Type
                               (SN, SU.To_String (FI.Name));
                           VT : Type_Access;
                        begin
                           --  §6.1.4 a field shall not be initialised twice.
                           for J in E.SL_Fields.First_Index .. I - 1 loop
                              if SU.To_String (E.SL_Fields.Element (J).Name)
                                   = SU.To_String (FI.Name)
                              then
                                 Error ("field '" & SU.To_String (FI.Name)
                                        & "' of '" & SN & "' is initialised "
                                        & "more than once (spec 6.1.4)");
                              end if;
                           end loop;
                           if FT = null then
                              Error ("struct '" & SN & "' has no field '"
                                     & SU.To_String (FI.Name) & "'");
                           end if;
                           VT := Infer (FI.Val, FT);
                           if FT /= null and then not Assignable (FT, VT) then
                              Error ("field '" & SU.To_String (FI.Name)
                                     & "' of '" & SN & "': expected '"
                                     & Image (FT) & "' but got '"
                                     & Image (VT) & "'");
                           end if;
                           --  §8.8.2 aggregate field init from a binding is a
                           --  transfer when the field type satisfies destruct.
                           Maybe_Move (FI.Val);
                        end;
                     end loop;

                     --  §5.5.3: every declared field shall be either supplied
                     --  by the literal or carry a default-value expression.
                     for K in 1 .. Kurt.Layout.Struct_Field_Count (SN) loop
                        declare
                           FN : constant String :=
                             Kurt.Layout.Struct_Field_Name (SN, K);
                           Supplied : Boolean := False;
                        begin
                           for I in E.SL_Fields.First_Index ..
                                    E.SL_Fields.Last_Index
                           loop
                              if SU.To_String (E.SL_Fields.Element (I).Name)
                                   = FN
                              then
                                 Supplied := True;
                              end if;
                           end loop;
                           --  §5.5.2 `?` padding fields are auto-zeroed and
                           --  never supplied; exempt them from the rule.
                           if FN /= "?"
                             and then not Supplied
                             and then Kurt.Layout.Field_Default (SN, FN) = null
                           then
                              Error ("struct literal of '" & SN
                                     & "' omits field '" & FN
                                     & "' which has no default (spec 5.5.3)");
                           end if;
                        end;
                     end loop;
                  end if;
                  E.Sem_Ty := Mk_Named (SN);
                  return E.Sem_Ty;
               end;

            when E_Variant_New =>
               declare
                  --  Concrete enum type from the expected type when the
                  --  written name is a generic template / intrinsic verdict;
                  --  keep its arguments (verdict payload types come from them).
                  Conc : constant Type_Access :=
                    (if Expected /= null and then Expected.Kind = T_Named
                        and then Kurt.Layout.Is_Enum
                                   (SU.To_String (Expected.Name))
                     then Expected
                     else Mk_Named (SU.To_String (E.VN_Enum)));
                  EN : constant String := SU.To_String (Conc.Name);
                  VN : constant String := SU.To_String (E.VN_Variant);
               begin
                  if VN = "#wild#" then
                     --  §6.1.5 wild construction. Permitted only on an enum
                     --  that does not declare its own `#wild#` variant.
                     if not Kurt.Layout.Is_Enum (EN) then
                        Error ("unknown enum type '" & EN & "'");
                     elsif Kurt.Layout.Has_Wild_Variant (EN) then
                        Error ("`" & EN & "::#wild#` construction is not "
                               & "permitted: '" & EN & "' declares a #wild# "
                               & "variant (spec 6.1.5)");
                     end if;
                     E.Sem_Ty := Conc;
                  elsif not Kurt.Layout.Is_Enum (EN) then
                     Error ("unknown enum type '" & EN & "'");
                  elsif not Kurt.Layout.Has_Variant (EN, VN) then
                     Error ("enum '" & EN & "' has no variant '" & VN & "'");
                  else
                     for I in E.VN_Fields.First_Index ..
                              E.VN_Fields.Last_Index
                     loop
                        declare
                           FI : constant Field_Init :=
                             E.VN_Fields.Element (I);
                           FT : constant Type_Access :=
                             Kurt.Layout.Variant_Field_Type_By_Name
                               (Conc, VN, SU.To_String (FI.Name));
                           VT : Type_Access;
                        begin
                           if FT = null then
                              Error ("variant '" & EN & "::" & VN
                                     & "' has no payload field '"
                                     & SU.To_String (FI.Name) & "'");
                           end if;
                           VT := Infer (FI.Val, FT);
                           if FT /= null and then not Assignable (FT, VT) then
                              Error ("payload field '"
                                     & SU.To_String (FI.Name) & "': expected '"
                                     & Image (FT) & "' but got '"
                                     & Image (VT) & "'");
                           end if;
                           --  §8.8.2 payload init from a binding is a transfer
                           --  when the payload type satisfies destruct.
                           Maybe_Move (FI.Val);
                        end;
                     end loop;
                  end if;
                  E.Sem_Ty := Conc;
                  return E.Sem_Ty;
               end;

            when E_Match =>
               declare
                  Scrut_Ty : constant Type_Access := Infer (E.M_Scrut, null);
                  Result   : Type_Access := Expected;
                  Has_Wild : Boolean := False;
                  Any_Live : Boolean := False;  --  §7.11 saw a non-diverging arm
                  Is_Enum_Scrut : constant Boolean :=
                    Scrut_Ty /= null and then Scrut_Ty.Kind = T_Named
                    and then Kurt.Layout.Is_Enum
                               (SU.To_String (Scrut_Ty.Name));
               begin
                  for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                     declare
                        Arm   : constant Match_Arm := E.M_Arms.Element (I);
                        BT    : Type_Access;
                        Saved : constant Natural := Natural (Scope.Length);
                     begin
                        case Arm.Pat.Kind is
                           when Pat_Wild =>
                              --  §7.4: a guarded arm may fail at runtime, so a
                              --  guarded `#wild#` does not make the match
                              --  exhaustive — only an unguarded one does.
                              if Arm.Guard = null then
                                 Has_Wild := True;
                              end if;
                           when Pat_Int =>
                              if not Is_Integer_Type (Scrut_Ty) then
                                 Error ("integer pattern matched against "
                                        & "non-integer scrutinee '"
                                        & Image (Scrut_Ty) & "'");
                              end if;
                           when Pat_Range =>
                              --  §5.10 range pattern: numeric scrutinee, and
                              --  a non-empty bound order.
                              if not Is_Integer_Type (Scrut_Ty) then
                                 Error ("range pattern matched against "
                                        & "non-integer scrutinee '"
                                        & Image (Scrut_Ty) & "'");
                              elsif Arm.Pat.Int_V > Arm.Pat.Range_Hi
                                or else (not Arm.Pat.Range_Incl
                                         and then Arm.Pat.Int_V
                                                    = Arm.Pat.Range_Hi)
                              then
                                 Error ("range pattern lower bound exceeds "
                                        & "upper bound (empty range)");
                              end if;
                           when Pat_Variant =>
                              if Is_Enum_Scrut
                                and then Natural (Arm.Pat.Path.Length) = 2
                              then
                                 declare
                                    EN : constant String :=
                                      SU.To_String (Scrut_Ty.Name);
                                    VN : constant String := SU.To_String
                                      (Arm.Pat.Path.Last_Element);
                                 begin
                                    if not Kurt.Layout.Has_Variant (EN, VN)
                                    then
                                       Error ("enum '" & EN
                                         & "' has no variant '" & VN & "'");
                                    else
                                       --  Bind payload fields positionally
                                       --  for the arm body's scope.
                                       for K in 1 .. Natural
                                         (Arm.Pat.Bindings.Length)
                                       loop
                                          Scope.Append
                                            ((Name => Arm.Pat.Bindings.Element
                                                        (K),
                                              Ty   => Pat_Field_Ty
                                                (Arm.Pat, Scrut_Ty, VN, K),
                                              others => <>));
                                       end loop;
                                    end if;
                                 end;
                              else
                                 Error ("variant pattern requires an enum "
                                        & "scrutinee");
                              end if;
                           when Pat_Slice =>
                              --  §7.4.2 slice pattern: the scrutinee shall be
                              --  an array; each bind names an element.
                              if Scrut_Ty = null
                                or else Scrut_Ty.Kind /= T_Array
                              then
                                 Error ("slice pattern requires an array "
                                        & "scrutinee, got '"
                                        & Image (Scrut_Ty) & "'");
                              else
                                 declare
                                    Rests : Natural := 0;
                                 begin
                                    for K in Arm.Pat.Slice_Elems.First_Index ..
                                             Arm.Pat.Slice_Elems.Last_Index
                                    loop
                                       declare
                                          SE : constant Slice_Elem :=
                                            Arm.Pat.Slice_Elems.Element (K);
                                       begin
                                          if SE.Kind = SE_Rest then
                                             Rests := Rests + 1;
                                          elsif SE.Kind = SE_Bind then
                                             Scope.Append
                                               ((Name => SE.Name,
                                                 Ty   => Scrut_Ty.Elem,
                                                 others => <>));
                                          end if;
                                       end;
                                    end loop;
                                    if Rests > 1 then
                                       Error ("a slice pattern may contain at "
                                          & "most one `...` (spec 7.4.2)");
                                    end if;
                                 end;
                              end if;
                        end case;

                        --  §5.10 binding pattern `name # sub`: bind the
                        --  scrutinee value to `name` for the arm (and guard).
                        if SU.Length (Arm.Pat.Bind_Name) > 0 then
                           Scope.Append
                             ((Name => Arm.Pat.Bind_Name,
                               Ty   => Scrut_Ty, others => <>));
                        end if;

                        --  §7.4: a guard clause is type-checked in the arm's
                        --  pattern-binding scope and shall satisfy `contract`.
                        if Arm.Guard /= null then
                           declare
                              GT : constant Type_Access :=
                                Infer (Arm.Guard, Mk_Named ("bool"));
                           begin
                              if not Is_Contract_Ty (GT) then
                                 Error ("match guard must satisfy `contract`, "
                                        & "got '" & Image (GT) & "'");
                              end if;
                           end;
                        end if;

                        BT := Infer (Arm.Arm_Body, Result);

                        --  Pop payload bindings introduced by this arm.
                        while Natural (Scope.Length) > Saved loop
                           Scope.Delete_Last;
                        end loop;

                        --  §7.11: a diverging arm contributes no type to the
                        --  unification; the result comes from the live arms.
                        if not Is_Never_Ty (BT) then
                           Any_Live := True;
                           if Result = null or else Is_Never_Ty (Result) then
                              Result := BT;
                           elsif not Same_Type (Result, BT) then
                              Error ("match arms have differing types: '"
                                     & Image (Result) & "' vs '"
                                     & Image (BT) & "'");
                           end if;
                        end if;
                     end;
                  end loop;

                  --  Exhaustiveness (§7): a #wild# arm covers everything;
                  --  otherwise an enum must list every variant.
                  if not Has_Wild then
                     if Is_Enum_Scrut then
                        declare
                           EN : constant String :=
                             SU.To_String (Scrut_Ty.Name);
                        begin
                           --  §4.5 / §7: an enum without a declared
                           --  `#wild#` variant has discriminant patterns
                           --  beyond its named variants, so a `#wild#`
                           --  arm is mandatory even when every variant is
                           --  listed. Only an enum that declares its own
                           --  `#wild#` variant is exhaustible by listing.
                           if not Kurt.Layout.Has_Wild_Variant (EN) then
                              Error ("non-exhaustive match: enum '" & EN
                                     & "' declares no #wild# variant, so a "
                                     & "#wild# arm is required");
                           else
                              for K in 1 .. Kurt.Layout.Variant_Count (EN)
                              loop
                                 declare
                                    VN : constant String :=
                                      Kurt.Layout.Variant_Name (EN, K);
                                    Found : Boolean := False;
                                 begin
                                    for I in E.M_Arms.First_Index ..
                                             E.M_Arms.Last_Index
                                    loop
                                       if E.M_Arms.Element (I).Pat.Kind
                                            = Pat_Variant
                                         and then E.M_Arms.Element (I).Guard
                                                    = null
                                         and then SU.To_String
                                           (E.M_Arms.Element (I).Pat.Path
                                              .Last_Element) = VN
                                       then
                                          Found := True;
                                       end if;
                                    end loop;
                                    if not Found then
                                       Error ("non-exhaustive match: enum '"
                                              & EN & "' variant '" & VN
                                              & "' is not covered");
                                    end if;
                                 end;
                              end loop;
                           end if;
                        end;
                     else
                        Error ("non-exhaustive match (a #wild# arm is "
                               & "required for this scrutinee)");
                     end if;
                  end if;

                  --  §7.11: when every arm diverges, the match itself is a
                  --  diverging expression of type `never`.
                  if not Any_Live then
                     E.Sem_Ty := Mk_Named ("never");
                  else
                     E.Sem_Ty := Result;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Cast =>
               --  §6.8 cast. Bootstrap scope: integer↔integer (§6.8.2),
               --  enum→discriminant (§6.8.7), integer↔float (§6.8.3-4),
               --  float↔float (§6.8.5), and same-size `as!` reinterpret
               --  (§6.8.11). `as ?` extracts an enum discriminant.
               declare
                  Src : constant Type_Access := Infer (E.Cast_Inner, null);
                  Src_Is_Enum : constant Boolean :=
                    Src /= null and then Src.Kind = T_Named
                    and then Kurt.Layout.Is_Enum (SU.To_String (Src.Name));
               begin
                  if E.Cast_Disc then
                     --  `e as ?` — only permitted on enums.
                     if Src_Is_Enum then
                        declare
                           EN : constant String := SU.To_String (Src.Name);
                           DS : constant Natural :=
                             Kurt.Layout.Enum_Disc_Size (EN);
                        begin
                           if DS = 0 then
                              --  §4.11.3: at most one variant and no
                              --  #wild#(V) — the discriminant type is
                              --  void and carries no value.
                              Error ("`as ?` on enum '" & EN
                                     & "' whose discriminant type is "
                                     & "void (spec 4.11.3)");
                              E.Sem_Ty := Mk_Named ("saddr");
                           else
                              E.Sem_Ty := Mk_Named
                                (Disc_Ty_Name
                                   (DS, Kurt.Layout.Enum_Disc_Signed (EN)));
                           end if;
                        end;
                     else
                        Error ("`as ?` requires an enum operand, got '"
                               & Image (Src) & "'");
                        E.Sem_Ty := Mk_Named ("saddr");
                     end if;
                  elsif E.Cast_Bang then
                     --  §2.6: `as!` is an airside-only operation.
                     if In_Airside = 0 then
                        Error ("`as!` (bitwise reinterpret) is permitted only "
                               & "in an `airside` region (spec 2.6)");
                     end if;
                     --  §6.8.11: bitwise reinterpret between equal-size types.
                     if Src /= null
                       and then Kurt.Layout.Size_Of (Src)
                                  /= Kurt.Layout.Size_Of (E.Cast_Ty)
                     then
                        Error ("`as!` requires equal-size types: '"
                               & Image (Src) & "' and '"
                               & Image (E.Cast_Ty) & "' differ in size");
                     end if;
                     E.Sem_Ty := E.Cast_Ty;
                  elsif (Src /= null and then Src.Kind = T_Fn)
                    or else (E.Cast_Ty /= null and then E.Cast_Ty.Kind = T_Fn)
                  then
                     --  §4.10: `as` shall not apply to or from a subroutine
                     --  pointer; conversions go through `as!` in an airside
                     --  block.
                     Error ("`as` shall not convert to or from a subroutine "
                            & "pointer ('" & Image (Src) & "' as '"
                            & Image (E.Cast_Ty)
                            & "'); use `as!` in an airside block (spec 4.10)");
                     E.Sem_Ty := E.Cast_Ty;
                  elsif (Is_Ref (E.Cast_Ty) or else Is_Uaddr (E.Cast_Ty))
                    and then (Is_Ref (Src) or else Is_Uaddr (Src))
                    and then not (Is_Uaddr (E.Cast_Ty) and then Is_Uaddr (Src))
                  then
                     --  §8.1.3 reference cast (sigil/modifier conversion).
                     declare
                        Outcome : constant Natural :=
                          Ref_Cast_Outcome (Src, E.Cast_Ty);
                     begin
                        if Outcome = 2 then
                           Error ("reference cast '" & Image (Src)
                                  & "' as '" & Image (E.Cast_Ty)
                                  & "' is not permitted (spec 8.1.3)");
                        elsif Outcome = 1 and then In_Airside = 0 then
                           --  §8.1.3: an ascending cast `&raw T` -> a managed
                           --  reference (`&T`/`&mut T`/`$T`) begins lifetime
                           --  tracking on an asserted referent and is
                           --  permitted only in an `airside` region.
                           Error ("ascending cast from '" & Image (Src)
                                  & "' to a managed reference is permitted "
                                  & "only in an `airside` region (spec 8.1.3)");
                        end if;
                        E.Sem_Ty := E.Cast_Ty;
                     end;
                  elsif Is_Integer_Type (E.Cast_Ty) then
                     if not (Is_Integer_Type (Src) or else Src_Is_Enum
                             or else Is_Float_Type (Src))
                     then
                        Error ("cannot cast '" & Image (Src)
                               & "' to integer type '"
                               & Image (E.Cast_Ty) & "'");
                     elsif Src_Is_Enum
                       and then Kurt.Layout.Enum_Disc_Size
                                  (SU.To_String (Src.Name)) = 0
                     then
                        Error ("cannot cast enum '"
                               & SU.To_String (Src.Name)
                               & "' whose discriminant type is void "
                               & "(spec 4.11.3)");
                     end if;
                     E.Sem_Ty := E.Cast_Ty;
                  elsif Is_Float_Type (E.Cast_Ty) then
                     if not (Is_Integer_Type (Src) or else Is_Float_Type (Src))
                     then
                        Error ("cannot cast '" & Image (Src)
                               & "' to float type '"
                               & Image (E.Cast_Ty) & "'");
                     end if;
                     E.Sem_Ty := E.Cast_Ty;
                  else
                     Error ("unsupported cast target '"
                            & Image (E.Cast_Ty) & "'");
                     E.Sem_Ty := E.Cast_Ty;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Unary =>
               --  §6.3.1 negation (numeric: int or float) / §6.5.3 bitwise
               --  NOT (integer) / §7.2.1 contract polarity inversion.
               declare
                  OT : constant Type_Access := Infer (E.U_Operand, Expected);
               begin
                  if OT /= null then
                     if E.U_Op = U_Neg
                       and then not (Is_Integer_Type (OT)
                                     or else Is_Float_Type (OT)
                                     or else Generic_Arith_OK (OT))
                     then
                        Error ("unary '-' requires a numeric operand, got '"
                               & Image (OT) & "'");
                     elsif E.U_Op = U_Not
                       and then not Is_Integer_Type (OT)
                     then
                        --  §7.2.1: `!` on a contract value exchanges the
                        --  success and failure variants. The bootstrap
                        --  supports the self-inverse cases: bool, and any
                        --  contract enum whose two payloads are identical
                        --  (a declared `-> inv_type` pair is otherwise
                        --  required and not yet implemented).
                        if not Is_Contract_Ty (OT) then
                           Error ("unary '!' requires an integer or a "
                                  & "`contract` operand, got '"
                                  & Image (OT) & "'");
                        elsif SU.To_String (OT.Name) /= "bool" then
                           declare
                              EN : constant String :=
                                SU.To_String (OT.Name);
                              SV : constant String :=
                                Kurt.Layout.Contract_Success_Variant (EN);
                              FV : constant String :=
                                Kurt.Layout.Contract_Fail_Variant (EN);
                              SC : constant Natural :=
                                Kurt.Layout.Variant_Field_Count (EN, SV);
                              FC : constant Natural :=
                                Kurt.Layout.Variant_Field_Count (EN, FV);
                           begin
                              if SC /= FC
                                or else (SC > 0 and then not Same_Type
                                  (Kurt.Layout.Variant_Field_Type
                                     (OT, SV, 1),
                                   Kurt.Layout.Variant_Field_Type
                                     (OT, FV, 1)))
                              then
                                 Error ("'!' on '" & Image (OT)
                                        & "' needs a declared inverted "
                                        & "pair -- asymmetric payloads "
                                        & "(spec 7.2.1; bootstrap supports "
                                        & "the self-inverse case only)");
                              end if;
                           end;
                        end if;
                     end if;
                  end if;
                  E.Sem_Ty := OT;
                  return OT;
               end;

            when E_Question =>
               --  §6.2.4: `e?` requires e and the enclosing fn return to
               --  both satisfy `contract`. Failure payload types shall
               --  match. The expression's type is e's success payload.
               declare
                  IT : constant Type_Access := Infer (E.Q_Inner, null);
                  EN : constant String :=
                    (if IT /= null and then IT.Kind = T_Named
                     then SU.To_String (IT.Name) else "");
                  Ret_EN : constant String :=
                    (if Cur_Ret /= null and then Cur_Ret.Kind = T_Named
                     then SU.To_String (Cur_Ret.Name) else "");
               begin
                  if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN) then
                     Error ("`?` operand must satisfy `contract`, got '"
                            & Image (IT) & "'");
                     E.Sem_Ty := IT;
                     return E.Sem_Ty;
                  end if;
                  if Ret_EN = ""
                    or else not Kurt.Layout.Is_Contract_Enum (Ret_EN)
                  then
                     Error ("`?` requires the enclosing subroutine to "
                            & "return a `contract` type; got '"
                            & Image (Cur_Ret) & "'");
                  elsif not Same_Type (Kurt.Layout.Variant_Field_Type
                          (IT, Kurt.Layout.Contract_Fail_Variant (EN), 1),
                        Kurt.Layout.Variant_Field_Type
                          (Cur_Ret,
                           Kurt.Layout.Contract_Fail_Variant (Ret_EN), 1))
                  then
                     Error ("`?` failure payload type of '" & Image (IT)
                            & "' does not match the enclosing return "
                            & "type '" & Image (Cur_Ret) & "' (spec 7.2.4)");
                  end if;
                  E.Sem_Ty := Kurt.Layout.Variant_Field_Type
                    (IT, Kurt.Layout.Contract_Success_Variant (EN), 1);
                  return E.Sem_Ty;
               end;

            when E_Tuple_Lit =>
               --  §6.1.7: type is .{T1, ..., TN} from element types. When an
               --  expected tuple type is in context, steer each element.
               declare
                  Tup : constant Type_Access :=
                    new AST_Type (Kind => T_Tuple);
               begin
                  for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index
                  loop
                     declare
                        Exp : Type_Access := null;
                        Eit : constant Expr_Access := E.TL_Elems.Element (I);
                     begin
                        if Expected /= null and then Expected.Kind = T_Tuple
                          and then I - E.TL_Elems.First_Index
                            < Natural (Expected.Elems.Length)
                        then
                           Exp := Expected.Elems.Element
                             (Expected.Elems.First_Index
                                + (I - E.TL_Elems.First_Index));
                        end if;
                        Tup.Elems.Append (Infer (Eit, Exp));
                     end;
                  end loop;
                  E.Sem_Ty := Tup;
                  return Tup;
               end;

            when E_Ref =>
               --  §8.1 reference creation. The place is a binding or field
               --  access; the result type is `sigil [mods] T`.
               declare
                  PT : constant Type_Access := Infer (E.Rf_Place, null);
               begin
                  if E.Rf_Place.Kind /= E_Path
                    and then E.Rf_Place.Kind /= E_Field
                    and then E.Rf_Place.Kind /= E_Deref
                  then
                     Error ("reference creation requires a place "
                            & "expression (binding, field, or deref)");
                  end if;
                  --  §8.5.2: atomic/guard references are restricted to
                  --  unsigned integer referents.
                  if E.Rf_Store in RS_Atomic | RS_Guard
                    and then not Is_Unsigned_Int_Type (PT)
                  then
                     Error ("'&" & (if E.Rf_Store = RS_Atomic
                                    then "atomic" else "guard")
                            & "' requires an unsigned integer referent, "
                            & "got '" & Image (PT) & "' (spec 8.5.2)");
                  end if;
                  --  §5.4: only shared references may be created from an
                  --  immutable `static` in landside code.
                  if E.Rf_Place.Kind = E_Path
                    and then Natural (E.Rf_Place.Segments.Length) = 1
                  then
                     declare
                        Name : constant String := SU.To_String
                          (E.Rf_Place.Segments.Last_Element);
                        M    : Boolean;
                     begin
                        if Lookup_Scope (Name) = null
                          and then Find_Static_Decl (Name, M)
                          and then not M
                          and then (E.Rf_Sigil = R_Excl
                                    or else E.Rf_Store = RS_Mut)
                        then
                           Error ("only shared references ('&', "
                                  & "'&volatile', '&atomic', '&guard') "
                                  & "may be created from immutable "
                                  & "static '" & Name & "' (spec 5.4)");
                        end if;
                        --  §2.2.1: an exclusive ('$') or '&mut' reference may
                        --  be created only from a mutable binding.
                        declare
                           Bmut, Found : Boolean;
                        begin
                           Bmut := Lookup_Scope_Mut (Name, Found);
                           if Found and then not Bmut
                             and then (E.Rf_Sigil = R_Excl
                                       or else E.Rf_Store = RS_Mut)
                           then
                              Error ("an exclusive ('$') or '&mut' reference "
                                     & "requires a mutable binding; '" & Name
                                     & "' is an immutable `let` (spec 2.2.1)");
                           end if;
                        end;
                     end;
                  end if;
                  E.Sem_Ty :=
                    Mk_Ref (E.Rf_Sigil, E.Rf_Volatile, E.Rf_Store, PT);
                  return E.Sem_Ty;
               end;

            when E_CAS =>
               --  §8.7: the target shall be `&atomic T` or `&guard T`;
               --  expected/new are T. The result is verdict.<T, T>.
               declare
                  TT : constant Type_Access := Infer (E.CAS_Tgt, null);
                  RT : Type_Access := null;   --  referent T
               begin
                  if not Is_Ref (TT)
                    or else TT.R_Store not in RS_Atomic | RS_Guard
                  then
                     Error ("compare-and-swap target shall be '&atomic T' "
                            & "or '&guard T', got '" & Image (TT)
                            & "' (spec 8.7)");
                  elsif not Is_Unsigned_Int_Type (TT.Target) then
                     --  §8.5.2 via §8.7: the referent shall be an unsigned
                     --  integer type.
                     Error ("compare-and-swap referent shall be an "
                            & "unsigned integer type, got '"
                            & Image (TT.Target) & "' (spec 8.7, 8.5.2)");
                  else
                     RT := TT.Target;
                  end if;

                  declare
                     ET : constant Type_Access := Infer (E.CAS_Exp, RT);
                     NT : constant Type_Access := Infer (E.CAS_New, RT);
                  begin
                     if RT /= null then
                        if not Assignable (RT, ET) then
                           Error ("CAS expected operand: expected '"
                                  & Image (RT) & "' but got '"
                                  & Image (ET) & "'");
                        end if;
                        if not Assignable (RT, NT) then
                           Error ("CAS new operand: expected '"
                                  & Image (RT) & "' but got '"
                                  & Image (NT) & "'");
                        end if;
                     end if;
                  end;

                  --  §4.5/§8.7 result type is the intrinsic verdict.<T, T>
                  --  (T the referent type) — built directly, no instantiation.
                  if RT /= null then
                     declare
                        V : constant Type_Access :=
                          new AST_Type (Kind => T_Named);
                     begin
                        V.Name := SU.To_Unbounded_String ("verdict");
                        V.Args.Append (RT);
                        V.Args.Append (RT);
                        E.Sem_Ty := V;
                     end;
                  else
                     E.Sem_Ty := null;
                  end if;
                  return E.Sem_Ty;
               end;

            when E_Array_Lit =>
               --  §6.1.6: element list or repeat form. The element type is
               --  steered by the expected array type when present.
               declare
                  Exp_Elem : constant Type_Access :=
                    (if Expected /= null and then Expected.Kind = T_Array
                     then Expected.Elem else null);
                  ET  : Type_Access := null;
                  Arr : constant Type_Access :=
                    new AST_Type (Kind => T_Array);
               begin
                  for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index
                  loop
                     declare
                        T : constant Type_Access :=
                          Infer (E.AL_Elems.Element (I),
                                 (if ET = null then Exp_Elem else ET));
                     begin
                        --  §9.5: a `[&dyn Trait; N]` literal coerces each
                        --  `&U` element (U implements Trait) to `&dyn Trait`.
                        if Is_Dyn_Ref (Exp_Elem) and then Is_Ref (T)
                          and then T.Target /= null
                          and then T.Target.Kind = T_Named
                          and then Type_Implements
                            (SU.To_String (T.Target.Name),
                             SU.To_String (Exp_Elem.Target.Trait_Name))
                        then
                           declare
                              DC : constant Expr_Access :=
                                new Expr_Node (Kind => E_Dyn_Cast);
                           begin
                              DC.DC_Inner := E.AL_Elems.Element (I);
                              DC.DC_Conc  := T.Target.Name;
                              DC.DC_Trait := Exp_Elem.Target.Trait_Name;
                              DC.Sem_Ty   := Exp_Elem;
                              E.AL_Elems.Replace_Element (I, DC);
                           end;
                           ET := Exp_Elem;
                        elsif ET = null then
                           ET := T;
                        elsif not Same_Type (ET, T) then
                           Error ("array literal elements have differing "
                                  & "types: '" & Image (ET) & "' vs '"
                                  & Image (T) & "'");
                        end if;
                     end;
                  end loop;
                  Arr.Elem := ET;
                  Arr.Len  :=
                    (if E.AL_Repeat > 0 then E.AL_Repeat
                     else Natural (E.AL_Elems.Length));
                  if Expected /= null and then Expected.Kind = T_Array
                    and then Expected.Len /= Arr.Len
                  then
                     Error ("array literal has" & Arr.Len'Image
                            & " elements but the expected type '"
                            & Image (Expected) & "' has"
                            & Expected.Len'Image);
                  end if;
                  E.Sem_Ty := Arr;
                  return Arr;
               end;

            when E_Dyn_Cast =>
               --  Synthesised by the coercion logic below; its type is
               --  the `&dyn Trait` it was annotated with at creation.
               return E.Sem_Ty;

            when E_Slice_Cast =>
               --  Synthesised by the coercion logic below; type is the
               --  `&[T]` it was annotated with at creation.
               return E.Sem_Ty;

            when E_Type_Intrinsic =>
               --  §6.12.1 layout intrinsics: translation-time `uaddr`
               --  constants. The operand shall be a known sized type;
               --  `@offset` additionally requires a struct field.
               declare
                  Known : Boolean := False;
               begin
                  if E.TI_Ty.Kind in T_Ref | T_Tuple | T_Array then
                     Known := True;
                  elsif E.TI_Ty.Kind = T_Named then
                     declare
                        TN : constant String := SU.To_String (E.TI_Ty.Name);
                     begin
                        --  §4: `void` is a complete type — size 0, align 0.
                        Known :=
                          Is_Integer_Type (E.TI_Ty)
                          or else Is_Float_Type (E.TI_Ty)
                          or else TN = "bool"
                          or else TN = "void"
                          or else Kurt.Layout.Is_Struct (TN)
                          or else Kurt.Layout.Is_Enum (TN);
                     end;
                  end if;

                  if E.TI_Ty.Kind = T_Array and then E.TI_Ty.Len = 0
                    and then E.TI_Op in TI_Size | TI_Align
                  then
                     --  §8.1.4: `[T]` is not a type — it exists only inside
                     --  a slice-reference production, so it has no size of
                     --  its own to query.
                     Error ("`@size`/`@align` cannot be applied to `[T]`: "
                            & "a slice exists only behind a reference "
                            & "(spec 8.1.4)");
                  elsif not Known then
                     declare
                        TypeNameStr : constant String :=
                          (if E.TI_Ty.Kind = T_Named then SU.To_String (E.TI_Ty.Name)
                           else "anonymous type");
                     begin
                        Error ("type intrinsic on unknown type '" & TypeNameStr
                               & "' (spec 6.12)");
                     end;
                  elsif E.TI_Op = TI_Offset then
                     if E.TI_Ty.Kind /= T_Named or else not Kurt.Layout.Is_Struct (SU.To_String (E.TI_Ty.Name)) then
                        Error ("`@offset` requires a struct type, got '"
                               & (if E.TI_Ty.Kind = T_Named then SU.To_String (E.TI_Ty.Name) else "anonymous type")
                               & "' (spec 6.12.1)");
                     elsif Kurt.Layout.Field_Type
                             (SU.To_String (E.TI_Ty.Name), SU.To_String (E.TI_Field)) = null
                     then
                        Error ("struct '" & SU.To_String (E.TI_Ty.Name) & "' has no field '"
                               & SU.To_String (E.TI_Field)
                               & "' (spec 6.12.1)");
                     end if;
                  end if;
                  E.Sem_Ty := Mk_Named ("uaddr");
                  return E.Sem_Ty;
               end;

            when E_Uninit =>
               --  §6.1.8: `uninit` is valid only as the value of an
               --  assignment to a binding's object (handled in S_Let/S_Mut/
               --  S_Assign). Reaching it through ordinary inference means it
               --  appeared in some other position, which is ill-formed.
               Error ("`uninit` shall appear only as the value of an "
                      & "assignment to a binding (spec 6.1.8)");
               E.Sem_Ty := Expected;
               return Expected;

            when E_Closure =>
               --  §9.9 the value type of a *non-capturing* closure is the
               --  invocable signature `fn(param types) -> return type` (it is
               --  a plain subroutine pointer). A *capturing* closure's value
               --  type is its anonymous capture struct `$clo_N$env`: each
               --  field holds a copy of a captured binding, and the value is
               --  invoked through the lifted subroutine `$clo_N(self, ...)`.
               --  The body is checked via the subroutine Kurt.Mono lifted it
               --  to; the return type is the explicit `-> U` or inferred from
               --  the body's first return (params pushed temporarily).
               declare
                  RT    : Type_Access := E.Clo_Ret;
                  Saved : constant Natural := Natural (Scope.Length);
                  FT    : constant Type_Access :=
                    new AST_Type (Kind => T_Fn);
               begin
                  --  §9.9.3 resolve each capture's type from the creating
                  --  scope and finalise the anonymous capture struct (whose
                  --  fields Kurt.Mono left untyped), then re-register the
                  --  layout so the lifted subroutine and the closure value
                  --  see the completed struct.
                  if not E.Clo_Caps.Is_Empty then
                     for K in E.Clo_Caps.First_Index ..
                              E.Clo_Caps.Last_Index
                     loop
                        declare
                           CN : constant String :=
                             SU.To_String (E.Clo_Caps.Element (K).Name);
                           CT : constant Type_Access := Lookup_Scope (CN);
                           C  : Closure_Param := E.Clo_Caps.Element (K);
                        begin
                           if CT = null then
                              Error ("closure captures '" & CN & "', whose "
                                     & "type cannot be determined in the "
                                     & "enclosing scope (spec 9.9.3)");
                           end if;
                           C.Ty := CT;
                           E.Clo_Caps.Replace_Element (K, C);
                           --  §9.9.2/§9.9.3: capturing a `with destruct`
                           --  binding transfers ownership into the closure and
                           --  shall be declared `xfer`. The captured binding is
                           --  invalidated in the enclosing scope; the env type
                           --  acquires `with destruct` (it now has a
                           --  destruct-satisfying field) and its destructor
                           --  destroys the moved value at scope exit.
                           if Satisfies_Destruct (CT) then
                              if not E.Clo_Xfer then
                                 Error ("closure captures the `with destruct` "
                                        & "binding '" & CN & "'; it shall be "
                                        & "declared `xfer` (spec 9.9.2)");
                              end if;
                              Mark_Moved (CN);
                           end if;
                           --  An aggregate capture (struct / tuple / array /
                           --  payload enum) lives in memory and cannot become
                           --  a register value, and a `with destruct` capture
                           --  must not be re-copied into an owned local (that
                           --  would double-destroy). So bind the body's view
                           --  of it by reference to the env field, rewriting
                           --  the prefix `let cap = self.cap;` (synthesised by
                           --  Kurt.Mono) into `let cap = &self.cap;`. Scalar
                           --  copyable captures keep their by-copy local.
                           if Cap_By_Ref (CT)
                             and then K - E.Clo_Caps.First_Index
                                        < Integer (E.Clo_Body.Length)
                           then
                              declare
                                 PS : constant Stmt_Access :=
                                   E.Clo_Body.Element
                                     (E.Clo_Body.First_Index
                                        + (K - E.Clo_Caps.First_Index));
                                 Ref : constant Expr_Access :=
                                   new Expr_Node (Kind => E_Ref);
                                 RT2 : constant Type_Access :=
                                   new AST_Type (Kind => T_Ref);
                              begin
                                 if PS.Kind = S_Let
                                   and then PS.L_Init /= null
                                   and then PS.L_Init.Kind = E_Field
                                 then
                                    Ref.Rf_Sigil := R_Shared;
                                    Ref.Rf_Place := PS.L_Init;
                                    PS.L_Init := Ref;
                                    RT2.Sigil  := R_Shared;
                                    RT2.Target := CT;
                                    PS.L_Ty := RT2;
                                 end if;
                              end;
                           end if;
                        end;
                     end loop;
                     for SI in U.Structs.First_Index ..
                               U.Structs.Last_Index
                     loop
                        if SU.To_String (U.Structs.Element (SI).Name)
                          = SU.To_String (E.Clo_Env_Name)
                        then
                           declare
                              SD : Struct_Decl := U.Structs.Element (SI);
                           begin
                              for K in SD.Fields.First_Index ..
                                       SD.Fields.Last_Index
                              loop
                                 declare
                                    FF : Struct_Field := SD.Fields.Element (K);
                                 begin
                                    FF.Ty := E.Clo_Caps.Element (K).Ty;
                                    SD.Fields.Replace_Element (K, FF);
                                 end;
                              end loop;
                              U.Structs.Replace_Element (SI, SD);
                           end;
                        end if;
                     end loop;
                     Kurt.Layout.Register (U);
                  end if;

                  for P of E.Clo_Params loop
                     Scope.Append ((Name => P.Name, Ty => P.Ty, others => <>));
                  end loop;
                  if RT = null then
                     for S of E.Clo_Body loop
                        if S.Kind = S_Return and then S.R_Val /= null then
                           RT := Infer (S.R_Val, null);
                           exit;
                        end if;
                     end loop;
                  end if;
                  while Natural (Scope.Length) > Saved loop
                     Scope.Delete_Last;
                  end loop;
                  if RT = null then
                     RT := Mk_Named ("void");
                  end if;

                  --  Propagate the return type (resolved here, where the
                  --  captures are in scope) onto the lifted subroutine, so its
                  --  own Check_Fn does not re-infer it before the
                  --  capture-loading prefix `let`s have entered scope.
                  for FI in U.Fns.First_Index .. U.Fns.Last_Index loop
                     if SU.To_String (U.Fns.Element (FI).Header.Name)
                       = SU.To_String (E.Clo_Fn_Name)
                       and then U.Fns.Element (FI).Header.Return_Type = null
                     then
                        declare
                           LF : Fn_Decl := U.Fns.Element (FI);
                        begin
                           LF.Header.Return_Type := RT;
                           U.Fns.Replace_Element (FI, LF);
                        end;
                     end if;
                  end loop;

                  if not E.Clo_Caps.Is_Empty then
                     --  Capturing: the value is the anonymous env struct.
                     E.Sem_Ty := Mk_Named (SU.To_String (E.Clo_Env_Name));
                     return E.Sem_Ty;
                  end if;

                  for P of E.Clo_Params loop
                     FT.Fn_Params.Append (P.Ty);
                  end loop;
                  FT.Fn_Ret := RT;
                  E.Sem_Ty := FT;
                  return FT;
               end;

            when E_Destruct =>
               --  §8.4/§8.11: `destruct(e)` runs e's destructor now;
               --  `undestruct(e)` reclaims e's storage without running it
               --  (airside only). Both consume the operand binding — a
               --  later use is a use-after-transfer failure. The result is
               --  `void`.
               declare
                  IT      : constant Type_Access := Infer (E.DT_Inner, null);
                  Is_Bind : constant Boolean :=
                    E.DT_Inner /= null and then E.DT_Inner.Kind = E_Path
                    and then Natural (E.DT_Inner.Segments.Length) = 1;
                  Word    : constant String :=
                    (if E.DT_Undo then "`undestruct`" else "`destruct`");
               begin
                  if not Is_Bind then
                     Error (Word & " operand shall be a binding (bootstrap)");
                  elsif not Satisfies_Destruct (IT) then
                     Error (Word & " requires an operand whose type satisfies "
                            & "`destruct` (spec 8.11)");
                  end if;
                  if E.DT_Undo and then In_Airside = 0 then
                     Error ("`undestruct` shall appear only inside an "
                            & "`airside` block or `airside fn` body "
                            & "(spec 8.4)");
                  end if;
                  Maybe_Move (E.DT_Inner);
                  E.Sem_Ty := Mk_Named ("void");
                  return E.Sem_Ty;
               end;

            when E_Airside_Blk =>
               --  §6.9 `airside { ... }` block expression. The body is
               --  checked as an airside lexical scope; the block's type is
               --  the type of the trailing `express` value, or `void` when
               --  no `express` targets the block. (Bootstrap: only a
               --  trailing `express` yields the value.)
               declare
                  Saved : constant Type_Access := Express_Expected;
               begin
                  Express_Expected := Expected;
                  if E.AB_Airside then
                     In_Airside := In_Airside + 1;
                  end if;
                  Check_Block (E.AB_Stmts);
                  if E.AB_Airside then
                     In_Airside := In_Airside - 1;
                  end if;
                  Express_Expected := Saved;
               end;
               if not E.AB_Stmts.Is_Empty
                 and then E.AB_Stmts.Last_Element.Kind = S_Express
                 and then E.AB_Stmts.Last_Element.Xp_Val /= null
               then
                  E.Sem_Ty := E.AB_Stmts.Last_Element.Xp_Val.Sem_Ty;
               else
                  E.Sem_Ty := Mk_Named ("void");
               end if;
               return E.Sem_Ty;

            when E_Loop =>
               --  §7.7 `loop { … }` as an expression. The body is checked in
               --  a loop context; its type is the annotated (expected) type
               --  when known, otherwise the type of the first `break expr`
               --  targeting this loop, or `never` when no break carries a
               --  value (a diverging loop).
               declare
                  Found : Type_Access := null;

                  --  Scan for a `break`-with-value that targets this loop:
                  --  descend into `if`/`airside` bodies but not into a nested
                  --  loop (whose breaks target the inner loop).
                  procedure Scan (V : Stmt_Vectors.Vector) is
                  begin
                     for I in V.First_Index .. V.Last_Index loop
                        declare
                           BS : constant Stmt_Access := V.Element (I);
                        begin
                           case BS.Kind is
                              when S_Break =>
                                 if Found = null
                                   and then BS.Brk_Val /= null
                                 then
                                    Found := BS.Brk_Val.Sem_Ty;
                                 end if;
                              when S_If =>
                                 Scan (BS.SI_Then);
                                 Scan (BS.SI_Else);
                              when S_Airside_Block =>
                                 Scan (BS.A_Stmts);
                              when others =>
                                 null;   --  skip S_While (nested loop)
                           end case;
                        end;
                     end loop;
                  end Scan;
               begin
                  In_Loop := In_Loop + 1;
                  Check_Block (E.Loop_Body);
                  In_Loop := In_Loop - 1;
                  if Expected /= null and then not Is_Void_Type (Expected) then
                     E.Sem_Ty := Expected;
                  else
                     Scan (E.Loop_Body);
                     E.Sem_Ty :=
                       (if Found /= null then Found else Mk_Named ("never"));
                  end if;
               end;
               return E.Sem_Ty;
         end case;
      end Infer;

      --  §6.1.8 shared check for a `uninit` value in a valid assignment
      --  position: it must occur in an airside region, and the target type
      --  must be known (so the binding's object has a determinate type).
      procedure Check_Uninit (Target : Type_Access) is
      begin
         if In_Airside = 0 then
            Error ("`uninit` shall appear only inside an `airside` block or "
                   & "`airside fn` body (spec 6.1.8)");
         end if;
         if Target = null then
            Error ("`uninit` requires a known target type; annotate the "
                   & "binding (spec 6.1.8)");
         end if;
      end Check_Uninit;

      --  §7.9: a labelled `break`/`continue` shall name a loop label that is
      --  in scope. An empty label (plain break/continue) is always allowed.
      procedure Check_Loop_Label (Label : SU.Unbounded_String) is
      begin
         if SU.Length (Label) = 0 then
            return;
         end if;
         for I in Label_Stack.First_Index .. Label_Stack.Last_Index loop
            if SU.To_String (Label_Stack.Element (I))
                 = SU.To_String (Label)
            then
               return;
            end if;
         end loop;
         Error ("`break`/`continue` names loop label ''" & SU.To_String (Label)
                & "' which is not in scope (spec 7.9)");
      end Check_Loop_Label;

      --------------------------------------------------------------------
      --  §7.11 divergence analysis (bootstrap subset). A statement list
      --  diverges when control cannot reach its end. The diverging forms
      --  recognised here: `@trap`, `return`, `break`, `continue`,
      --  `express`, a `-> never` call, a `loop {}` with no `break`, an
      --  `if`/`else` whose both arms diverge, and an `airside` block
      --  whose body diverges.
      function Cond_Is_True (E : Expr_Access) return Boolean is
        (E /= null and then E.Kind = E_Bool_Lit and then E.Bool_V);

      --  §7.11: a `loop {}` diverges only when no `break` (targeting it or
      --  an enclosing loop) and no `express` (targeting an enclosing
      --  block) is reachable in its body. Conservative: any such escape
      --  anywhere in V disqualifies it, even one bound to a nested
      --  construct — a false negative is safe; a false positive is not.
      function Has_Escape (V : Stmt_Vectors.Vector) return Boolean is
      begin
         for I in V.First_Index .. V.Last_Index loop
            declare
               S : constant Stmt_Access := V.Element (I);
            begin
               case S.Kind is
                  when S_Break | S_Express => return True;
                  when S_Airside_Block =>
                     if Has_Escape (S.A_Stmts) then return True; end if;
                  when S_If =>
                     if Has_Escape (S.SI_Then)
                       or else Has_Escape (S.SI_Else)
                     then return True; end if;
                  when S_While =>
                     if Has_Escape (S.W_Body)
                       or else Has_Escape (S.W_Then)
                     then return True; end if;
                  when S_Extract =>
                     if Has_Escape (S.X_Else) then return True; end if;
                  when others => null;
               end case;
            end;
         end loop;
         return False;
      end Has_Escape;

      function Stmts_Diverge (V : Stmt_Vectors.Vector) return Boolean;

      function Stmt_Diverges (S : Stmt_Access) return Boolean is
      begin
         if S = null then
            return False;
         end if;
         case S.Kind is
            when S_Trap | S_Return | S_Break | S_Continue | S_Express =>
               return True;
            when S_Expr =>
               --  §7.11: a `-> never` call (its value type is `never`).
               return Is_Never_Ty (S.E_Val.Sem_Ty);
            when S_Airside_Block =>
               return Stmts_Diverge (S.A_Stmts);
            when S_If =>
               return (not S.SI_Else.Is_Empty)
                 and then Stmts_Diverge (S.SI_Then)
                 and then Stmts_Diverge (S.SI_Else);
            when S_While =>
               --  `loop { ... }` desugars to `while true`; with no escaping
               --  break/express it never transfers control onward.
               return Cond_Is_True (S.W_Cond)
                 and then not Has_Escape (S.W_Body);
            when S_Let | S_Mut | S_Assign | S_Fence | S_Extract
               | S_Asm =>
               return False;
         end case;
      end Stmt_Diverges;

      function Stmts_Diverge (V : Stmt_Vectors.Vector) return Boolean is
      begin
         --  Once a statement diverges, the rest of the list is
         --  unreachable, so the list diverges from that point.
         for I in V.First_Index .. V.Last_Index loop
            if Stmt_Diverges (V.Element (I)) then
               return True;
            end if;
         end loop;
         return False;
      end Stmts_Diverge;

      --------------------------------------------------------------------
      procedure Check_Stmt (S : Stmt_Access);

      --  §8.2/§8.3: map a reference sigil + store modifier to its initial
      --  permission state. `&raw` is untracked (§8.2.2): Tracked is False.
      procedure Borrow_State
        (Sigil   : Ref_Sigil;
         Store   : Ref_Store;
         State   : out Kurt.Borrow.Perm_State;
         Tracked : out Boolean)
      is
      begin
         Tracked := True;
         case Sigil is
            when R_Raw =>
               Tracked := False;
               State   := Kurt.Borrow.Shared_RO;
            when R_Excl =>
               State := Kurt.Borrow.Idle;            --  $T
            when R_Shared =>
               case Store is
                  when RS_None => State := Kurt.Borrow.Shared_RO;
                  when RS_Mut  => State := Kurt.Borrow.Shared_RW;
                  when RS_Atomic | RS_Guard =>
                     State := Kurt.Borrow.Atomic_Ref;
               end case;
         end case;
      end Borrow_State;

      --  §8.2: when `Name` is bound to `&x`/`$x`/`&mut x` (etc.) of a simple
      --  named place, register the reference in the derivation tree and apply
      --  the §8.3 aliasing constraint at creation.
      procedure Register_Borrow (Name : String; Init : Expr_Access) is
      begin
         if Init = null or else Init.Kind /= E_Ref
           or else Init.Rf_Place.Kind /= E_Path
           or else Natural (Init.Rf_Place.Segments.Length) /= 1
         then
            return;
         end if;
         declare
            Place : constant String :=
              SU.To_String (Init.Rf_Place.Segments.Last_Element);
            St    : Kurt.Borrow.Perm_State;
            Tr    : Boolean;
         begin
            Borrow_State (Init.Rf_Sigil, Init.Rf_Store, St, Tr);
            if not Tr then
               return;
            end if;
            --  §8.3 Constraint: a new reference to a place already held by a
            --  `$T` at Assert_Excl provably aliases the exclusive reference.
            if Kurt.Borrow.Has_Asserted_Excl (Borrows, Place) then
               Error ("reference to '" & Place & "' aliases an exclusive "
                      & "'$' reference that has asserted exclusivity "
                      & "(spec 8.3)");
            end if;
            declare
               Ignore : constant Kurt.Borrow.Node_Id :=
                 Kurt.Borrow.Create
                   (Borrows, Referent => Place, Bound_To => Name,
                    State => St, Scope_Len => Natural (Scope.Length));
               pragma Unreferenced (Ignore);
            begin
               null;
            end;
         end;
      end Register_Borrow;

      --  §8.3: a store through `*binding` whose binding holds a tracked
      --  reference. An exclusive store asserts exclusivity; if the place is
      --  aliased by another live reference, that is a provable violation.
      procedure Register_Store (Lhs : Expr_Access) is
      begin
         if Lhs.Kind /= E_Deref
           or else Lhs.D_Inner.Kind /= E_Path
           or else Natural (Lhs.D_Inner.Segments.Length) /= 1
         then
            return;
         end if;
         declare
            Name : constant String :=
              SU.To_String (Lhs.D_Inner.Segments.Last_Element);
            N    : constant Kurt.Borrow.Node_Id :=
              Kurt.Borrow.Of_Binding (Borrows, Name);
         begin
            if N = Kurt.Borrow.No_Node then
               return;
            end if;
            Kurt.Borrow.Record_Store (Borrows, N);
            if Kurt.Borrow.Is_Exclusive
                 (Kurt.Borrow.State_Of (Borrows, N))
              and then Kurt.Borrow.Has_Live_Alias (Borrows, N)
            then
               Error ("store through exclusive '$' reference '" & Name
                      & "' whose referent is aliased by a live reference "
                      & "(spec 8.3)");
            end if;
            --  §8.3 the store is a foreign event for every other reference to
            --  the same place: apply the permission-state transition (after
            --  the alias check above, which is the mandatory diagnostic).
            --  An atomic store goes through an `atomic`/`guard` reference.
            Kurt.Borrow.Apply_Foreign_Store
              (Borrows, N,
               Atomic => Kurt.Borrow.State_Of (Borrows, N) =
                         Kurt.Borrow.Atomic_Ref);
         end;
      end Register_Store;

      --  §8.4 a place outlives the call iff its storage has program lifetime
      --  ('static / 'const): a top-level `static`/`static mut` or a `const`.
      --  A local `let`/`mut` binding or a value parameter dies when the call
      --  returns, so a reference to it shall not be returned.
      function Outlives_Call (Place : String) return Boolean is
         Dummy : Boolean;
      begin
         if Find_Static_Decl (Place, Dummy) then
            return True;
         end if;
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            if SU.To_String (U.Consts.Element (I).Name) = Place then
               return True;
            end if;
         end loop;
         return False;
      end Outlives_Call;

      --  §8.4.3 escape verification: a returned landside reference shall not
      --  outlive its referent. The referent must have program lifetime; a
      --  reference to a local or to a value parameter escapes its scope.
      --  Provenance of a returned reference binding comes from the derivation
      --  tree (`let r = &local; return r;` is caught the same as `return
      --  &local;`). `&raw` is unmanaged (airside responsibility) and exempt.
      procedure Check_Return_Escape (E : Expr_Access) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Ref =>
               if E.Rf_Sigil /= R_Raw
                 and then E.Rf_Place /= null
                 and then E.Rf_Place.Kind = E_Path
                 and then Natural (E.Rf_Place.Segments.Length) >= 1
               then
                  declare
                     Root : constant String :=
                       SU.To_String (E.Rf_Place.Segments.First_Element);
                  begin
                     if not Outlives_Call (Root) then
                        Error ("returns a reference to '" & Root
                               & "', which does not outlive the call; its "
                               & "referent escapes its scope (spec 8.4.3)");
                     end if;
                  end;
               end if;
            when E_Path =>
               if Natural (E.Segments.Length) = 1 then
                  declare
                     Name : constant String :=
                       SU.To_String (E.Segments.Last_Element);
                     N    : constant Kurt.Borrow.Node_Id :=
                       Kurt.Borrow.Of_Binding (Borrows, Name);
                  begin
                     --  A tracked local reference: check what it points to.
                     --  No node ⇒ a reference parameter (its referent is the
                     --  caller's, which outlives the call) or an untracked
                     --  chain — conservatively permitted.
                     if N /= Kurt.Borrow.No_Node then
                        declare
                           Ref : constant String :=
                             Kurt.Borrow.Referent_Of (Borrows, N);
                        begin
                           if not Outlives_Call (Ref) then
                              Error ("returns reference '" & Name
                                     & "' pointing to '" & Ref
                                     & "', which does not outlive the call "
                                     & "(spec 8.4.3)");
                           end if;
                        end;
                     end if;
                  end;
               end if;
            when E_Cast =>
               --  A reference cast preserves the referent (§6.8.8).
               Check_Return_Escape (E.Cast_Inner);
            when others =>
               null;  --  call results etc.: the callee's signature is
                      --  verified at its own definition.
         end case;
      end Check_Return_Escape;

      procedure Check_Block (Stmts : Stmt_Vectors.Vector) is
         Entry_Len  : constant Natural := Natural (Scope.Length);
         --  §5.17: this block opens a fresh scope. Names already in Scope
         --  (params, outer-block locals, and any pattern bindings appended
         --  just before this call) belong to enclosing scopes and may be
         --  shadowed; only declarations made within this block collide.
         Saved_Base : constant Natural := Block_Base;
      begin
         Block_Base := Entry_Len;
         for I in Stmts.First_Index .. Stmts.Last_Index loop
            Check_Stmt (Stmts.Element (I));
         end loop;
         Block_Base := Saved_Base;
         --  §8.2 liveness: references bound inside this block lapse at its
         --  end (their bindings leave scope).
         Kurt.Borrow.Kill_Above (Borrows, Entry_Len);
         --  §8.8.2: moved-binding records for this block's bindings lapse too.
         for I in reverse 1 .. Natural (Moved.Length) loop
            if Moved.Element (I).Depth > Entry_Len then
               Moved.Delete (I);
            end if;
         end loop;
      end Check_Block;

      --  §5.17: a name shall be declared at most once within a scope. Flag a
      --  collision with a binding already declared in the current block;
      --  bindings below Block_Base belong to outer scopes and are shadowed.
      procedure Check_Dup_In_Scope (Name : SU.Unbounded_String) is
      begin
         for I in Block_Base + 1 .. Natural (Scope.Length) loop
            if SU.To_String (Scope.Element (I).Name) = SU.To_String (Name) then
               Error ("'" & SU.To_String (Name) & "' is already declared in "
                      & "this scope (spec 5.17)");
               return;
            end if;
         end loop;
      end Check_Dup_In_Scope;

      procedure Check_Stmt (S : Stmt_Access) is
      begin
         case S.Kind is
            when S_Return =>
               if S.R_Val = null then
                  --  §5.1 bare `return;` is well-formed only in a subroutine
                  --  whose return type is `void`.
                  if Cur_Ret /= null and then not Is_Void_Type (Cur_Ret) then
                     Error ("bare `return;` in a subroutine returning '"
                            & Image (Cur_Ret) & "'; a value is required "
                            & "(spec 5.1)");
                  end if;
                  return;
               end if;
               declare
                  RT : constant Type_Access := Infer (S.R_Val, Cur_Ret);
               begin
                  if not Assignable (Cur_Ret, RT) then
                     Error ("return type mismatch: subroutine returns '"
                            & Image (Cur_Ret) & "' but expression is '"
                            & Image (RT) & "'");
                  end if;
                  --  §8.4.3: a returned landside reference shall not outlive
                  --  its referent (no reference to a local / value parameter).
                  if Cur_Ret /= null and then Cur_Ret.Kind = T_Ref
                    and then Cur_Ret.Sigil /= R_Raw
                  then
                     Check_Return_Escape (S.R_Val);
                  end if;
                  --  §8.8.2: returning a `destruct`-typed binding transfers it.
                  Maybe_Move (S.R_Val);
               end;

            when S_Expr =>
               declare
                  ET : constant Type_Access := Infer (S.E_Val, null);
                  pragma Unreferenced (ET);
               begin
                  null;
               end;

            when S_Let | S_Mut =>
               if S.L_Is_Refut then
                  --  §5.2.1 refutable let-else: `let Enum::V { binds } = e
                  --  else { diverge };`. On a match the payload binds for the
                  --  rest of the enclosing scope; the else block (which sees no
                  --  payload binding) runs on mismatch.
                  declare
                     CT : constant Type_Access := Infer (S.L_Init, null);
                     EN : constant String :=
                       (if CT /= null and then CT.Kind = T_Named
                        then SU.To_String (CT.Name) else "");
                     VN : constant String :=
                       SU.To_String (S.L_Refut_Pat.Path.Last_Element);
                  begin
                     if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                        Error ("refutable `let` requires an enum value; got '"
                               & Image (CT) & "' (spec 5.2.1)");
                     elsif not Kurt.Layout.Has_Variant (EN, VN) then
                        Error ("enum '" & EN & "' has no variant '" & VN
                               & "' (spec 5.2.1)");
                     end if;
                     --  else first (no payload in scope here), then the
                     --  payload bindings persist into the enclosing scope.
                     Check_Block (S.L_Else);
                     if EN /= "" and then Kurt.Layout.Is_Enum (EN)
                       and then Kurt.Layout.Has_Variant (EN, VN)
                     then
                        for K in 1 .. Natural (S.L_Refut_Pat.Bindings.Length)
                        loop
                           Check_Dup_In_Scope
                             (S.L_Refut_Pat.Bindings.Element (K));
                           Scope.Append
                             ((Name => S.L_Refut_Pat.Bindings.Element (K),
                               Ty   => Pat_Field_Ty (S.L_Refut_Pat, CT, VN, K), others => <>));
                        end loop;
                     end if;
                  end;
                  return;
               end if;
               declare
                  Ty : Type_Access := S.L_Ty;
               begin
                  --  §4.6: `[T]` cannot be a binding type (use `&[T]`).
                  if Is_Unsized_Value (S.L_Ty) then
                     Error ("`[T]`/`dyn Trait` cannot be a binding type "
                            & "(use a reference) (spec 4.6/9.5)");
                  end if;
                  if S.L_Init /= null and then S.L_Init.Kind = E_Uninit then
                     --  §6.1.8: `let/mut x: T = uninit;` — no value to infer
                     --  from, so the type annotation is required.
                     Check_Uninit (Ty);
                     S.L_Init.Sem_Ty := Ty;
                  elsif S.L_Init /= null then
                     declare
                        IT : constant Type_Access := Infer (S.L_Init, Ty);
                     begin
                        if Ty = null then
                           Ty := IT;
                        --  §4.6 `let r: &[T] = &arr;` slice coercion.
                        elsif Is_Slice_Ref (Ty) and then Is_Ref (IT)
                          and then IT.Target /= null
                          and then IT.Target.Kind = T_Array
                          and then IT.Target.Len > 0
                          and then Same_Type (Ty.Target.Elem,
                                              IT.Target.Elem)
                        then
                           declare
                              SC : constant Expr_Access :=
                                new Expr_Node (Kind => E_Slice_Cast);
                           begin
                              SC.SC_Inner := S.L_Init;
                              SC.SC_Len   := IT.Target.Len;
                              SC.Sem_Ty   := Ty;
                              S.L_Init    := SC;
                           end;
                        --  §2.9.1 the initialiser's type must be assignable to
                        --  the declared type. `&T → &dyn Trait` coercion is
                        --  resolved downstream, so it is exempted here.
                        elsif IT /= null
                          and then not Assignable (Ty, IT)
                          and then not (Is_Dyn_Ref (Ty) and then Is_Ref (IT))
                          and then not Is_Generic_Param_Ty (IT)
                          and then not Is_Generic_Param_Ty (Ty)
                        then
                           --  In a generic template, associated-item types are
                           --  not yet concrete; the assignability is re-checked
                           --  at each monomorphised instance.
                           Error ("initialiser of type '" & Image (IT)
                                  & "' is not assignable to declared type '"
                                  & Image (Ty) & "' (spec 2.9.1)");
                        end if;
                     end;
                  end if;
                  if not S.L_Tuple_Names.Is_Empty then
                     --  §4.7 destructuring: each name binds a tuple field.
                     if Ty = null or else Ty.Kind /= T_Tuple then
                        Error ("destructuring let requires a tuple value, "
                               & "got '" & Image (Ty) & "'");
                     elsif Natural (S.L_Tuple_Names.Length)
                             /= Natural (Ty.Elems.Length)
                     then
                        Error ("destructuring pattern has"
                               & S.L_Tuple_Names.Length'Image
                               & " names but tuple '" & Image (Ty) & "' has"
                               & Ty.Elems.Length'Image & " fields");
                     else
                        for I in S.L_Tuple_Names.First_Index ..
                                 S.L_Tuple_Names.Last_Index
                        loop
                           Check_Dup_In_Scope (S.L_Tuple_Names.Element (I));
                           Scope.Append
                             ((Name => S.L_Tuple_Names.Element (I),
                               Ty   => Kurt.Layout.Tuple_Field_Type
                                         (Ty, I - S.L_Tuple_Names.First_Index),
                               Is_Mut => S.Kind = S_Mut));
                        end loop;
                     end if;
                  else
                     if Ty = null then
                        Error ("binding '" & SU.To_String (S.L_Name)
                               & "' needs a type annotation or initialiser");
                     end if;
                     Check_Dup_In_Scope (S.L_Name);
                     --  §2.2.1: `let` is single-assignment (immutable); `mut`
                     --  is mutable.
                     Scope.Append
                       ((Name => S.L_Name, Ty => Ty,
                         Is_Mut => S.Kind = S_Mut));
                     Register_Borrow (SU.To_String (S.L_Name), S.L_Init);
                     --  §8.8.2: initialising from a `destruct`-typed binding
                     --  transfers it (the source is invalidated).
                     Maybe_Move (S.L_Init);
                  end if;
               end;

            when S_Assign =>
               --  §6.7.1/§6.7.2 the left side of an assignment (plain or
               --  compound) shall be a place expression: a binding, a field
               --  access, or a dereference. A value expression here would
               --  otherwise reach an unsupported lvalue path in codegen.
               if S.Asn_Lhs.Kind not in E_Path | E_Field | E_Deref then
                  Error ("the left side of an assignment shall be a place "
                         & "expression (a binding, field access, or "
                         & "dereference) (spec 6.7.1)");
               end if;
               if S.Asn_Rhs.Kind = E_Uninit then
                  --  §6.1.8: `place = uninit;` — establishes the contained
                  --  state without storing a value.
                  declare
                     LT : constant Type_Access := Infer (S.Asn_Lhs, null);
                  begin
                     Check_Uninit (LT);
                     S.Asn_Rhs.Sem_Ty := LT;
                  end;
                  return;
               end if;
               declare
                  LT : constant Type_Access := Infer (S.Asn_Lhs, null);
                  RT : constant Type_Access := Infer (S.Asn_Rhs, LT);
               begin
                  --  §8.3: a store through an exclusive reference asserts
                  --  exclusivity; flag a provable alias.
                  Register_Store (S.Asn_Lhs);
                  --  §8.8.2: assigning a `destruct`-typed binding transfers it.
                  Maybe_Move (S.Asn_Rhs);
                  if not Assignable (LT, RT) then
                     Error ("assignment type mismatch: place is '"
                            & Image (LT) & "' but value is '"
                            & Image (RT) & "'");
                  end if;
                  --  §5.4: a plain `static` is immutable; stores require
                  --  `static mut`.
                  if S.Asn_Lhs.Kind = E_Path
                    and then Natural (S.Asn_Lhs.Segments.Length) = 1
                  then
                     declare
                        Name : constant String := SU.To_String
                          (S.Asn_Lhs.Segments.Last_Element);
                        M       : Boolean;
                        Mutable : Boolean;
                        Is_Local : Boolean;
                     begin
                        Mutable := Lookup_Scope_Mut (Name, Is_Local);
                        if Is_Local then
                           --  §2.2.1/§5.1: a `let` binding (and an immutable
                           --  parameter) is single-assignment.
                           if not Mutable then
                              Error ("assignment to immutable binding '"
                                     & Name & "' -- declare it `mut` "
                                     & "(spec 2.2.1)");
                           end if;
                        elsif Find_Static_Decl (Name, M) and then not M then
                           Error ("assignment to immutable static '"
                                  & Name & "' -- declare it `static "
                                  & "mut` (spec 5.4)");
                        else
                           --  §5.3: a `const` is a translation-time value and
                           --  cannot be assigned to.
                           for CI in U.Consts.First_Index ..
                                     U.Consts.Last_Index loop
                              if SU.To_String (U.Consts.Element (CI).Name)
                                   = Name
                              then
                                 Error ("assignment to `const` '" & Name
                                        & "' (spec 5.3)");
                              end if;
                           end loop;
                        end if;
                     end;
                  end if;
                  --  §8.1.2: a store through a reference requires store
                  --  permission — `$T`, or a `mut`/`atomic`/`guard`
                  --  modifier. `&T` and `&raw T` are load-only.
                  if S.Asn_Lhs.Kind = E_Deref then
                     declare
                        IT : constant Type_Access :=
                          S.Asn_Lhs.D_Inner.Sem_Ty;
                     begin
                        if Is_Ref (IT)
                          and then IT.Sigil /= R_Excl
                          and then IT.R_Store = RS_None
                        then
                           Error ("store through load-only reference '"
                                  & Image (IT) & "' -- a store requires "
                                  & "'$', 'mut', 'atomic' or 'guard' "
                                  & "(spec 8.1.2)");
                        end if;
                     end;
                     --  §8.5.2 `mut` field requirement for atomic stores: a
                     --  store (including RMW) through an `&atomic`/`&guard`/
                     --  `&mut`/`$` reference derived from a `.field` access
                     --  in a non-exclusive context shall not appear unless
                     --  the field carries the `mut` field modifier (§5.5.1).
                     --  Loads through such a reference are unrestricted, so
                     --  this is enforced at the store, not at reference
                     --  creation. Waived when the containing value is reached
                     --  through an exclusive (`$`) or `&mut` path, or a `mut`
                     --  binding of the containing value.
                     declare
                        Ref : constant Expr_Access := S.Asn_Lhs.D_Inner;
                     begin
                        if Ref.Kind = E_Ref
                          and then Ref.Rf_Sigil /= R_Raw
                          and then Ref.Rf_Place.Kind = E_Field
                          and then (Ref.Rf_Store in RS_Atomic | RS_Guard
                                                   | RS_Mut
                                    or else Ref.Rf_Sigil = R_Excl)
                        then
                           declare
                              Recv : constant Expr_Access :=
                                Ref.Rf_Place.F_Recv;
                              RT   : constant Type_Access :=
                                Infer (Recv, null);
                              RTD  : constant Type_Access :=
                                (if Is_Ref (RT) then RT.Target else RT);
                              FN   : constant String :=
                                SU.To_String (Ref.Rf_Place.F_Name);
                              Exclusive_Ctx : Boolean := False;
                           begin
                              if Is_Ref (RT)
                                and then (RT.Sigil = R_Excl
                                          or else RT.R_Store = RS_Mut)
                              then
                                 Exclusive_Ctx := True;
                              elsif not Is_Ref (RT)
                                and then Recv.Kind = E_Path
                                and then Natural (Recv.Segments.Length) = 1
                              then
                                 declare
                                    Found : Boolean;
                                    Mut   : constant Boolean :=
                                      Lookup_Scope_Mut
                                        (SU.To_String
                                           (Recv.Segments.Last_Element),
                                         Found);
                                 begin
                                    Exclusive_Ctx := Found and then Mut;
                                 end;
                              end if;
                              if not Exclusive_Ctx
                                and then RTD /= null
                                and then RTD.Kind = T_Named
                                and then Kurt.Layout.Is_Struct
                                           (SU.To_String (RTD.Name))
                                and then not Kurt.Layout.Field_Is_Mut
                                           (SU.To_String (RTD.Name), FN)
                              then
                                 Error ("atomic/exclusive store to non-`mut` "
                                        & "field '" & FN & "' requires the "
                                        & "field be declared `mut` "
                                        & "(spec 8.5.2)");
                              end if;
                           end;
                        end if;
                     end;
                  end if;
               end;

            when S_Fence =>
               null;   --  §8.5.3: fences carry no static obligations here

            when S_While =>
               declare
                  Has_Label : constant Boolean := SU.Length (S.W_Label) > 0;
                  Saved     : Natural := 0;
                  Bound_Let : Boolean := False;
               begin
                  if S.W_Is_Let then
                     --  §7.5.1 `while let Enum::Variant { binds } = e { }`:
                     --  the body sees the positional payload bindings.
                     declare
                        CT : constant Type_Access := Infer (S.W_Cond, null);
                        EN : constant String :=
                          (if CT /= null and then CT.Kind = T_Named
                           then SU.To_String (CT.Name) else "");
                        VN : constant String :=
                          SU.To_String (S.W_Let_Pat.Path.Last_Element);
                     begin
                        if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                           Error ("`while let` requires an enum value; got '"
                                  & Image (CT) & "' (spec 7.5.1)");
                        elsif not Kurt.Layout.Has_Variant (EN, VN) then
                           Error ("enum '" & EN & "' has no variant '" & VN
                                  & "' (spec 7.5.1)");
                        else
                           Saved := Natural (Scope.Length);
                           Bound_Let := True;
                           for K in 1 .. Natural (S.W_Let_Pat.Bindings.Length)
                           loop
                              Scope.Append
                                ((Name => S.W_Let_Pat.Bindings.Element (K),
                                  Ty   => Pat_Field_Ty (S.W_Let_Pat, CT, VN, K), others => <>));
                           end loop;
                        end if;
                     end;
                  elsif S.W_Is_Contract then
                     --  §7.5.1 `while cond -> v { }`: cond is a contract
                     --  value; v binds the success payload in the body.
                     declare
                        CT : constant Type_Access := Infer (S.W_Cond, null);
                        EN : constant String :=
                          (if CT /= null and then CT.Kind = T_Named
                           then SU.To_String (CT.Name) else "");
                     begin
                        if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
                        then
                           Error ("`while ->` requires a contract value; got '"
                                  & Image (CT) & "' (spec 7.5.1)");
                        elsif S.W_Cond.Kind /= E_Path
                          or else Natural (S.W_Cond.Segments.Length) /= 1
                        then
                           --  §7.5.1 bootstrap: the `->` scrutinee must be a
                           --  binding re-read each iteration; a call/temporary
                           --  is not yet materialised.
                           Error ("the `while ... -> v` scrutinee must currently "
                                  & "be a binding reassigned in the body "
                                  & "(bootstrap)");
                        else
                           Saved := Natural (Scope.Length);
                           Bound_Let := True;
                           Scope.Append
                             ((Name => S.W_Succ_Bind,
                               Ty   => Kurt.Layout.Variant_Field_Type
                                         (CT,
                                          Kurt.Layout.Contract_Success_Variant
                                            (EN), 1), others => <>));
                        end if;
                     end;
                  else
                     declare
                        CT : constant Type_Access :=
                          Infer (S.W_Cond, Mk_Named ("bool"));
                        pragma Unreferenced (CT);
                     begin
                        null;
                     end;
                  end if;
                  In_Loop := In_Loop + 1;
                  if Has_Label then
                     Label_Stack.Append (S.W_Label);   --  §7.9 in scope
                  end if;
                  Check_Block (S.W_Body);
                  Check_Block (S.W_Then);   --  §7.5.3 step block
                  if Has_Label then
                     Label_Stack.Delete_Last;
                  end if;
                  In_Loop := In_Loop - 1;
                  if Bound_Let then
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                  end if;
               end;

            when S_If =>
               if S.SI_Is_Let then
                  --  §7.3.3 `if let Enum::Variant { binds } = e { } else { }`.
                  declare
                     CT : constant Type_Access := Infer (S.SI_Cond, null);
                     EN : constant String :=
                       (if CT /= null and then CT.Kind = T_Named
                        then SU.To_String (CT.Name) else "");
                     VN : constant String :=
                       SU.To_String (S.SI_Let_Pat.Path.Last_Element);
                     Saved : Natural;
                  begin
                     if EN = "" or else not Kurt.Layout.Is_Enum (EN) then
                        Error ("`if let` requires an enum value; got '"
                               & Image (CT) & "' (spec 7.3.3)");
                        Check_Block (S.SI_Then);
                        Check_Block (S.SI_Else);
                     elsif not Kurt.Layout.Has_Variant (EN, VN) then
                        Error ("enum '" & EN & "' has no variant '" & VN
                               & "' (spec 7.3.3)");
                        Check_Block (S.SI_Then);
                        Check_Block (S.SI_Else);
                     else
                        --  then-block sees the positional payload bindings.
                        Saved := Natural (Scope.Length);
                        for K in 1 .. Natural (S.SI_Let_Pat.Bindings.Length)
                        loop
                           Scope.Append
                             ((Name => S.SI_Let_Pat.Bindings.Element (K),
                               Ty   => Pat_Field_Ty (S.SI_Let_Pat, CT, VN, K), others => <>));
                        end loop;
                        Check_Block (S.SI_Then);
                        while Natural (Scope.Length) > Saved loop
                           Scope.Delete_Last;
                        end loop;
                        --  else-block binds nothing (§7.3.3).
                        Check_Block (S.SI_Else);
                     end if;
                  end;
               elsif S.SI_Is_Contract then
                  --  §7 contract-binding `if e -> v | err`.
                  declare
                     CT : constant Type_Access := Infer (S.SI_Cond, null);
                     EN : constant String :=
                       (if CT /= null and then CT.Kind = T_Named
                        then SU.To_String (CT.Name) else "");
                     Saved : Natural;
                  begin
                     if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
                     then
                        Error ("the `->` form requires a contract value; "
                               & "got '" & Image (CT) & "'");
                        Check_Block (S.SI_Then);
                        Check_Block (S.SI_Else);
                     elsif S.SI_Cond.Kind /= E_Path
                       or else Natural (S.SI_Cond.Segments.Length) /= 1
                     then
                        --  §7.3 bootstrap: the `->` scrutinee must be a
                        --  binding (a place) so the payload can be aliased
                        --  in place. A call/temporary is not yet materialised.
                        Error ("the `if ... -> v` scrutinee must currently be a "
                               & "binding; bind the value first (bootstrap)");
                        Check_Block (S.SI_Then);
                        Check_Block (S.SI_Else);
                     else
                        --  then-block sees the success payload.
                        Saved := Natural (Scope.Length);
                        Scope.Append
                          ((Name => S.SI_Succ_Bind,
                            Ty   => Kurt.Layout.Variant_Field_Type
                                      (CT,
                                       Kurt.Layout.Contract_Success_Variant
                                         (EN), 1), others => <>));
                        Check_Block (S.SI_Then);
                        while Natural (Scope.Length) > Saved loop
                           Scope.Delete_Last;
                        end loop;
                        --  else-block sees the failure payload (if bound).
                        Saved := Natural (Scope.Length);
                        if SU.Length (S.SI_Fail_Bind) > 0 then
                           Scope.Append
                             ((Name => S.SI_Fail_Bind,
                               Ty   => Kurt.Layout.Variant_Field_Type
                                         (CT,
                                          Kurt.Layout.Contract_Fail_Variant
                                            (EN), 1), others => <>));
                        end if;
                        Check_Block (S.SI_Else);
                        while Natural (Scope.Length) > Saved loop
                           Scope.Delete_Last;
                        end loop;
                     end if;
                  end;
               else
                  declare
                     CT : constant Type_Access :=
                       Infer (S.SI_Cond, Mk_Named ("bool"));
                     pragma Unreferenced (CT);
                  begin
                     Check_Block (S.SI_Then);
                     Check_Block (S.SI_Else);
                  end;
               end if;

            when S_Airside_Block =>
               In_Airside := In_Airside + 1;
               Check_Block (S.A_Stmts);
               In_Airside := In_Airside - 1;

            when S_Extract =>
               --  §7: `let v <- e else err { ... }`. e is a contract value;
               --  v binds the success payload for the rest of the block,
               --  err binds the failure payload inside the else block.
               declare
                  ET : constant Type_Access := Infer (S.X_Expr, null);
                  EN : constant String :=
                    (if ET /= null and then ET.Kind = T_Named
                     then SU.To_String (ET.Name) else "");
                  Saved : Natural;
               begin
                  if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
                  then
                     Error ("`<-` requires a contract value; got '"
                            & Image (ET) & "'");
                     Check_Block (S.X_Else);
                  else
                     Saved := Natural (Scope.Length);
                     if SU.Length (S.X_Err) > 0 then
                        Scope.Append
                          ((Name => S.X_Err,
                            Ty   => Kurt.Layout.Variant_Field_Type
                                      (ET,
                                       Kurt.Layout.Contract_Fail_Variant (EN),
                                       1), others => <>));
                     end if;
                     Check_Block (S.X_Else);
                     while Natural (Scope.Length) > Saved loop
                        Scope.Delete_Last;
                     end loop;
                     --  §7.2.3: the `else` block shall either diverge or
                     --  yield a fallback value via `express`; otherwise
                     --  the extracted binding would continue uninitialized
                     --  on the failure path.
                     if not Stmts_Diverge (S.X_Else) then
                        Error ("the `else` of `<-` must diverge (return/"
                               & "break/continue/@trap) or yield a value "
                               & "via `express` (spec 7.2.3)");
                     end if;
                     declare
                        Succ_Ty : constant Type_Access :=
                          Kurt.Layout.Variant_Field_Type
                            (ET, Kurt.Layout.Contract_Success_Variant (EN), 1);
                     begin
                        if S.X_Is_Place then
                           --  §7.2.3 copy the success payload into the place,
                           --  which shall be an existing `mut` binding.
                           declare
                              PN : constant String := SU.To_String (S.X_Bind);
                              PT : constant Type_Access := Lookup_Scope (PN);
                              Is_Local : Boolean;
                              Mutable  : constant Boolean :=
                                Lookup_Scope_Mut (PN, Is_Local);
                           begin
                              if PT = null then
                                 Error ("extract-assignment target '" & PN
                                        & "' is not a binding");
                              elsif not Mutable then
                                 Error ("extract-assignment target '" & PN
                                        & "' must be `mut` (spec 7.2.3)");
                              elsif not Assignable (PT, Succ_Ty) then
                                 Error ("extract-assignment type mismatch: "
                                        & "place is '" & Image (PT)
                                        & "' but success payload is '"
                                        & Image (Succ_Ty) & "'");
                              end if;
                           end;
                        else
                           --  Success binding stays in scope for the rest.
                           Scope.Append
                             ((Name => S.X_Bind, Ty => Succ_Ty, others => <>));
                        end if;
                     end;
                  end if;
               end;

            when S_Break =>
               --  §7.7/§7.9: break may carry a value and/or a target label.
               if In_Loop = 0 then
                  Error ("`break` shall appear only within a loop (spec 7.7)");
               end if;
               Check_Loop_Label (S.Brk_Label);
               if S.Brk_Val /= null then
                  declare
                     T : constant Type_Access := Infer (S.Brk_Val, null);
                     pragma Unreferenced (T);
                  begin null; end;
               end if;
            when S_Continue =>
               --  §7.9: optional target label.
               if In_Loop = 0 then
                  Error ("`continue` shall appear only within a loop "
                         & "(spec 7.7)");
               end if;
               Check_Loop_Label (S.Cont_Label);
            when S_Express =>
               --  §7.8: the expressed value is typed against the innermost
               --  enclosing block expression's expected type (steering
               --  literals like a `let` annotation); outside a block
               --  expression it is inferred freely.
               declare
                  T : constant Type_Access :=
                    Infer (S.Xp_Val, Express_Expected);
                  pragma Unreferenced (T);
               begin null; end;

            when S_Trap =>
               --  §7.10/§7.11: `@trap;` is a diverging expression; it
               --  produces no value and imposes no type obligation.
               null;
            when S_Asm =>
               --  §6.11 inline assembly is opaque to the type system, but its
               --  `in`/`io` operand expressions are ordinary Kurt expressions
               --  (inferred so codegen has their types) and each `out`/`io`
               --  target shall be an existing binding (a place).
               --  §6.11: `asm` is permitted only inside an airside region.
               if In_Airside = 0 then
                  Error ("inline `asm` is permitted only inside an `airside` "
                         & "block or `airside fn` body (spec 6.11)");
               end if;
               for I in S.Asm_In_Exprs.First_Index ..
                        S.Asm_In_Exprs.Last_Index loop
                  declare
                     T : constant Type_Access :=
                       Infer (S.Asm_In_Exprs.Element (I), null);
                     pragma Unreferenced (T);
                  begin null; end;
               end loop;
               for I in S.Asm_Out_Names.First_Index ..
                        S.Asm_Out_Names.Last_Index loop
                  if Lookup_Scope
                       (SU.To_String (S.Asm_Out_Names.Element (I))) = null
                  then
                     Error ("asm `out` target '"
                            & SU.To_String (S.Asm_Out_Names.Element (I))
                            & "' is not a binding");
                  end if;
               end loop;
               --  §6.11: overlap between a (resource-mode) operand target and
               --  a `clobber` entry, and duplicate resource targets, shall not
               --  appear. Logical/positional targets (`'…`) get impl-chosen
               --  registers and cannot textually overlap a named clobber.
               declare
                  function In_Clobbers (R : String) return Boolean is
                  begin
                     for K in S.Asm_Clobbers.First_Index ..
                              S.Asm_Clobbers.Last_Index loop
                        if SU.To_String (S.Asm_Clobbers.Element (K)) = R then
                           return True;
                        end if;
                     end loop;
                     return False;
                  end In_Clobbers;

                  procedure Check_Target (R : String) is
                  begin
                     if R'Length > 0 and then R (R'First) /= '''
                       and then In_Clobbers (R)
                     then
                        Error ("asm operand target '" & R & "' overlaps a "
                               & "`clobber` entry (spec 6.11)");
                     end if;
                  end Check_Target;
               begin
                  for I in S.Asm_In_Regs.First_Index ..
                           S.Asm_In_Regs.Last_Index loop
                     Check_Target (SU.To_String (S.Asm_In_Regs.Element (I)));
                  end loop;
                  for I in S.Asm_Out_Regs.First_Index ..
                           S.Asm_Out_Regs.Last_Index loop
                     Check_Target (SU.To_String (S.Asm_Out_Regs.Element (I)));
                  end loop;
               end;
         end case;
      end Check_Stmt;

   begin
      --  §5.17: within the top-level scope a name shall be declared at most
      --  once, uniformly across fn / struct / enum / trait / const / static.
      --  Names containing '$' are compiler-generated (monomorphised
      --  instances, lowered `Type$method` impl items) and are unique by
      --  construction, so they are excluded to avoid false positives.
      declare
         Seen : Path_Segments.Vector;

         function Is_Generated (Name : String) return Boolean is
         begin
            for I in Name'Range loop
               if Name (I) = '$' then
                  return True;
               end if;
            end loop;
            return False;
         end Is_Generated;

         procedure Note (Name : String; Kind : String) is
         begin
            if Is_Generated (Name) then
               return;
            end if;
            for I in Seen.First_Index .. Seen.Last_Index loop
               if SU.To_String (Seen.Element (I)) = Name then
                  Error ("duplicate declaration of '" & Name
                         & "' (" & Kind & "): a name shall be declared at "
                         & "most once in a scope (spec 5.17)");
                  return;
               end if;
            end loop;
            Seen.Append (SU.To_Unbounded_String (Name));
         end Note;
      begin
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            Note (SU.To_String (U.Structs.Element (I).Name), "struct");
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            Note (SU.To_String (U.Enums.Element (I).Name), "enum");
         end loop;
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            Note (SU.To_String (U.Traits.Element (I).Name), "trait");
         end loop;
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            Note (SU.To_String (U.Consts.Element (I).Name), "const");
         end loop;
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            Note (SU.To_String (U.Statics.Element (I).Name), "static");
         end loop;
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Note (SU.To_String (U.Fns.Element (I).Header.Name), "fn");
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Note (SU.To_String (U.Gen_Fns.Element (I).Header.Name), "fn");
         end loop;
      end;

      --  §5.5 field-name uniqueness within a named composite (the anonymous
      --  `?` padding field is exempt) and §5.1 parameter-name uniqueness.
      declare
         procedure Check_Unique_Fields
           (Owner : String; Fields : Struct_Field_Vectors.Vector) is
         begin
            for I in Fields.First_Index .. Fields.Last_Index loop
               declare
                  N : constant String :=
                    SU.To_String (Fields.Element (I).Name);
               begin
                  if N /= "" and then N /= "?" then
                     for J in Fields.First_Index .. I - 1 loop
                        if SU.To_String (Fields.Element (J).Name) = N then
                           Error ("duplicate field '" & N & "' in " & Owner
                                  & " (spec 5.5)");
                        end if;
                     end loop;
                  end if;
               end;
            end loop;
         end Check_Unique_Fields;

         --  §5.9 generic type-parameter names shall be distinct.
         procedure Check_Unique_Generics (H : Fn_Header) is
            G : Generic_Param_Vectors.Vector renames H.Generic_Params;
         begin
            for I in G.First_Index .. G.Last_Index loop
               for J in G.First_Index .. I - 1 loop
                  if SU.To_String (G.Element (J).Name)
                       = SU.To_String (G.Element (I).Name)
                  then
                     Error ("duplicate generic parameter '"
                            & SU.To_String (G.Element (I).Name)
                            & "' in '" & SU.To_String (H.Name)
                            & "' (spec 5.9)");
                  end if;
               end loop;
            end loop;
         end Check_Unique_Generics;

         procedure Check_Unique_Params (H : Fn_Header) is
         begin
            Check_Unique_Generics (H);
            for I in H.Params.First_Index .. H.Params.Last_Index loop
               declare
                  N : constant String :=
                    SU.To_String (H.Params.Element (I).Name);
               begin
                  if N /= "" then
                     for J in H.Params.First_Index .. I - 1 loop
                        if SU.To_String (H.Params.Element (J).Name) = N then
                           Error ("duplicate parameter '" & N
                                  & "' in subroutine '"
                                  & SU.To_String (H.Name) & "' (spec 5.1)");
                        end if;
                     end loop;
                  end if;
               end;
            end loop;
         end Check_Unique_Params;
      begin
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            Check_Unique_Fields
              ("struct '" & SU.To_String (U.Structs.Element (I).Name) & "'",
               U.Structs.Element (I).Fields);
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            declare
               EnV : Enum_Variant_Vectors.Vector renames
                 U.Enums.Element (I).Variants;
               EnN : constant String :=
                 SU.To_String (U.Enums.Element (I).Name);
               Wilds : Natural := 0;
            begin
               for V in EnV.First_Index .. EnV.Last_Index loop
                  Check_Unique_Fields
                    ("variant '" & SU.To_String (EnV.Element (V).Name) & "'",
                     EnV.Element (V).Payload);
                  --  §5.7 at most one `#wild#` variant per enum.
                  if EnV.Element (V).Is_Wild then
                     Wilds := Wilds + 1;
                     if Wilds = 2 then
                        Error ("enum '" & EnN & "' declares more than one "
                               & "`#wild#` variant (spec 5.7)");
                     end if;
                  end if;
                  --  §5.7 variant-name uniqueness within the enum.
                  for W in EnV.First_Index .. V - 1 loop
                     if SU.To_String (EnV.Element (W).Name)
                          = SU.To_String (EnV.Element (V).Name)
                     then
                        Error ("duplicate variant '"
                               & SU.To_String (EnV.Element (V).Name)
                               & "' in enum '" & EnN & "' (spec 5.7)");
                     end if;
                  end loop;
                  --  §5.7 discriminant collision (explicit values and
                  --  `#wild#(V)` canonical values must be distinct).
                  for W in EnV.First_Index .. V - 1 loop
                     if EnV.Element (W).Value = EnV.Element (V).Value then
                        Error ("discriminant value"
                               & Long_Long_Integer'Image (EnV.Element (V).Value)
                               & " of variant '"
                               & SU.To_String (EnV.Element (V).Name)
                               & "' collides with variant '"
                               & SU.To_String (EnV.Element (W).Name)
                               & "' in enum '" & EnN & "' (spec 5.7)");
                     end if;
                  end loop;
               end loop;
            end;
         end loop;
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Check_Unique_Params (U.Fns.Element (I).Header);
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Check_Unique_Params (U.Gen_Fns.Element (I).Header);
         end loop;
      end;

      --  Phase 1: collect signatures (fns and @dyn prototypes).
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            Fn : constant Fn_Decl := U.Fns.Element (I);
         begin
            Sigs.Append
              ((Name        => Fn.Header.Name,
                Params      => Fn.Header.Params,
                Ret         => Fn.Header.Return_Type,
                Is_Variadic => Fn.Header.Is_Variadic,
                Is_Never    => Fn.Header.Is_Never));
         end;
      end loop;

      for I in U.Dyns.First_Index .. U.Dyns.Last_Index loop
         declare
            D : constant Dyn_Decl := U.Dyns.Element (I);
         begin
            for J in D.Items.First_Index .. D.Items.Last_Index loop
               declare
                  P : constant Fn_Proto := D.Items.Element (J);
               begin
                  Sigs.Append
                    ((Name        => P.Name,
                      Params      => P.Params,
                      Ret         => P.Return_Type,
                      Is_Variadic => P.Is_Variadic,
                      Is_Never    => P.Is_Never));
                  Dyn_Fn_Names.Append (P.Name);   --  §10.4 airside-only
               end;
            end loop;
         end;
      end loop;

      --  §4.11.3: validate enum discriminant declarations. `with
      --  discrim(T)` shall name an integer type and every declared
      --  value shall fit in T; violations are translation failures.
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            D  : constant Kurt.Parser.Enum_Decl := U.Enums.Element (I);
            EN : constant String := SU.To_String (D.Name);
         begin
            if D.Discrim_Ty /= null then
               if Is_Void_Type (D.Discrim_Ty) then
                  declare
                     Has_Wild_Canon : Boolean := False;
                  begin
                     for J in D.Variants.First_Index .. D.Variants.Last_Index loop
                        if D.Variants.Element (J).Wild_Canon then
                           Has_Wild_Canon := True;
                        end if;
                     end loop;
                     if Natural (D.Variants.Length) > 1 or else Has_Wild_Canon then
                        Error ("enum '" & EN & "': `with discrim(void)` requires "
                               & "at most one variant and no #wild#(V) canonical value (spec 4.11.3)");
                     end if;
                  end;
               elsif not Is_Integer_Type (D.Discrim_Ty) then
                  Error ("enum '" & EN & "': `with discrim(T)` requires "
                         & "an integer type or void, got '"
                         & Image (D.Discrim_Ty) & "' (spec 4.11.3)");
               else
                  declare
                     Sz  : constant Natural :=
                       Kurt.Layout.Size_Of (D.Discrim_Ty);
                     Sgn : constant Boolean :=
                       Kurt.Layout.Enum_Disc_Signed (EN);
                     Lo  : Long_Long_Integer := 0;
                     Hi  : Long_Long_Integer := Long_Long_Integer'Last;
                  begin
                     if Sgn and then Sz < 8 then
                        Lo := -(2 ** (8 * Sz - 1));
                        Hi := 2 ** (8 * Sz - 1) - 1;
                     elsif not Sgn and then Sz < 8 then
                        Lo := 0;
                        Hi := 2 ** (8 * Sz) - 1;
                     elsif not Sgn then
                        Lo := 0;   --  ui8: any representable literal fits
                     end if;
                     for J in D.Variants.First_Index ..
                              D.Variants.Last_Index
                     loop
                        declare
                           V : constant Long_Long_Integer :=
                             D.Variants.Element (J).Value;
                        begin
                           if V < Lo or else V > Hi then
                              Error ("enum '" & EN & "': discriminant"
                                     & V'Image & " does not fit in `"
                                     & Image (D.Discrim_Ty)
                                     & "` (spec 4.11.3)");
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            end if;

            --  §5.7 at most one `#wild#` variant per enum. (Variant-name
            --  uniqueness and discriminant-collision are enforced during
            --  discriminant resolution.) A pure rejection of an ill-formed
            --  declaration; never affects a valid enum.
            declare
               Wild_Count : Natural := 0;
            begin
               for J in D.Variants.First_Index .. D.Variants.Last_Index loop
                  if D.Variants.Element (J).Is_Wild then
                     Wild_Count := Wild_Count + 1;
                  end if;
               end loop;
               if Wild_Count > 1 then
                  Error ("enum '" & EN & "' declares" & Wild_Count'Image
                         & " `#wild#` variants; at most one is permitted "
                         & "(spec 5.7)");
               end if;
            end;
         end;
      end loop;

      --  §4.11.5: `align(N)` requires N to be a power of two.
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            D : constant Kurt.Parser.Struct_Decl := U.Structs.Element (I);
            M : Natural := D.Align_N;
         begin
            while M > 1 and then M mod 2 = 0 loop
               M := M / 2;
            end loop;
            if D.Align_N > 0 and then M /= 1 then
               Error ("struct '" & SU.To_String (D.Name)
                      & "': align(" & Natural'Image (D.Align_N)
                      & " ) shall be a power of two (spec 4.11.5)");
            end if;

            --  §5.5.3: type-check each default-value expression against its
            --  field type (and give it a Sem_Ty for codegen to lower).
            for J in D.Fields.First_Index .. D.Fields.Last_Index loop
               declare
                  Fld : constant Struct_Field := D.Fields.Element (J);
               begin
                  if Fld.Default /= null then
                     declare
                        DT : constant Type_Access :=
                          Infer (Fld.Default, Fld.Ty);
                     begin
                        if Fld.Ty /= null and then not Assignable (Fld.Ty, DT)
                        then
                           Error ("struct '" & SU.To_String (D.Name)
                                  & "': default for field '"
                                  & SU.To_String (Fld.Name) & "' is '"
                                  & Image (DT) & "' but the field is '"
                                  & Image (Fld.Ty) & "' (spec 5.5.3)");
                        end if;
                     end;
                  end if;
               end;
            end loop;
         end;
      end loop;

      --  §5.3 / §5.4: validate const and static declarations. Both
      --  initializers shall be translation-time evaluable; the bootstrap
      --  folds const values at use sites and emits static objects as
      --  data-section constants, so the accepted forms are restricted
      --  accordingly.
      declare
         --  Conservative xlatime-foldability (§6.10.2): literals, layout
         --  intrinsics, other consts, and pure operators over them.
         function Is_Xlatime_Foldable (E : Expr_Access) return Boolean is
         begin
            if E = null then
               return False;
            end if;
            case E.Kind is
               when E_Int_Lit | E_Float_Lit | E_Bool_Lit
                  | E_Type_Intrinsic =>
                  return True;
               when E_Unary =>
                  return Is_Xlatime_Foldable (E.U_Operand);
               when E_Binary =>
                  return Is_Xlatime_Foldable (E.B_Lhs)
                    and then Is_Xlatime_Foldable (E.B_Rhs);
               when E_Cast =>
                  return Is_Xlatime_Foldable (E.Cast_Inner);
               when E_Path =>
                  if Natural (E.Segments.Length) = 1 then
                     for I in U.Consts.First_Index ..
                              U.Consts.Last_Index
                     loop
                        if SU."=" (U.Consts.Element (I).Name,
                                   E.Segments.Last_Element)
                        then
                           return True;
                        end if;
                     end loop;
                  end if;
                  return False;
               when others =>
                  return False;
            end case;
         end Is_Xlatime_Foldable;

         --  A static initializer must fold to one scalar data word: a
         --  literal or a negated literal.
         function Is_Static_Init (E : Expr_Access) return Boolean is
           (E /= null
            and then (E.Kind in E_Int_Lit | E_Float_Lit | E_Bool_Lit
                      or else (E.Kind = E_Unary
                               and then E.U_Operand /= null
                               and then E.U_Operand.Kind in
                                 E_Int_Lit | E_Float_Lit)));
      begin
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            declare
               D  : constant Kurt.Parser.Const_Decl := U.Consts.Element (I);
               IT : constant Type_Access := Infer (D.Init, D.Ty);
            begin
               if not Assignable (D.Ty, IT) then
                  Error ("const '" & SU.To_String (D.Name)
                         & "': initializer type '" & Image (IT)
                         & "' does not match '" & Image (D.Ty) & "'");
               elsif not Is_Xlatime_Foldable (D.Init) then
                  Error ("const '" & SU.To_String (D.Name)
                         & "': initializer is not evaluable at "
                         & "translation time (spec 5.3, bootstrap "
                         & "subset: literals, type intrinsics, consts, "
                         & "and pure operators)");
               end if;
            end;
         end loop;

         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            declare
               D  : constant Kurt.Parser.Static_Decl :=
                 U.Statics.Element (I);
               IT : constant Type_Access := Infer (D.Init, D.Ty);
            begin
               if not (Is_Integer_Type (D.Ty)
                       or else Is_Float_Type (D.Ty)
                       or else (D.Ty.Kind = T_Named
                                and then SU.To_String (D.Ty.Name)
                                       = "bool"))
               then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': bootstrap supports scalar statics only, "
                         & "got '" & Image (D.Ty) & "'");
               elsif not Assignable (D.Ty, IT) then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': initializer type '" & Image (IT)
                         & "' does not match '" & Image (D.Ty) & "'");
               elsif not Is_Static_Init (D.Init) then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': initializer shall be evaluable at "
                         & "translation time (spec 5.4, bootstrap "
                         & "subset: a literal)");
               end if;
            end;
         end loop;
      end;

      --  Phase 2: analyse each fn body. Expr/Stmt nodes are heap-
      --  allocated and reached through access values, so mutating
      --  Sem_Ty updates the shared nodes in place; the vector elements
      --  (which hold those access values) need no write-back.
      --
      --  Concrete fns (incl. monomorphised instances) are checked with
      --  an empty generic context; §5.9 templates are checked ONCE under
      --  the type-erasure rule with their parameters abstract.
      declare
         procedure Check_Fn (Fn : Fn_Decl) is
         begin
            Cur_Generics := Fn.Header.Generic_Params;
            Scope.Clear;
            Kurt.Borrow.Clear (Borrows);
            Moved.Clear;
            for J in Fn.Header.Params.First_Index ..
                     Fn.Header.Params.Last_Index
            loop
               declare
                  P : constant Param := Fn.Header.Params.Element (J);
               begin
                  if SU.Length (P.Name) > 0 then
                     Scope.Append ((Name => P.Name, Ty => P.Ty, Is_Mut => P.Is_Mut));
                  end if;
               end;
            end loop;

            if Fn.Header.Return_Type /= null then
               Cur_Ret := Fn.Header.Return_Type;
            elsif Fn.Header.Is_Closure then
               --  §9.9 a closure that omits `-> U` infers its return type
               --  from its body's first `return` (params already in scope).
               declare
                  RT : Type_Access := null;
               begin
                  for S of Fn.Body_Stmts loop
                     if S.Kind = S_Return and then S.R_Val /= null then
                        RT := Infer (S.R_Val, null);
                        exit;
                     end if;
                  end loop;
                  Cur_Ret := (if RT /= null then RT else Mk_Named ("void"));
               end;
            else
               Cur_Ret := Mk_Named ("void");
            end if;

            --  §5.1.1: the whole body of an `airside fn` is an airside
            --  region (§6.1.8 lets `uninit` appear there).
            In_Airside := (if Fn.Header.Is_Airside then 1 else 0);
            for J in Fn.Body_Stmts.First_Index ..
                     Fn.Body_Stmts.Last_Index
            loop
               Check_Stmt (Fn.Body_Stmts.Element (J));
            end loop;
            In_Airside := 0;

            --  §4.10/§7.11: a `-> never` subroutine's body shall diverge —
            --  control shall not be able to reach its end.
            if Fn.Header.Is_Never
              and then not Stmts_Diverge (Fn.Body_Stmts)
            then
               Error ("body of '-> never' subroutine '"
                      & SU.To_String (Fn.Header.Name)
                      & "' can fall through; it shall diverge "
                      & "(spec 4.10/7.11)");
            end if;
         end Check_Fn;
         --  §8.11: type- and borrow-check each `with destruct { ... }` block
         --  as codegen will lower it — with `self` bound to an exclusive
         --  reference to the object being destroyed (`$selftype`). Synthesised
         --  here so the block is held to the same rules as any subroutine.
         procedure Check_Destruct (Nm : String; Block : Stmt_Vectors.Vector) is
            D : Fn_Decl;
            P : Param;
         begin
            if Block.Is_Empty then
               return;
            end if;
            P.Name           := SU.To_Unbounded_String ("self");
            P.Ty             := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil       := R_Excl;
            P.Ty.Target      := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String (Nm);
            D.Header.Name    := SU.To_Unbounded_String (Nm & "$destruct");
            D.Header.Params.Append (P);
            D.Body_Stmts     := Block;
            Check_Fn (D);
         end Check_Destruct;
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Check_Fn (U.Fns.Element (I));
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Check_Fn (U.Gen_Fns.Element (I));
         end loop;
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            if U.Structs.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Structs.Element (I).Name),
                               U.Structs.Element (I).Destruct_Block);
            end if;
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if U.Enums.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Enums.Element (I).Name),
                               U.Enums.Element (I).Destruct_Block);
            end if;
         end loop;
      end;

      --  §4.6: a dynamically-sized array `[T]` shall not appear as a
      --  parameter, return, struct-field, or enum-payload-field type (other
      --  than as a reference target). `let`/`mut` annotations are checked in
      --  Check_Stmt.
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            H : Fn_Header renames U.Fns.Element (I).Header;
         begin
            for P in H.Params.First_Index .. H.Params.Last_Index loop
               if Is_Unsized_Value (H.Params.Element (P).Ty) then
                  Error ("`[T]`/`dyn Trait` cannot be a parameter type "
                         & "(use a reference) (spec 4.6/9.5)");
               end if;
            end loop;
            if Is_Unsized_Value (H.Return_Type) then
               Error ("`[T]`/`dyn Trait` cannot be a return type "
                      & "(use a reference) (spec 4.6/9.5)");
            end if;
         end;
      end loop;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            SD : Struct_Decl renames U.Structs.Element (I);
         begin
            for Fi in SD.Fields.First_Index .. SD.Fields.Last_Index loop
               if Is_Unsized_Value (SD.Fields.Element (Fi).Ty) then
                  Error ("`[T]`/`dyn Trait` cannot be a struct field type "
                         & "(use a reference) (spec 4.6/9.5)");
               end if;
            end loop;
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            ED : Enum_Decl renames U.Enums.Element (I);
         begin
            for Vi in ED.Variants.First_Index .. ED.Variants.Last_Index loop
               declare
                  P : Struct_Field_Vectors.Vector renames
                    ED.Variants.Element (Vi).Payload;
               begin
                  for Fi in P.First_Index .. P.Last_Index loop
                     if Is_Unsized_Value (P.Element (Fi).Ty) then
                        Error ("`[T]`/`dyn Trait` cannot be an enum "
                               & "payload field type (use a reference) "
                               & "(spec 4.6/9.5)");
                     end if;
                  end loop;
               end;
            end loop;
         end;
      end loop;

      --  §9.2.1: two trait impls on one type providing the same method name do
      --  NOT collide at declaration time (they mangle to distinct
      --  `Type$Trait$method` symbols); the collision is resolved at each
      --  invocation — a bare `e.m()` with two providers is the TF, and
      --  `(e as Trait).m()` always disambiguates. Both are handled at the call
      --  site (see Resolve_Item_Symbol), so no declaration-time check here.

      --  §9.4.2 duplicate detection: a type shall implement a given trait at
      --  most once within the translation unit.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         for J in I + 1 .. U.Trait_Impls.Last_Index loop
            if SU.Length (U.Trait_Impls.Element (I).Trait_Name) > 0
              and then SU.To_String (U.Trait_Impls.Element (I).Ty_Name)
                 = SU.To_String (U.Trait_Impls.Element (J).Ty_Name)
              and then SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                 = SU.To_String (U.Trait_Impls.Element (J).Trait_Name)
            then
               Error ("type '"
                      & SU.To_String (U.Trait_Impls.Element (I).Ty_Name)
                      & "' implements trait '"
                      & SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                      & "' more than once (spec 9.4.2)");
            end if;
         end loop;
      end loop;

      --  §9.1: two items (methods / associated fns) with the same mangled
      --  symbol on one type — e.g. two inherent `impl Type { fn a }` blocks —
      --  are a declaration-time TF (they would otherwise collide in codegen).
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         for J in I + 1 .. U.Fns.Last_Index loop
            if SU.To_String (U.Fns.Element (I).Header.Name)
                 = SU.To_String (U.Fns.Element (J).Header.Name)
            then
               Error ("duplicate definition of '"
                      & SU.To_String (U.Fns.Element (I).Header.Name)
                      & "' (two items with the same name on one type, "
                      & "spec 9.1)");
            end if;
         end loop;
      end loop;

      --  §9.4: an `impl Type as Trait` shall provide every trait method that
      --  has no default body. A missing one would otherwise fail at link time.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Tr : constant String := SU.To_String (TI.Trait_Name);

            function Impl_Provides (Nm : String) return Boolean is
            begin
               for K in TI.Methods.First_Index .. TI.Methods.Last_Index loop
                  if SU.To_String (TI.Methods.Element (K)) = Nm then
                     return True;
                  end if;
               end loop;
               return False;
            end Impl_Provides;
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  for M in U.Traits.Element (T).Methods.First_Index ..
                           U.Traits.Element (T).Methods.Last_Index loop
                     declare
                        TM : Trait_Method renames
                          U.Traits.Element (T).Methods.Element (M);
                        MN : constant String := SU.To_String (TM.Sig.Name);
                     begin
                        if not TM.Has_Body and then not Impl_Provides (MN) then
                           Error ("`impl " & SU.To_String (TI.Ty_Name)
                                  & " as " & Tr & "` does not provide method '"
                                  & MN & "' (spec 9.4)");
                        end if;
                     end;
                  end loop;
               end if;
            end loop;
         end;
      end loop;

      --  §9.3.1 associated-type completeness: an `impl T as Trait` shall
      --  define every associated type the trait leaves without a default, and
      --  shall not define one the trait does not declare.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Tr : constant String := SU.To_String (TI.Trait_Name);

            function Impl_Defines (Nm : String) return Boolean is
            begin
               for K in TI.Assoc_Types.First_Index ..
                        TI.Assoc_Types.Last_Index loop
                  if SU.To_String (TI.Assoc_Types.Element (K).Name) = Nm then
                     return True;
                  end if;
               end loop;
               return False;
            end Impl_Defines;
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  declare
                     TD : Trait_Decl renames U.Traits.Element (T);

                     function Trait_Has (Nm : String) return Boolean is
                     begin
                        for K in TD.Assoc_Types.First_Index ..
                                 TD.Assoc_Types.Last_Index loop
                           if SU.To_String (TD.Assoc_Types.Element (K).Name)
                                = Nm
                           then
                              return True;
                           end if;
                        end loop;
                        return False;
                     end Trait_Has;
                  begin
                     --  Every required (no-default) trait assoc type defined?
                     for K in TD.Assoc_Types.First_Index ..
                              TD.Assoc_Types.Last_Index loop
                        if TD.Assoc_Types.Element (K).Ty = null
                          and then not Impl_Defines
                            (SU.To_String (TD.Assoc_Types.Element (K).Name))
                        then
                           Error ("impl of trait '" & Tr & "' for type '"
                             & SU.To_String (TI.Ty_Name)
                             & "' is missing associated type '"
                             & SU.To_String (TD.Assoc_Types.Element (K).Name)
                             & "' (spec 9.3.1)");
                        end if;
                     end loop;
                     --  No def for an associated type the trait lacks?
                     for K in TI.Assoc_Types.First_Index ..
                              TI.Assoc_Types.Last_Index loop
                        if not Trait_Has
                          (SU.To_String (TI.Assoc_Types.Element (K).Name))
                        then
                           Error ("impl defines associated type '"
                             & SU.To_String (TI.Assoc_Types.Element (K).Name)
                             & "' not declared by trait '" & Tr
                             & "' (spec 9.3.1)");
                        end if;
                     end loop;
                  end;
               end if;
            end loop;
         end;
      end loop;

      --  §9.3.3 supertrait satisfaction: a type that implements a trait with
      --  supertrait bounds shall also implement every required supertrait.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Ty : constant String := SU.To_String (TI.Ty_Name);
            Tr : constant String := SU.To_String (TI.Trait_Name);
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  declare
                     TD : Trait_Decl renames U.Traits.Element (T);
                  begin
                     for S in TD.Supertraits.First_Index ..
                              TD.Supertraits.Last_Index
                     loop
                        declare
                           Sup : constant String :=
                             SU.To_String (TD.Supertraits.Element (S));
                        begin
                           if not Type_Implements (Ty, Sup) then
                              Error ("type '" & Ty & "' implements trait '"
                                     & Tr & "' but not its supertrait '"
                                     & Sup & "' (spec 9.3.3)");
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            end loop;
         end;
      end loop;

      Error_Count := Errors;
   end Check;

end Kurt.Sema;
