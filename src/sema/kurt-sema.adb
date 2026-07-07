with Ada.Text_IO;
with Ada.Strings.Unbounded;
with Ada.Containers.Vectors;

with Kurt.Layout;
with Kurt.Borrow;
with Kurt.Mono;

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
   function Disc_Ty_Name (Sz : Cell_Count; Signed : Boolean)
     return String is
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
   --  Recurses into T_Array element types and T_Tuple member types: a
   --  fixed-size array of `dyn Trait` (`[dyn Show; 2]`) or a tuple
   --  containing one (`.{dyn Show, si4}`) embeds the unsized value just
   --  as directly as a bare top-level occurrence would, and the codegen
   --  layout has no more idea how to size that member than it would the
   --  bare form.
   function Is_Unsized_Value (T : Type_Access) return Boolean is
   begin
      if Is_Unsized_Arr (T) or else Is_Dyn_Bare (T) then
         return True;
      end if;
      if T = null then
         return False;
      end if;
      case T.Kind is
         when T_Array =>
            return Is_Unsized_Value (T.Elem);
         when T_Tuple =>
            for I in T.Elems.First_Index .. T.Elems.Last_Index loop
               if Is_Unsized_Value (T.Elems.Element (I)) then
                  return True;
               end if;
            end loop;
            return False;
         when others =>
            return False;
      end case;
   end Is_Unsized_Value;

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

   --  §8.5.2: "Creating an `&atomic T` or `&guard T` reference for a `T`
   --  at a width for which the execution environment does not provide
   --  atomic operations shall not appear." On this aarch64 backend, atomic
   --  load/store/RMW/CAS lower to ldaxr/stlxr, which handle 1/2/4/8-byte
   --  operands only; a 16-byte (ldaxp-shaped) or wider operand has no
   --  lowering here, so widths above 8 bytes are not atomic-eligible.
   function Is_Atomic_Width_Ok (T : Type_Access) return Boolean is
   begin
      return Is_Unsigned_Int_Type (T) and then Kurt.Layout.Size_Of (T) <= 8;
   end Is_Atomic_Width_Ok;

   --  §6.5: the unsigned integer type of a given size in cells — the
   --  contextual type of an unsuffixed shift-count literal.
   function Unsigned_Of_Size (Size : Cell_Count) return Type_Access is
      S : constant String := Cell_Count'Image (Size);
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
      --  §5.1.2 `extern(iface)` invocation interface; "" = native. Carried
      --  into the synthesized `fn(...)->...` type of a bare-name fn-pointer
      --  value so a non-native interface makes it a distinct type (§4.10).
      Extern_Iface : SU.Unbounded_String;
      --  §5.12.1/§9.2: whether the subroutine itself was declared `pub`.
      --  An `impl` method inherits no visibility of its own (spec 5.12.1),
      --  so a non-`pub` method is callable via `.method()` receiver syntax
      --  only from the source unit that declares it (Infer_Call).
      Is_Pub : Boolean := False;
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

   --  §5.2 definite-assignment state for a deferred-init binding (`let
   --  x: T;` / `mut x: T;`, initializer omitted). Uninit: untouched on
   --  every live path so far. Maybe: assigned on some but not all live
   --  paths -- a "proof failure": a read/reference-creation is rejected,
   --  and (if the type satisfies `destruct`) so is scope exit. Init:
   --  assigned on every live path.
   type Init_State is (St_Uninit, St_Maybe, St_Init);

   type Init_Bind is record
      Name   : SU.Unbounded_String;
      State  : Init_State := St_Uninit;
      Depth  : Natural := 0;
      Ty     : Type_Access;
      Is_Let : Boolean := False;  --  single-assignment (spec 5.2)
   end record;

   package Init_Vec is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Init_Bind);

   ----------------------------------------------------------------------
   procedure Check
     (U           : in out Kurt.Parser.Translation_Unit;
      Error_Count : out Natural)
   is separate;

end Kurt.Sema;
