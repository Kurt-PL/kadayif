with Ada.Text_IO;
with Ada.Strings.Unbounded;
with Ada.Containers.Vectors;
with Ada.Unchecked_Conversion;
with Interfaces;

with Kurt.Layout;

package body Kurt.Codegen is

   package IO renames Ada.Text_IO;
   package SU renames Ada.Strings.Unbounded;

   use Kurt.Parser;

   ----------------------------------------------------------------------
   --  Numeric-to-string helpers
   ----------------------------------------------------------------------
   function Img (V : Long_Long_Integer) return String is
      Raw : constant String := Long_Long_Integer'Image (V);
   begin
      if Raw'Length >= 1 and then Raw (Raw'First) = ' ' then
         return Raw (Raw'First + 1 .. Raw'Last);
      else
         return Raw;
      end if;
   end Img;

   function Img (N : Integer) return String is
      (Img (Long_Long_Integer (N)));

   ----------------------------------------------------------------------
   --  String literal pool
   ----------------------------------------------------------------------

   type String_Entry is record
      Bytes : SU.Unbounded_String;
   end record;

   package String_Pool_Pkg is new Ada.Containers.Vectors
     (Index_Type => Natural, Element_Type => String_Entry);
   subtype String_Pool is String_Pool_Pkg.Vector;

   procedure Collect_Strings_In_Stmt
     (S : Stmt_Access; Pool : in out String_Pool);

   procedure Collect_Strings_In_Expr
     (E : Expr_Access; Pool : in out String_Pool)
   is separate;

   procedure Collect_Strings_In_Stmt
     (S : Stmt_Access; Pool : in out String_Pool)
   is separate;

   ----------------------------------------------------------------------
   --  Binding table: name → (stack offset, declared type)
   ----------------------------------------------------------------------

   type Binding is record
      Name   : SU.Unbounded_String;
      Offset : Cell_Count;
      Ty     : Type_Access;
   end record;

   --  §8.8.2/§8.11 runtime drop flag: a destruct binding carries a 1-cell
   --  frame slot, set to 1 when the binding is initialised and cleared to 0
   --  when it is transferred / `destruct`-ed / `undestruct`-ed. Scope-exit
   --  destruction is guarded on the flag, so a binding moved on only some
   --  control-flow paths is destroyed exactly once (conditional-move drop
   --  flags). Bind_Off identifies the binding by its frame slot.
   type Drop_Flag is record
      Bind_Off : Cell_Count;
      Flag_Off : Cell_Count;
   end record;

   package Flag_Vec is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Drop_Flag);

   package Binding_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Binding);

   ----------------------------------------------------------------------
   --  Dyn-item symbol table — every fn prototype inside a `@dyn` block.
   --  Records the fixed-arg count and whether the prototype is variadic,
   --  so call sites can split arguments correctly under Apple's arm64
   --  variadic ABI (named args in regs, ... on the stack).
   ----------------------------------------------------------------------

   type Dyn_Sym is record
      Name        : SU.Unbounded_String;
      Fixed_Args  : Natural := 0;
      Is_Variadic : Boolean := False;
      --  §5.15 `@symbol`: external name to emit at call sites; empty means
      --  use the Kurt identifier (Name).
      Symbol      : SU.Unbounded_String;
   end record;

   package Dyn_Sym_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Dyn_Sym);

   --  §9.5-6 trait metadata for dynamic dispatch, captured by Emit. The
   --  trait declarations give each method's Zone-C index (the impl list,
   --  used for dispatch-table emission, is read directly from U in Emit).
   Unit_Traits : Trait_Vectors.Vector;

   --  §5.4 static bindings of the unit being emitted (label `_Kst_NAME`).
   Unit_Statics : Static_Vectors.Vector;

   --  §5.3 top-level `const` declarations, published so Lower_Stmt's
   --  inline-`asm` `'(expr)` evaluator (§6.11) can resolve a `const` name
   --  the same way Emit's top-level-`asm` evaluator does (§5.13) — see
   --  Kurt.Parser.Fold_Int_Expr.
   Unit_Consts : Const_Vectors.Vector;

   --  §7.10.1 whether this unit declares a `@trap` handler. When set, a
   --  `@trap;` branches to the synthesised `_kurt_trap_handler`; otherwise
   --  it goes straight to the default divergence.
   Unit_Has_Trap_Handler : Boolean := False;

   --  §8.11 type names with an emittable destructor `_<Name>$drop` (declared
   --  `with destruct { ... }`). Set by Emit; read at scope-exit drop emission.
   Unit_Drop_Types : Path_Segments.Vector;

   function Type_Has_Drop (Name : String) return Boolean is
   begin
      for I in Unit_Drop_Types.First_Index .. Unit_Drop_Types.Last_Index loop
         if SU.To_String (Unit_Drop_Types.Element (I)) = Name then
            return True;
         end if;
      end loop;
      return False;
   end Type_Has_Drop;

   --  §8.11 destroy the object of type T living at [self+Off], where `self`
   --  (an exclusive reference = object address) sits in frame slot Self_Off.
   --  A named field delegates to its own `_<Name>$drop`; array elements and
   --  tuple members are destroyed in turn (they have no synthesised drop of
   --  their own). Only destruct-satisfying parts emit anything.
   procedure Emit_Drop_At
     (F : IO.File_Type; Self_Off, Off : Cell_Count;
      T : Kurt.Parser.Type_Access)
   is separate;

   --  §8.11 field/payload destruction tail of a synthesised `<Tn>$drop`.
   --  Struct: destroy each destruct-satisfying field in declaration order.
   --  Enum: load the discriminant and destroy the active variant's payload.
   procedure Emit_Field_Drops
     (F : IO.File_Type; Tn : String; Self_Off : Cell_Count)
   is separate;

   --  Index of Name in Unit_Statics, or 0.
   function Find_Static (Name : String) return Natural is
   begin
      for I in Unit_Statics.First_Index .. Unit_Statics.Last_Index loop
         if SU.To_String (Unit_Statics.Element (I).Name) = Name then
            return I;
         end if;
      end loop;
      return 0;
   end Find_Static;

   --  §9.6.3: the field index of method M_Name in trait Tr_Name. Zone C
   --  begins at field `3 + S` (S = number of direct supertraits); the
   --  k-th method is field `3 + S + k`. Returns -1 if unknown.
   function Method_Field_Index (Tr_Name, M_Name : String) return Integer is separate;

   --  Active loop labels, innermost last. `continue` targets Cont_Lbl
   --  (the loop's condition re-test) and `break` targets Break_Lbl.
   type Loop_Labels is record
      Cont_Lbl  : SU.Unbounded_String;
      Break_Lbl : SU.Unbounded_String;
      Name      : SU.Unbounded_String;   --  §7.9 source label; empty = none
      --  §8.4 binding count at the loop body's entry, so `break`/`continue`
      --  destroy the body locals live at the jump before leaving the body.
      Body_Entry : Natural := 0;
      --  §7.7 frame offset of the loop-expression's result slot; a `break
      --  expr` targeting this loop stores its value here. -1 for a statement
      --  loop (the break value, if any, is discarded).
      Result_Off : Long_Long_Integer := -1;
   end record;

   package Loop_Stack_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Loop_Labels);

   --  §7.8 active express-block targets, innermost last. An `express`
   --  stores its value to the innermost target's Result_Off, destroys
   --  the bindings declared since the block's entry (Body_Entry), and
   --  branches to End_Lbl — an early exit from the block expression.
   type Express_Target is record
      End_Lbl    : SU.Unbounded_String;
      Result_Off : Cell_Count := 0;
      Body_Entry : Natural := 0;
      Name       : SU.Unbounded_String;   --  §7.9 block label; empty = none
   end record;

   package Express_Stack_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Express_Target);

   --  Internal fn return types, so call sites can classify the return
   --  value per the Apple AAPCS64 composite rules (1 reg / 2 regs / sret).
   type Fn_Ret is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
      --  §5.15 `@symbol "name"` on an `extern` fn WITH a body: overrides the
      --  external name a direct call site (and a bare-name fn-pointer
      --  coercion) targets. Empty = use the Kurt identifier (Name).
      Symbol : SU.Unbounded_String;
   end record;

   package Fn_Ret_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Fn_Ret);

   type Lower_State is record
      Next_Str_Idx : Natural := 0;
      Fn_Name      : SU.Unbounded_String;  --  for per-function label uniqueness
      Epilogue_Lbl : SU.Unbounded_String;
      Bindings     : Binding_Pkg.Vector;
      Next_Offset  : Cell_Count := 16;  --  16 bytes reserved for x29/x30
      If_Idx       : Natural := 0;
      Loop_Idx     : Natural := 0;
      Dyn_Syms     : Dyn_Sym_Pkg.Vector;
      Loops        : Loop_Stack_Pkg.Vector;
      --  §7.8 express-block targets (innermost last; see Express_Target).
      Expr_Blocks  : Express_Stack_Pkg.Vector;
      --  Aggregate-ABI context (AAPCS64). Ret_Ty is the enclosing fn's
      --  return type; Sret_Off is the frame slot holding the incoming x8
      --  indirect-result pointer (-1 when the return is not sret-class);
      --  Pending_Sret is set by a let-binding right before lowering an
      --  E_Call initialiser whose result must land in that frame slot.
      Ret_Ty       : Type_Access := null;
      Sret_Off     : Long_Long_Integer := -1;
      Pending_Sret : Long_Long_Integer := -1;
      Fn_Rets      : Fn_Ret_Pkg.Vector;
      --  §8.8.2/§8.11 runtime drop flags for this body's destruct bindings,
      --  and a counter for the unique skip labels of guarded drops.
      Drop_Flags   : Flag_Vec.Vector;
      Flag_Lbl     : Natural := 0;
      --  §8.11 16-byte frame slot for saving the return value (x0/x1) across
      --  scope-exit destructor calls (set in Emit_Fn's prologue).
      Ret_Scratch  : Cell_Count := 0;
   end record;

   --  Frame offset of the drop flag for the binding at Bind_Off, or -1.
   function Flag_Off_Of
     (ST : Lower_State; Bind_Off : Cell_Count) return Long_Long_Integer is
   begin
      for E of ST.Drop_Flags loop
         if E.Bind_Off = Bind_Off then
            return Long_Long_Integer (E.Flag_Off);
         end if;
      end loop;
      return -1;
   end Flag_Off_Of;

   function Lookup_Fn_Ret
     (ST : Lower_State; Name : String) return Type_Access
   is
   begin
      for I in ST.Fn_Rets.First_Index .. ST.Fn_Rets.Last_Index loop
         if SU.To_String (ST.Fn_Rets.Element (I).Name) = Name then
            return ST.Fn_Rets.Element (I).Ty;
         end if;
      end loop;
      return null;
   end Lookup_Fn_Ret;

   --  §5.15: the `@symbol` override for internal fn Name, or "" when it has
   --  none (or Name is unknown here — a `@dyn` callee, handled separately).
   function Fn_Symbol_Of
     (ST : Lower_State; Name : String) return String
   is
   begin
      for I in ST.Fn_Rets.First_Index .. ST.Fn_Rets.Last_Index loop
         if SU.To_String (ST.Fn_Rets.Element (I).Name) = Name then
            return SU.To_String (ST.Fn_Rets.Element (I).Symbol);
         end if;
      end loop;
      return "";
   end Fn_Symbol_Of;

   function Lookup_Dyn_Sym
     (ST : Lower_State; Name : String; Found : out Dyn_Sym) return Boolean
   is
   begin
      for I in ST.Dyn_Syms.First_Index .. ST.Dyn_Syms.Last_Index loop
         if SU.To_String (ST.Dyn_Syms.Element (I).Name) = Name then
            Found := ST.Dyn_Syms.Element (I);
            return True;
         end if;
      end loop;
      return False;
   end Lookup_Dyn_Sym;

   --  Look up a name in the binding stack (most recent first). Returns
   --  position in the vector, or 0 when not found.
   function Find_Binding (ST : Lower_State; Name : String) return Natural is
   begin
      for I in reverse ST.Bindings.First_Index .. ST.Bindings.Last_Index loop
         if SU.To_String (ST.Bindings.Element (I).Name) = Name then
            return I;
         end if;
      end loop;
      return 0;
   end Find_Binding;

   --  §8.8.2: if E is a transferred (moved) binding (Kurt.Sema set
   --  P_Is_Move), clear its runtime drop flag at this point, so its
   --  scope-exit destructor does not run (the obligation moved to the
   --  destination). The clear is at the move's control-flow position, so a
   --  conditional move clears the flag only on the path it occurs.
   procedure Note_Move
     (F : IO.File_Type; ST : in out Lower_State; E : Expr_Access) is separate;

   --  §8.4/§8.11 scope-exit destruction: run the destructor of each
   --  `with destruct` binding declared above index Keep, in reverse
   --  declaration order (LIFO, innermost first). Each drop is guarded by the
   --  binding's runtime drop flag (cleared on transfer / destruct), so a
   --  binding moved on only some paths is destroyed exactly once. Used at the
   --  fn epilogue (Keep = 0), at every inner-block exit (Keep = the block's
   --  entry binding count), and at each `return` (Keep = 0, all in scope).
   --  Preserve_Ret saves/restores x0/x1 around the calls so a return value
   --  survives the destructor invocations.
   procedure Emit_Binding_Drops
     (F : IO.File_Type; ST : in out Lower_State;
      Keep : Natural; Preserve_Ret : Boolean)
   is separate;

   ----------------------------------------------------------------------
   --  Layout queries (single-sourced in Kurt.Layout, §4.11)
   ----------------------------------------------------------------------
   function Sizeof (T : Type_Access) return Cell_Count is
     (Kurt.Layout.Size_Of (T));

   --  §7.4 the payload-region offset / type of a variant pattern's K-th
   --  binding: by the named field for a `field = binding` rename entry,
   --  else by position K.
   function Pat_Field_Off
     (Pat : Kurt.Parser.Pattern; T : Type_Access; VN : String; K : Positive)
      return Cell_Count is
   begin
      if K <= Natural (Pat.Bind_Fields.Length)
        and then SU.Length (Pat.Bind_Fields.Element (K)) > 0
      then
         return Cell_Count
           (Long_Long_Integer'Max
              (0, Kurt.Layout.Variant_Field_Offset_By_Name
                    (T, VN, SU.To_String (Pat.Bind_Fields.Element (K)))));
      end if;
      return Kurt.Layout.Variant_Field_Offset (T, VN, K);
   end Pat_Field_Off;

   function Pat_Field_Ty
     (Pat : Kurt.Parser.Pattern; T : Type_Access; VN : String; K : Positive)
      return Type_Access is
   begin
      if K <= Natural (Pat.Bind_Fields.Length)
        and then SU.Length (Pat.Bind_Fields.Element (K)) > 0
      then
         return Kurt.Layout.Variant_Field_Type_By_Name
           (T, VN, SU.To_String (Pat.Bind_Fields.Element (K)));
      end if;
      return Kurt.Layout.Variant_Field_Type (T, VN, K);
   end Pat_Field_Ty;

   function Is_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref);

   --  §7.11: "an invocation of a subroutine declared with the return-type
   --  keyword `never`" is a diverging expression (mirrors Kurt.Sema.
   --  Check.Stmt_Diverges' `when S_Expr` case, which this codegen pass
   --  cannot call directly). Shared by Lower_Stmt (nested blocks) and
   --  Emit_Fn (the top-level function body) so both insert the implicit
   --  `@trap` the spec requires after such a statement.
   function Is_Never_Expr (E : Expr_Access) return Boolean is
     (E /= null and then E.Sem_Ty /= null
      and then E.Sem_Ty.Kind = T_Named
      and then SU.To_String (E.Sem_Ty.Name) = "never");

   --  An aggregate lives in RAM: a struct, an enum with a payload, a
   --  tuple, or an array. A unit-only enum is a bare discriminant (scalar).
   function Is_Aggregate_Type (T : Type_Access) return Boolean is
     (T /= null
      and then ((T.Kind = T_Named
                   and then (Kurt.Layout.Is_Struct (SU.To_String (T.Name))
                             or else Kurt.Layout.Enum_Has_Payload
                                       (SU.To_String (T.Name))))
                or else T.Kind = T_Tuple
                or else T.Kind = T_Array));

   --  §7.2: contract types in codegen. `bool` is the built-in scalar
   --  contract (success = 1, failure = 0); any other contract enum takes
   --  its variant discriminants from the layout registry.
   function Is_Contract_Ty (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Named
      and then (SU.To_String (T.Name) = "bool"
                or else Kurt.Layout.Is_Contract_Enum
                          (SU.To_String (T.Name))));

   function Contract_Succ_Val (T : Type_Access) return Long_Long_Integer is
     (if SU.To_String (T.Name) = "bool" then 1
      else Kurt.Layout.Variant_Value
        (SU.To_String (T.Name),
         Kurt.Layout.Contract_Success_Variant (SU.To_String (T.Name))));

   function Contract_Fail_Val (T : Type_Access) return Long_Long_Integer is
     (if SU.To_String (T.Name) = "bool" then 0
      else Kurt.Layout.Variant_Value
        (SU.To_String (T.Name),
         Kurt.Layout.Contract_Fail_Variant (SU.To_String (T.Name))));

   --  AAPCS64 composite classification of a by-value aggregate.
   --    One_Reg  : size ≤ 8  — one x register
   --    Two_Regs : size ≤ 16 — a consecutive register pair
   --    Indirect : size > 16 — caller-allocated copy, pointer passed;
   --               returns use the x8 indirect-result register (sret)
   type Agg_Class is (Not_Agg, One_Reg, Two_Regs, Indirect);

   --  §9.5: a reference to a trait object is a 16-byte fat reference and
   --  travels by the two-register aggregate rule.
   function Is_Dyn_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref
      and then T.Target /= null and then T.Target.Kind = T_Dyn);

   --  §4.6: a `&[T]` slice — also a 16-byte fat reference (ptr + len).
   function Is_Slice_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref
      and then T.Target /= null and then T.Target.Kind = T_Array
      and then T.Target.Len = 0);

   function Classify_Agg (T : Type_Access) return Agg_Class is
   begin
      if Is_Dyn_Ref (T) or else Is_Slice_Ref (T) then
         return Two_Regs;
      elsif not Is_Aggregate_Type (T) then
         return Not_Agg;
      elsif Kurt.Layout.Size_Of (T) <= 8 then
         return One_Reg;
      elsif Kurt.Layout.Size_Of (T) <= 16 then
         return Two_Regs;
      else
         return Indirect;
      end if;
   end Classify_Agg;

   --  A named integer type is signed iff it is an `si*` type or `saddr`.
   function Is_Signed_Int (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      declare
         N : constant String := SU.To_String (T.Name);
      begin
         return (N'Length >= 2
                   and then N (N'First) = 's' and then N (N'First + 1) = 'i')
             or else N = "saddr";
      end;
   end Is_Signed_Int;

   --  A floating-point named type (§4).
   function Is_Float (T : Type_Access) return Boolean is
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
   end Is_Float;

   --  Load an arbitrary 64-bit pattern into integer register x<Reg> with a
   --  movz/movk sequence (unlike Lower_Imm, accepts the full unsigned range).
   procedure Lower_Bits_64
     (F : IO.File_Type; Reg : Natural; Bits : Interfaces.Unsigned_64)
   is
      use Interfaces;
      R     : constant String := "x" & Img (Reg);
      Done  : Boolean := False;
   begin
      if Bits = 0 then
         IO.Put_Line (F, "    mov     " & R & ", #0");
         return;
      end if;
      for I in 0 .. 3 loop
         declare
            Lane : constant Unsigned_64 :=
              Shift_Right (Bits, 16 * I) and 16#FFFF#;
         begin
            if Lane /= 0 then
               IO.Put_Line
                 (F,
                  (if not Done then "    movz    " else "    movk    ")
                  & R & ", #" & Img (Long_Long_Integer (Lane))
                  & (if I = 0 then "" else ", lsl #" & Img (16 * I)));
               Done := True;
            end if;
         end;
      end loop;
   end Lower_Bits_64;

   --  Materialise the floating-point constant Value into FP register
   --  d<D_Reg> (f64) or s<D_Reg> (f32 when Bytes = 4), via the IEEE-754
   --  bit pattern loaded through a scratch integer register (x12/w12).
   procedure Lower_Float_Const
     (F : IO.File_Type; D_Reg : Natural; Value : Long_Float;
      Bytes : Cell_Count)
   is separate;

   --  The type of an expression is whatever Kurt.Sema attached. Falls
   --  back to the binding table for bare identifiers in the unlikely
   --  event sema left Sem_Ty null (e.g. a path used only as a callee).
   function Type_Of_Expr (E : Expr_Access; ST : Lower_State) return Type_Access
   is separate;

   ----------------------------------------------------------------------
   --  String pool emission
   ----------------------------------------------------------------------

   procedure Emit_String_Pool
     (F : IO.File_Type; Pool : String_Pool)
   is separate;

   ----------------------------------------------------------------------
   --  Shared lowering helpers used by the subunits below.
   ----------------------------------------------------------------------

   --  Materialise a non-negative integer immediate into a register via a
   --  movz / movk chain (each instruction sets one 16-bit lane).
   procedure Lower_Imm
     (F : IO.File_Type; Reg : Natural; V : Long_Long_Integer; Wide : Boolean)
   is separate;

   --  §7.2.2 truthiness: reduce the contract value in x<Reg> to 0/1 —
   --  1 iff the discriminant equals the success variant's value. The
   --  register may hold a whole ≤8-byte payload aggregate, so the
   --  discriminant (at offset 0) is masked out first. Scratch: x12, x13.
   procedure Emit_Truthify
     (F : IO.File_Type; Reg : Natural; Ty : Type_Access)
   is separate;

   --  Copy Sz bytes from [Src_Base, #Src_Off] to [Dst_Base, #Dst_Off]
   --  through x9/w9, in 8-byte chunks with a sized tail (so reads never
   --  overrun a source that is not 8-byte padded, e.g. a payload alias).
   procedure Emit_Mem_Copy
     (F        : IO.File_Type;
      Src_Base : String; Src_Off : Cell_Count;
      Dst_Base : String; Dst_Off : Cell_Count;
      Sz       : Cell_Count)
   is separate;

   function Path_Symbol (E : Expr_Access) return String is
   begin
      if E = null or else E.Kind /= E_Path or else E.Segments.Is_Empty then
         raise Program_Error with "Path_Symbol: not a non-empty path";
      end if;
      return SU.To_String (E.Segments.Last_Element);
   end Path_Symbol;

   ----------------------------------------------------------------------
   --  Lowering bodies live in separate subunits to keep each source file
   --  well under 1000 lines:
   --    kurt-codegen-lower_expr_into_reg.adb  — expressions (+ nested
   --                                             call / binary / if)
   --    kurt-codegen-lower_stmt.adb           — statements
    --  Both subunits see every declaration above and recurse into each
   --  other freely.
   ----------------------------------------------------------------------

   --  Forward declarations first, so the mutually-recursive subunits
   --  (Lower_Expr_Into_Reg ⇄ Lower_Float_Into_D, Lower_Stmt) can all call
   --  one another regardless of stub order.
   procedure Lower_Float_Into_D
     (F     : IO.File_Type;
      E     : Expr_Access;
      D_Reg : Natural;
      ST    : in out Lower_State);
   --  Materialise a float-typed expression into FP register d<D_Reg> (f64)
   --  or s<D_Reg> (f32, when its type is 4 bytes).

   procedure Lower_Expr_Into_Reg
     (F          : IO.File_Type;
      E          : Expr_Access;
      Target_Reg : Natural;
      ST         : in out Lower_State);

   procedure Lower_Stmt
     (F  : IO.File_Type;
      S  : Stmt_Access;
      ST : in out Lower_State);

   --  §2.1.4: materialise a struct/variant/tuple/array literal into a
   --  freshly bump-allocated stack temporary (same allocation scheme as a
   --  let-binding's slot), returning its frame offset. This lets a
   --  composite literal appear anywhere an lvalue-shaped source is needed
   --  (call argument, return value, match scrutinee) and not only as a
   --  let/mut initialiser. The temporary is never registered as a binding,
   --  so it carries no runtime drop flag and no scope-exit destructor is
   --  ever emitted for it: the only reachable non-initialiser positions
   --  (call arguments, `return`) TRANSFER the value into the callee/caller
   --  per §8.8.2, so no drop is owed. This routine is not a general
   --  temporary-drop mechanism and shall not be used where the value could
   --  be read without being transferred while its type satisfies destruct.
   function Materialize_Composite
     (F : IO.File_Type; ST : in out Lower_State;
      Ty : Type_Access; Init : Expr_Access)
      return Cell_Count;

   --  Completions as separate subunits.
   procedure Lower_Float_Into_D
     (F     : IO.File_Type;
      E     : Expr_Access;
      D_Reg : Natural;
      ST    : in out Lower_State) is separate;

   procedure Lower_Expr_Into_Reg
     (F          : IO.File_Type;
      E          : Expr_Access;
      Target_Reg : Natural;
      ST         : in out Lower_State) is separate;

   procedure Lower_Stmt
     (F  : IO.File_Type;
      S  : Stmt_Access;
      ST : in out Lower_State) is separate;

   function Materialize_Composite
     (F : IO.File_Type; ST : in out Lower_State;
      Ty : Type_Access; Init : Expr_Access)
      return Cell_Count
   is separate;

   ----------------------------------------------------------------------
   --  Function lowering
   ----------------------------------------------------------------------

   --  16-byte aligned, generous enough for the bootstrap. Scalars take
   --  8 bytes; aggregates and arrays their rounded size. Overflow is
   --  detected after lowering (Next_Offset is checked against this).
   Frame_Bytes : constant Cell_Count := 512;

   procedure Emit_Fn
     (F        : IO.File_Type;
      Fn       : Fn_Decl;
      Dyn_Syms : Dyn_Sym_Pkg.Vector;
      Fn_Rets  : Fn_Ret_Pkg.Vector;
      Str_Base : in out Natural)
   is separate;

   ----------------------------------------------------------------------
   procedure Emit (U : Kurt.Parser.Translation_Unit; Out_Path : String) is separate;

end Kurt.Codegen;
