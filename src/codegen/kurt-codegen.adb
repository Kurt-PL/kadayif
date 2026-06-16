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

   procedure Collect_Strings_In_Expr
     (E : Expr_Access; Pool : in out String_Pool)
   is
   begin
      if E = null then
         return;
      end if;
      case E.Kind is
         when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_Path | E_Uninit =>
            null;
         when E_Range =>
            Collect_Strings_In_Expr (E.Rg_Lo, Pool);
            Collect_Strings_In_Expr (E.Rg_Hi, Pool);
         when E_String_Lit =>
            Pool.Append ((Bytes => E.Str_Bytes));
         when E_Field =>
            Collect_Strings_In_Expr (E.F_Recv, Pool);
         when E_Call =>
            Collect_Strings_In_Expr (E.C_Callee, Pool);
            for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
               Collect_Strings_In_Expr (E.C_Args.Element (I), Pool);
            end loop;
         when E_If =>
            Collect_Strings_In_Expr (E.I_Cond, Pool);
            Collect_Strings_In_Expr (E.I_Then, Pool);
            Collect_Strings_In_Expr (E.I_Else, Pool);
         when E_Binary =>
            Collect_Strings_In_Expr (E.B_Lhs, Pool);
            Collect_Strings_In_Expr (E.B_Rhs, Pool);
         when E_Deref =>
            Collect_Strings_In_Expr (E.D_Inner, Pool);
         when E_Struct_Lit =>
            for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index loop
               Collect_Strings_In_Expr (E.SL_Fields.Element (I).Val, Pool);
            end loop;
         when E_Variant_New =>
            for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index loop
               Collect_Strings_In_Expr (E.VN_Fields.Element (I).Val, Pool);
            end loop;
         when E_Match =>
            Collect_Strings_In_Expr (E.M_Scrut, Pool);
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               Collect_Strings_In_Expr (E.M_Arms.Element (I).Arm_Body, Pool);
            end loop;
         when E_Cast =>
            Collect_Strings_In_Expr (E.Cast_Inner, Pool);
         when E_Unary =>
            Collect_Strings_In_Expr (E.U_Operand, Pool);
         when E_Tuple_Lit =>
            for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
               Collect_Strings_In_Expr (E.TL_Elems.Element (I), Pool);
            end loop;
         when E_Question =>
            Collect_Strings_In_Expr (E.Q_Inner, Pool);
         when E_Ref =>
            Collect_Strings_In_Expr (E.Rf_Place, Pool);
         when E_CAS =>
            Collect_Strings_In_Expr (E.CAS_Tgt, Pool);
            Collect_Strings_In_Expr (E.CAS_Exp, Pool);
            Collect_Strings_In_Expr (E.CAS_New, Pool);
         when E_Array_Lit =>
            for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               Collect_Strings_In_Expr (E.AL_Elems.Element (I), Pool);
            end loop;
         when E_Dyn_Cast =>
            Collect_Strings_In_Expr (E.DC_Inner, Pool);
         when E_Slice_Cast =>
            Collect_Strings_In_Expr (E.SC_Inner, Pool);
         when E_Type_Intrinsic =>
            null;   --  folded to a constant; no strings
      end case;
   end Collect_Strings_In_Expr;

   procedure Collect_Strings_In_Stmt
     (S : Stmt_Access; Pool : in out String_Pool)
   is
   begin
      case S.Kind is
         when S_Return =>
            Collect_Strings_In_Expr (S.R_Val, Pool);
         when S_Expr =>
            Collect_Strings_In_Expr (S.E_Val, Pool);
         when S_Airside_Block =>
            for I in S.A_Stmts.First_Index .. S.A_Stmts.Last_Index loop
               Collect_Strings_In_Stmt (S.A_Stmts.Element (I), Pool);
            end loop;
         when S_Let | S_Mut =>
            Collect_Strings_In_Expr (S.L_Init, Pool);
         when S_Assign =>
            Collect_Strings_In_Expr (S.Asn_Lhs, Pool);
            Collect_Strings_In_Expr (S.Asn_Rhs, Pool);
         when S_While =>
            Collect_Strings_In_Expr (S.W_Cond, Pool);
            for I in S.W_Body.First_Index .. S.W_Body.Last_Index loop
               Collect_Strings_In_Stmt (S.W_Body.Element (I), Pool);
            end loop;
            for I in S.W_Then.First_Index .. S.W_Then.Last_Index loop
               Collect_Strings_In_Stmt (S.W_Then.Element (I), Pool);
            end loop;
         when S_If =>
            Collect_Strings_In_Expr (S.SI_Cond, Pool);
            for I in S.SI_Then.First_Index .. S.SI_Then.Last_Index loop
               Collect_Strings_In_Stmt (S.SI_Then.Element (I), Pool);
            end loop;
            for I in S.SI_Else.First_Index .. S.SI_Else.Last_Index loop
               Collect_Strings_In_Stmt (S.SI_Else.Element (I), Pool);
            end loop;
         when S_Extract =>
            Collect_Strings_In_Expr (S.X_Expr, Pool);
            for I in S.X_Else.First_Index .. S.X_Else.Last_Index loop
               Collect_Strings_In_Stmt (S.X_Else.Element (I), Pool);
            end loop;
         when S_Break =>
            Collect_Strings_In_Expr (S.Brk_Val, Pool);
         when S_Continue | S_Fence =>
            null;
         when S_Express =>
            Collect_Strings_In_Expr (S.Xp_Val, Pool);
      end case;
   end Collect_Strings_In_Stmt;

   ----------------------------------------------------------------------
   --  Binding table: name → (stack offset, declared type)
   ----------------------------------------------------------------------

   type Binding is record
      Name   : SU.Unbounded_String;
      Offset : Natural;
      Ty     : Type_Access;
   end record;

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
   function Method_Field_Index (Tr_Name, M_Name : String) return Integer is
   begin
      for I in Unit_Traits.First_Index .. Unit_Traits.Last_Index loop
         if SU.To_String (Unit_Traits.Element (I).Name) = Tr_Name then
            declare
               Tr : Trait_Decl renames Unit_Traits.Element (I);
               S  : constant Natural := Natural (Tr.Supertraits.Length);
            begin
               for J in Tr.Methods.First_Index .. Tr.Methods.Last_Index loop
                  if SU.To_String (Tr.Methods.Element (J).Sig.Name)
                       = M_Name
                  then
                     return 3 + S + (J - Tr.Methods.First_Index);
                  end if;
               end loop;
            end;
         end if;
      end loop;
      return -1;
   end Method_Field_Index;

   --  Active loop labels, innermost last. `continue` targets Cont_Lbl
   --  (the loop's condition re-test) and `break` targets Break_Lbl.
   type Loop_Labels is record
      Cont_Lbl  : SU.Unbounded_String;
      Break_Lbl : SU.Unbounded_String;
      Name      : SU.Unbounded_String;   --  §7.9 source label; empty = none
   end record;

   package Loop_Stack_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Loop_Labels);

   --  Internal fn return types, so call sites can classify the return
   --  value per the Apple AAPCS64 composite rules (1 reg / 2 regs / sret).
   type Fn_Ret is record
      Name : SU.Unbounded_String;
      Ty   : Type_Access;
   end record;

   package Fn_Ret_Pkg is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Fn_Ret);

   type Lower_State is record
      Next_Str_Idx : Natural := 0;
      Fn_Name      : SU.Unbounded_String;  --  for per-function label uniqueness
      Epilogue_Lbl : SU.Unbounded_String;
      Bindings     : Binding_Pkg.Vector;
      Next_Offset  : Natural := 16;  --  16 bytes reserved for x29/x30
      If_Idx       : Natural := 0;
      Loop_Idx     : Natural := 0;
      Dyn_Syms     : Dyn_Sym_Pkg.Vector;
      Loops        : Loop_Stack_Pkg.Vector;
      --  Aggregate-ABI context (AAPCS64). Ret_Ty is the enclosing fn's
      --  return type; Sret_Off is the frame slot holding the incoming x8
      --  indirect-result pointer (-1 when the return is not sret-class);
      --  Pending_Sret is set by a let-binding right before lowering an
      --  E_Call initialiser whose result must land in that frame slot.
      Ret_Ty       : Type_Access := null;
      Sret_Off     : Integer := -1;
      Pending_Sret : Integer := -1;
      Fn_Rets      : Fn_Ret_Pkg.Vector;
   end record;

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

   ----------------------------------------------------------------------
   --  Layout queries (single-sourced in Kurt.Layout, §4.11)
   ----------------------------------------------------------------------
   function Sizeof (T : Type_Access) return Natural is
     (Kurt.Layout.Size_Of (T));

   function Is_Ref (T : Type_Access) return Boolean is
     (T /= null and then T.Kind = T_Ref);

   --  An aggregate lives in RAM: a struct, an enum with a payload, a
   --  tuple, or an array. A unit-only enum is a bare discriminant (scalar).
   function Is_Aggregate_Type (T : Type_Access) return Boolean is
     (T /= null
      and then ((T.Kind = T_Named
                   and then (Kurt.Layout.Is_Struct (SU.To_String (T.Name))
                             or else Kurt.Layout.Enum_Has_Payload
                                       (SU.To_String (T.Name))))
                or else T.Kind = T_Tuple
                or else T.Kind = T_Array
                or else T.Kind = T_Range));

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
     (F : IO.File_Type; D_Reg : Natural; Value : Long_Float; Bytes : Natural)
   is
      use Interfaces;
      function To_U64 is new Ada.Unchecked_Conversion (Long_Float, Unsigned_64);
      function To_U32 is new Ada.Unchecked_Conversion (Float, Unsigned_32);
   begin
      if Bytes = 4 then
         Lower_Bits_64
           (F, 12, Unsigned_64 (To_U32 (Float (Value))));
         IO.Put_Line (F, "    fmov    s" & Img (D_Reg) & ", w12");
      else
         Lower_Bits_64 (F, 12, To_U64 (Value));
         IO.Put_Line (F, "    fmov    d" & Img (D_Reg) & ", x12");
      end if;
   end Lower_Float_Const;

   --  The type of an expression is whatever Kurt.Sema attached. Falls
   --  back to the binding table for bare identifiers in the unlikely
   --  event sema left Sem_Ty null (e.g. a path used only as a callee).
   function Type_Of_Expr (E : Expr_Access; ST : Lower_State) return Type_Access
   is
      Idx : Natural;
   begin
      if E = null then
         return null;
      end if;
      if E.Sem_Ty /= null then
         return E.Sem_Ty;
      end if;
      if E.Kind = E_Path and then Natural (E.Segments.Length) = 1 then
         Idx := Find_Binding (ST, SU.To_String (E.Segments.Last_Element));
         if Idx /= 0 then
            return ST.Bindings.Element (Idx).Ty;
         end if;
      end if;
      return null;
   end Type_Of_Expr;

   ----------------------------------------------------------------------
   --  String pool emission
   ----------------------------------------------------------------------

   procedure Emit_String_Pool
     (F : IO.File_Type; Pool : String_Pool)
   is
   begin
      if Pool.Is_Empty then
         return;
      end if;
      --  __TEXT,__const is a generic read-only section: the linker does
      --  not merge entries head-to-tail (unlike __cstring), so each Kurt
      --  string literal keeps its exact byte sequence. The bytes are
      --  laid out faithfully — a trailing NUL is present iff the source
      --  literal contains `\0`.
      IO.Put_Line (F, ".section __TEXT,__const");
      for I in Pool.First_Index .. Pool.Last_Index loop
         IO.Put_Line (F, "Lstr" & Img (I) & ":");
         declare
            B  : constant String := SU.To_String (Pool.Element (I).Bytes);
            Bs : Boolean := False;
         begin
            if B'Length = 0 then
               IO.Put_Line (F, "    .byte 0");
            else
               IO.Put (F, "    .byte ");
               for C of B loop
                  if Bs then
                     IO.Put (F, ", ");
                  end if;
                  IO.Put (F, Img (Integer (Character'Pos (C))));
                  Bs := True;
               end loop;
               IO.New_Line (F);
            end if;
         end;
      end loop;
   end Emit_String_Pool;

   ----------------------------------------------------------------------
   --  Shared lowering helpers used by the subunits below.
   ----------------------------------------------------------------------

   --  Materialise a non-negative integer immediate into a register via a
   --  movz / movk chain (each instruction sets one 16-bit lane).
   procedure Lower_Imm
     (F : IO.File_Type; Reg : Natural; V : Long_Long_Integer; Wide : Boolean)
   is
      R     : constant String := (if Wide then "x" else "w") & Img (Reg);
      Lanes : constant Natural := (if Wide then 4 else 2);
      Done  : Boolean := False;
   begin
      if V < 0 then
         raise Program_Error with
           "codegen: negative integer literals not yet supported";
      end if;
      if V = 0 then
         IO.Put_Line (F, "    mov     " & R & ", #0");
         return;
      end if;
      for I in 0 .. Lanes - 1 loop
         declare
            Lane  : constant Long_Long_Integer :=
              (V / (2 ** (16 * I))) mod 16#1_0000#;
            Shift : constant Natural := 16 * I;
         begin
            if Lane /= 0 then
               if not Done then
                  IO.Put_Line (F, "    movz    " & R & ", #" & Img (Lane)
                                  & (if Shift = 0 then ""
                                     else ", lsl #" & Img (Shift)));
                  Done := True;
               else
                  IO.Put_Line (F, "    movk    " & R & ", #" & Img (Lane)
                                  & ", lsl #" & Img (Shift));
               end if;
            end if;
         end;
      end loop;
   end Lower_Imm;

   --  §7.2.2 truthiness: reduce the contract value in x<Reg> to 0/1 —
   --  1 iff the discriminant equals the success variant's value. The
   --  register may hold a whole ≤8-byte payload aggregate, so the
   --  discriminant (at offset 0) is masked out first. Scratch: x12, x13.
   procedure Emit_Truthify
     (F : IO.File_Type; Reg : Natural; Ty : Type_Access)
   is
      XR  : constant String := "x" & Img (Reg);
      WR  : constant String := "w" & Img (Reg);
      DSz : constant Natural :=
        (if SU.To_String (Ty.Name) = "bool" then 1
         else Kurt.Layout.Enum_Disc_Size (SU.To_String (Ty.Name)));
      Src : constant String := (if DSz < 8 then "x12" else XR);
   begin
      if DSz < 8 then
         IO.Put_Line (F, "    and     x12, " & XR & ", #0x"
           & (case DSz is
                 when 1 => "ff", when 2 => "ffff",
                 when others => "ffffffff"));
      end if;
      Lower_Imm (F, 13, Contract_Succ_Val (Ty), True);
      IO.Put_Line (F, "    cmp     " & Src & ", x13");
      IO.Put_Line (F, "    cset    " & WR & ", eq");
   end Emit_Truthify;

   --  Copy Sz bytes from [Src_Base, #Src_Off] to [Dst_Base, #Dst_Off]
   --  through x9/w9, in 8-byte chunks with a sized tail (so reads never
   --  overrun a source that is not 8-byte padded, e.g. a payload alias).
   procedure Emit_Mem_Copy
     (F        : IO.File_Type;
      Src_Base : String; Src_Off : Natural;
      Dst_Base : String; Dst_Off : Natural;
      Sz       : Natural)
   is
      Done : Natural := 0;
   begin
      while Sz - Done >= 8 loop
         IO.Put_Line (F, "    ldr     x9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    str     x9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 8;
      end loop;
      if Sz - Done >= 4 then
         IO.Put_Line (F, "    ldr     w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    str     w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 4;
      end if;
      if Sz - Done >= 2 then
         IO.Put_Line (F, "    ldrh    w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    strh    w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
         Done := Done + 2;
      end if;
      if Sz - Done >= 1 then
         IO.Put_Line (F, "    ldrb    w9, [" & Src_Base & ", #"
                         & Img (Src_Off + Done) & "]");
         IO.Put_Line (F, "    strb    w9, [" & Dst_Base & ", #"
                         & Img (Dst_Off + Done) & "]");
      end if;
   end Emit_Mem_Copy;

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

   ----------------------------------------------------------------------
   --  Function lowering
   ----------------------------------------------------------------------

   --  16-byte aligned, generous enough for the bootstrap. Scalars take
   --  8 bytes; aggregates and arrays their rounded size. Overflow is
   --  detected after lowering (Next_Offset is checked against this).
   Frame_Bytes : constant Integer := 512;

   procedure Emit_Fn
     (F        : IO.File_Type;
      Fn       : Fn_Decl;
      Dyn_Syms : Dyn_Sym_Pkg.Vector;
      Fn_Rets  : Fn_Ret_Pkg.Vector;
      Str_Base : in out Natural)
   is
      --  §5.15: an `@symbol "name"` on an extern fn overrides the emitted
      --  external label; otherwise the identifier is used.
      Sym : constant String := "_"
        & (if SU.Length (Fn.Header.Symbol_Name) > 0
           then SU.To_String (Fn.Header.Symbol_Name)
           else SU.To_String (Fn.Header.Name));
      ST  : Lower_State;
   begin
      ST.Dyn_Syms := Dyn_Syms;
      ST.Fn_Rets  := Fn_Rets;
      ST.Fn_Name  := Fn.Header.Name;
      ST.Ret_Ty   := Fn.Header.Return_Type;
      --  Continue string-label numbering across functions so it matches
      --  the global order in which Collect_Strings filled the pool.
      ST.Next_Str_Idx := Str_Base;
      IO.New_Line (F);
      IO.Put_Line (F, ".globl " & Sym);
      IO.Put_Line (F, ".p2align 2");
      IO.Put_Line (F, Sym & ":");

      --  Prologue. The stp/ldp pre/post-index immediates only reach
      --  ±512, so the frame is carved with a separate sub/add (range
      --  0..4095) and x29/x30 saved at the frame base.
      IO.Put_Line (F, "    sub     sp, sp, #" & Img (Frame_Bytes));
      IO.Put_Line (F, "    stp     x29, x30, [sp]");
      IO.Put_Line (F, "    mov     x29, sp");

      ST.Epilogue_Lbl :=
        SU.To_Unbounded_String ("Lret_" & SU.To_String (Fn.Header.Name));

      --  AAPCS64: an indirect-class (sret) return arrives as a pointer in
      --  x8. Preserve it across the body for the S_Return copy.
      if Classify_Agg (ST.Ret_Ty) = Indirect then
         ST.Sret_Off := Integer (ST.Next_Offset);
         IO.Put_Line (F, "    str     x8, [x29, #"
                         & Img (ST.Next_Offset) & "]");
         ST.Next_Offset := ST.Next_Offset + 8;
      end if;

      --  Spill parameters into stack slots and register their bindings.
      --  AAPCS64: scalars and ≤8-byte aggregates take one x register,
      --  9–16-byte aggregates a register pair, and >16-byte aggregates
      --  arrive as a pointer to a caller-owned copy (copied into the
      --  frame so the binding behaves like any local).
      declare
         NGRN : Natural := 0;   --  next general-purpose register number
      begin
         for I in Fn.Header.Params.First_Index ..
                  Fn.Header.Params.Last_Index
         loop
            declare
               P   : constant Param     := Fn.Header.Params.Element (I);
               Cls : constant Agg_Class := Classify_Agg (P.Ty);
               Off : constant Natural   := ST.Next_Offset;
            begin
               case Cls is
                  when Not_Agg | One_Reg =>
                     IO.Put_Line (F, "    str     x" & Img (NGRN)
                                     & ", [x29, #" & Img (Off) & "]");
                     NGRN := NGRN + 1;
                     ST.Next_Offset := ST.Next_Offset + 8;
                  when Two_Regs =>
                     IO.Put_Line (F, "    str     x" & Img (NGRN)
                                     & ", [x29, #" & Img (Off) & "]");
                     IO.Put_Line (F, "    str     x" & Img (NGRN + 1)
                                     & ", [x29, #" & Img (Off + 8) & "]");
                     NGRN := NGRN + 2;
                     ST.Next_Offset := ST.Next_Offset + 16;
                  when Indirect =>
                     declare
                        Sz   : constant Natural := Sizeof (P.Ty);
                        Slot : constant Natural := ((Sz + 7) / 8) * 8;
                     begin
                        IO.Put_Line (F, "    mov     x10, x" & Img (NGRN));
                        Emit_Mem_Copy (F, "x10", 0, "x29", Off, Sz);
                        NGRN := NGRN + 1;
                        ST.Next_Offset := ST.Next_Offset + Slot;
                     end;
               end case;
               if SU.Length (P.Name) > 0 then
                  ST.Bindings.Append
                    ((Name => P.Name, Offset => Off, Ty => P.Ty));
               end if;
            end;
         end loop;
      end;

      --  Body
      for I in Fn.Body_Stmts.First_Index .. Fn.Body_Stmts.Last_Index loop
         Lower_Stmt (F, Fn.Body_Stmts.Element (I), ST);
      end loop;

      --  Epilogue
      IO.Put_Line (F, SU.To_String (ST.Epilogue_Lbl) & ":");
      IO.Put_Line (F, "    ldp     x29, x30, [sp]");
      IO.Put_Line (F, "    add     sp, sp, #" & Img (Frame_Bytes));
      IO.Put_Line (F, "    ret");

      if ST.Next_Offset > Natural (Frame_Bytes) then
         raise Program_Error with
           "codegen: fn '" & SU.To_String (Fn.Header.Name)
           & "' needs" & Natural'Image (ST.Next_Offset)
           & " bytes of frame (fixed frame is"
           & Integer'Image (Frame_Bytes) & ")";
      end if;

      Str_Base := ST.Next_Str_Idx;
   end Emit_Fn;

   ----------------------------------------------------------------------
   procedure Emit (U : Kurt.Parser.Translation_Unit; Out_Path : String) is
      F        : IO.File_Type;
      Pool     : String_Pool;
      Dyn_Syms : Dyn_Sym_Pkg.Vector;
      Fn_Rets  : Fn_Ret_Pkg.Vector;
   begin
      --  §9.5-6: publish trait metadata for the dispatch machinery.
      Unit_Traits := U.Traits;

      --  §5.4: publish the static-binding table for name resolution in
      --  the lowering passes.
      Unit_Statics := U.Statics;

      --  Return-type table for every internal fn, so call sites can
      --  classify aggregate returns (AAPCS64).
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         Fn_Rets.Append
           ((Name => U.Fns.Element (I).Header.Name,
             Ty   => U.Fns.Element (I).Header.Return_Type));
      end loop;

      --  Build the @dyn symbol table from every @dyn block in the unit.
      for I in U.Dyns.First_Index .. U.Dyns.Last_Index loop
         declare
            D : constant Dyn_Decl := U.Dyns.Element (I);
         begin
            for J in D.Items.First_Index .. D.Items.Last_Index loop
               declare
                  P : constant Fn_Proto := D.Items.Element (J);
               begin
                  Dyn_Syms.Append
                    ((Name        => P.Name,
                      Fixed_Args  => Natural (P.Params.Length),
                      Is_Variadic => P.Is_Variadic,
                      Symbol      => P.Symbol_Name));
               end;
            end loop;
         end;
      end loop;

      --  Pre-pass: collect every string literal in the order the
      --  lowering pass will encounter them.
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            Fn : constant Fn_Decl := U.Fns.Element (I);
         begin
            for J in Fn.Body_Stmts.First_Index .. Fn.Body_Stmts.Last_Index
            loop
               Collect_Strings_In_Stmt (Fn.Body_Stmts.Element (J), Pool);
            end loop;
         end;
      end loop;

      IO.Create (F, IO.Out_File, Out_Path);
      IO.Put_Line (F, "// kadayif bootstrap output");
      IO.Put_Line (F, "// target: arm64-apple-darwin");

      Emit_String_Pool (F, Pool);

      IO.Put_Line (F, ".section __TEXT,__text,regular,pure_instructions");

      declare
         Str_Base : Natural := 0;
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Emit_Fn (F, U.Fns.Element (I), Dyn_Syms, Fn_Rets, Str_Base);
         end loop;
      end;

      --  §9.5-6 dispatch tables. One static table per `impl T as Trait`,
      --  with the three-zone layout (header + method pointers). Zone B
      --  (supertraits) is empty in the bootstrap.
      if not U.Trait_Impls.Is_Empty then
         --  Shared no-op destructor — Zone A field 2 always holds a valid
         --  subroutine pointer (§9.6.1).
         IO.New_Line (F);
         IO.Put_Line (F, ".p2align 2");
         IO.Put_Line (F, "_kurt_noop_dtor:");
         IO.Put_Line (F, "    ret");

         IO.Put_Line (F, ".section __DATA,__const");
         for I in U.Trait_Impls.First_Index ..
                  U.Trait_Impls.Last_Index
         loop
            declare
               TI    : constant Trait_Impl := U.Trait_Impls.Element (I);
               TyN   : constant String := SU.To_String (TI.Ty_Name);
               TrN   : constant String := SU.To_String (TI.Trait_Name);
               Conc  : constant Type_Access :=
                 new AST_Type'(Kind => T_Named,
                               Name => TI.Ty_Name, Args => <>);
            begin
               IO.Put_Line (F, ".p2align 3");
               IO.Put_Line (F, "_Ldtable_" & TyN & "_" & TrN & ":");
               IO.Put_Line (F, "    .quad " & Img (Sizeof (Conc)));   --  [0]
               IO.Put_Line (F, "    .quad "
                 & Img (Kurt.Layout.Align_Of (Conc)));               --  [1]
               IO.Put_Line (F, "    .quad _kurt_noop_dtor");         --  [2]
               for T in U.Traits.First_Index .. U.Traits.Last_Index loop
                  if SU.To_String (U.Traits.Element (T).Name) = TrN then
                     declare
                        Tr : Trait_Decl renames U.Traits.Element (T);
                     begin
                        --  Zone B (§9.6.2): one reference per direct
                        --  supertrait, to that supertrait's own table for
                        --  the same concrete type.
                        for SI in Tr.Supertraits.First_Index ..
                                  Tr.Supertraits.Last_Index
                        loop
                           IO.Put_Line (F, "    .quad _Ldtable_" & TyN
                             & "_" & SU.To_String
                                       (Tr.Supertraits.Element (SI)));
                        end loop;
                        --  Zone C: one pointer per trait method, in
                        --  declaration order — `Type$method`.
                        for M in Tr.Methods.First_Index ..
                                 Tr.Methods.Last_Index
                        loop
                           IO.Put_Line (F, "    .quad _" & TyN & "$"
                             & SU.To_String
                                 (Tr.Methods.Element (M).Sig.Name));
                        end loop;
                     end;
                  end if;
               end loop;
            end;
         end loop;
      end if;

      --  §5.4 static objects: translation-time-initialized data words.
      if not U.Statics.Is_Empty then
         IO.New_Line (F);
         IO.Put_Line (F, ".section __DATA,__data");
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            declare
               function To_U64 is new Ada.Unchecked_Conversion
                 (Long_Float, Interfaces.Unsigned_64);
               function To_U32 is new Ada.Unchecked_Conversion
                 (Float, Interfaces.Unsigned_32);

               D    : constant Static_Decl := U.Statics.Element (I);
               Sz   : constant Natural := Sizeof (D.Ty);
               Neg  : constant Boolean :=
                 D.Init.Kind = E_Unary;
               Lit  : constant Expr_Access :=
                 (if Neg then D.Init.U_Operand else D.Init);
               Bits : Interfaces.Unsigned_64;
            begin
               case Lit.Kind is
                  when E_Int_Lit =>
                     declare
                        V : constant Long_Long_Integer :=
                          (if Neg then -Lit.Int_V else Lit.Int_V);
                     begin
                        Bits := Interfaces.Unsigned_64'Mod (V);
                     end;
                  when E_Float_Lit =>
                     declare
                        V : constant Long_Float :=
                          (if Neg then -Lit.Float_V else Lit.Float_V);
                     begin
                        if Sz = 4 then
                           Bits := Interfaces.Unsigned_64
                             (To_U32 (Float (V)));
                        else
                           Bits := To_U64 (V);
                        end if;
                     end;
                  when E_Bool_Lit =>
                     Bits := (if Lit.Bool_V then 1 else 0);
                  when others =>
                     raise Program_Error with
                       "codegen: unsupported static initializer";
               end case;
               --  Mask to the object width for the data directive.
               if Sz < 8 then
                  Bits := Interfaces."and"
                    (Bits,
                     Interfaces.Unsigned_64'Mod
                       (Long_Long_Integer (2) ** (8 * Sz) - 1));
               end if;
               IO.Put_Line (F, ".p2align "
                 & (case Sz is
                       when 1 => "0", when 2 => "1",
                       when 4 => "2", when others => "3"));
               IO.Put_Line (F, "_Kst_" & SU.To_String (D.Name) & ":");
               IO.Put_Line (F,
                 (case Sz is
                     when 1      => "    .byte ",
                     when 2      => "    .short ",
                     when 4      => "    .long ",
                     when others => "    .quad ")
                 & Interfaces.Unsigned_64'Image (Bits));
            end;
         end loop;
      end if;

      IO.Close (F);
   end Emit;

end Kurt.Codegen;
