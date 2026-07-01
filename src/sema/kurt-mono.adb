with Ada.Strings.Unbounded;
with Ada.Strings.Fixed;
with Ada.Strings;

package body Kurt.Mono is

   package SU renames Ada.Strings.Unbounded;
   use Kurt.Parser;

   ----------------------------------------------------------------------
   --  Mangle an instantiated type into a flat identifier.
   --     verdict.<si4, si4>  ->  "verdict$si4$si4"
   --     &raw ui1            ->  "praw_ui1"
   ----------------------------------------------------------------------
   function Mangle (T : Type_Access) return String is
   begin
      if T = null then
         return "void";
      end if;
      case T.Kind is
         when T_Named =>
            declare
               S : SU.Unbounded_String := T.Name;
            begin
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  SU.Append (S, "$");
                  SU.Append (S, Mangle (T.Args.Element (I)));
               end loop;
               return SU.To_String (S);
            end;
         when T_Ref =>
            return (case T.Sigil is
                       when R_Shared => "pref",
                       when R_Excl   => "pexc",
                       when R_Raw    => "praw")
                   & (if T.R_Volatile then "v" else "")
                   & (case T.R_Store is
                         when RS_None   => "",
                         when RS_Mut    => "m",
                         when RS_Atomic => "a",
                         when RS_Guard  => "g")
                   & "_" & Mangle (T.Target);
         when T_Tuple =>
            declare
               S : SU.Unbounded_String := SU.To_Unbounded_String ("tup");
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  SU.Append (S, "$");
                  SU.Append (S, Mangle (T.Elems.Element (I)));
               end loop;
               return SU.To_String (S);
            end;
         when T_Array =>
            declare
               Img : constant String := T.Len'Image;
            begin
               return "arr" & Img (Img'First + 1 .. Img'Last)
                 & "_" & Mangle (T.Elem);
            end;
         when T_Range =>
            return (if T.Rng_Inclusive then "rangein_" else "rangeex_")
              & Mangle (T.Rng_Elem);
         when T_Dyn =>
            return "dyn_" & SU.To_String (T.Trait_Name);
         when T_Fn =>
            declare
               S : SU.Unbounded_String := SU.To_Unbounded_String ("fnptr");
            begin
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  SU.Append (S, "$" & Mangle (T.Fn_Params.Element (I)));
               end loop;
               if T.Fn_Ret /= null then
                  SU.Append (S, "$ret$" & Mangle (T.Fn_Ret));
               end if;
               return SU.To_String (S);
            end;
      end case;
   end Mangle;

   ----------------------------------------------------------------------
   --  Deep copy of a type with generic parameters substituted by the
   --  corresponding argument. Params and Args are positionally matched.
   ----------------------------------------------------------------------
   function Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is
   begin
      if T = null then
         return null;
      end if;
      case T.Kind is
         when T_Named =>
            --  A bare name matching a parameter is replaced by the arg.
            if T.Args.Is_Empty then
               for I in Params.First_Index .. Params.Last_Index loop
                  if SU.To_String (Params.Element (I))
                       = SU.To_String (T.Name)
                  then
                     return Subst
                       (Args.Element (Args.First_Index + (I - Params.First_Index)),
                        Path_Segments.Empty_Vector, Type_Vectors.Empty_Vector);
                  end if;
               end loop;
            end if;
            --  Otherwise copy, substituting inside any nested arguments.
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Named);
            begin
               R.Name := T.Name;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  R.Args.Append (Subst (T.Args.Element (I), Params, Args));
               end loop;
               return R;
            end;
         when T_Ref =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Ref);
            begin
               R.Sigil      := T.Sigil;
               R.R_Volatile := T.R_Volatile;
               R.R_Store    := T.R_Store;
               R.Target     := Subst (T.Target, Params, Args);
               return R;
            end;
         when T_Tuple =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Tuple);
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  R.Elems.Append (Subst (T.Elems.Element (I), Params, Args));
               end loop;
               return R;
            end;
         when T_Array =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Array);
            begin
               R.Elem := Subst (T.Elem, Params, Args);
               R.Len  := T.Len;
               return R;
            end;
         when T_Range =>
            return new AST_Type'
              (Kind          => T_Range,
               Rng_Inclusive => T.Rng_Inclusive,
               Rng_Elem      => Subst (T.Rng_Elem, Params, Args));
         when T_Dyn =>
            return T;   --  trait object carries no substitutable parts
         when T_Fn =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Fn);
            begin
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  R.Fn_Params.Append
                    (Subst (T.Fn_Params.Element (I), Params, Args));
               end loop;
               R.Fn_Ret      := Subst (T.Fn_Ret, Params, Args);
               R.Fn_Variadic := T.Fn_Variadic;
               R.Fn_Airside  := T.Fn_Airside;
               R.Fn_Never    := T.Fn_Never;
               R.Fn_Extern   := T.Fn_Extern;
               return R;
            end;
      end case;
   end Subst;

   ----------------------------------------------------------------------
   --  Deep copy of an expression / statement tree with generic
   --  parameters substituted in every embedded type annotation. Used by
   --  fn-template instantiation (§5.9.3): the template itself was
   --  already checked under type erasure, so the copy is a semantics-
   --  preserving specialisation.
   ----------------------------------------------------------------------

   function Copy_Expr
     (E      : Expr_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Expr_Access;

   function Copy_Stmt
     (S      : Stmt_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Access;

   function Copy_Block
     (V      : Stmt_Vectors.Vector;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Vectors.Vector
   is
      R : Stmt_Vectors.Vector;
   begin
      for I in V.First_Index .. V.Last_Index loop
         R.Append (Copy_Stmt (V.Element (I), Params, Args));
      end loop;
      return R;
   end Copy_Block;

   function Copy_Expr
     (E      : Expr_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Expr_Access
   is
      function C (X : Expr_Access) return Expr_Access is
        (Copy_Expr (X, Params, Args));
      R : Expr_Access;
   begin
      if E = null then
         return null;
      end if;
      R := new Expr_Node (Kind => E.Kind);
      case E.Kind is
         when E_Int_Lit =>
            R.Int_V      := E.Int_V;
            R.Int_Suffix := E.Int_Suffix;
         when E_Float_Lit =>
            R.Float_V      := E.Float_V;
            R.Float_Suffix := E.Float_Suffix;
         when E_Bool_Lit =>
            R.Bool_V := E.Bool_V;
         when E_String_Lit =>
            R.Str_Bytes := E.Str_Bytes;
         when E_Path =>
            R.Segments := E.Segments;
            --  §9.3.2: a 2-segment `T::NAME` whose head names a generic
            --  parameter is specialised by substituting the type argument
            --  (its mangled concrete name) for the head segment.
            if Natural (R.Segments.Length) = 2 then
               for I in Params.First_Index .. Params.Last_Index loop
                  if SU.To_String (Params.Element (I))
                       = SU.To_String (R.Segments.First_Element)
                  then
                     R.Segments.Replace_Element
                       (R.Segments.First_Index,
                        SU.To_Unbounded_String
                          (Mangle (Args.Element
                             (Args.First_Index
                              + (I - Params.First_Index)))));
                  end if;
               end loop;
            end if;
            for I in E.P_Type_Args.First_Index ..
                     E.P_Type_Args.Last_Index
            loop
               R.P_Type_Args.Append
                 (Subst (E.P_Type_Args.Element (I), Params, Args));
            end loop;
         when E_Field =>
            R.F_Recv := C (E.F_Recv);
            R.F_Name := E.F_Name;
         when E_Call =>
            R.C_Callee := C (E.C_Callee);
            for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
               R.C_Args.Append (C (E.C_Args.Element (I)));
            end loop;
         when E_If =>
            R.I_Cond := C (E.I_Cond);
            R.I_Then := C (E.I_Then);
            R.I_Else := C (E.I_Else);
         when E_Binary =>
            R.B_Op  := E.B_Op;
            R.B_Lhs := C (E.B_Lhs);
            R.B_Rhs := C (E.B_Rhs);
         when E_Deref =>
            R.D_Inner := C (E.D_Inner);
         when E_Struct_Lit =>
            R.SL_Name := E.SL_Name;
            for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index loop
               R.SL_Fields.Append
                 ((Name => E.SL_Fields.Element (I).Name,
                   Val  => C (E.SL_Fields.Element (I).Val)));
            end loop;
         when E_Variant_New =>
            R.VN_Enum    := E.VN_Enum;
            R.VN_Variant := E.VN_Variant;
            for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index loop
               R.VN_Fields.Append
                 ((Name => E.VN_Fields.Element (I).Name,
                   Val  => C (E.VN_Fields.Element (I).Val)));
            end loop;
         when E_Match =>
            R.M_Scrut := C (E.M_Scrut);
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               R.M_Arms.Append
                 ((Pat      => E.M_Arms.Element (I).Pat,
                   Guard    => C (E.M_Arms.Element (I).Guard),
                   Arm_Body => C (E.M_Arms.Element (I).Arm_Body)));
            end loop;
         when E_Cast =>
            R.Cast_Inner := C (E.Cast_Inner);
            R.Cast_Ty    := Subst (E.Cast_Ty, Params, Args);
            R.Cast_Disc  := E.Cast_Disc;
            R.Cast_Bang  := E.Cast_Bang;
         when E_Unary =>
            R.U_Op      := E.U_Op;
            R.U_Operand := C (E.U_Operand);
         when E_Tuple_Lit =>
            for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
               R.TL_Elems.Append (C (E.TL_Elems.Element (I)));
            end loop;
         when E_Question =>
            R.Q_Inner := C (E.Q_Inner);
         when E_Ref =>
            R.Rf_Sigil    := E.Rf_Sigil;
            R.Rf_Volatile := E.Rf_Volatile;
            R.Rf_Store    := E.Rf_Store;
            R.Rf_Place    := C (E.Rf_Place);
         when E_CAS =>
            R.CAS_Tgt := C (E.CAS_Tgt);
            R.CAS_Exp := C (E.CAS_Exp);
            R.CAS_New := C (E.CAS_New);
            R.CAS_Ne  := E.CAS_Ne;
         when E_Array_Lit =>
            for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               R.AL_Elems.Append (C (E.AL_Elems.Element (I)));
            end loop;
            R.AL_Repeat := E.AL_Repeat;
         when E_Dyn_Cast =>
            R.DC_Inner := C (E.DC_Inner);
            R.DC_Conc  := E.DC_Conc;
            R.DC_Trait := E.DC_Trait;
         when E_Slice_Cast =>
            R.SC_Inner := C (E.SC_Inner);
            R.SC_Len   := E.SC_Len;
         when E_Type_Intrinsic =>
            R.TI_Ty    := Subst (E.TI_Ty, Params, Args);
            R.TI_Op    := E.TI_Op;
            R.TI_Field := E.TI_Field;
         when E_Uninit =>
            null;
         when E_Closure =>
            --  §9.9 closures are lowered to their own subroutine; copy the
            --  fields directly (shallow over the body, which is shared).
            R.Clo_Params   := E.Clo_Params;
            R.Clo_Ret      := E.Clo_Ret;
            R.Clo_Body     := E.Clo_Body;
            R.Clo_Xfer     := E.Clo_Xfer;
            R.Clo_Fn_Name  := E.Clo_Fn_Name;
            R.Clo_Caps     := E.Clo_Caps;
            R.Clo_Env_Name := E.Clo_Env_Name;
         when E_Destruct =>
            R.DT_Inner := C (E.DT_Inner);
            R.DT_Undo  := E.DT_Undo;
         when E_Range =>
            R.Rg_Lo        := C (E.Rg_Lo);
            R.Rg_Hi        := C (E.Rg_Hi);
            R.Rg_Inclusive := E.Rg_Inclusive;
      end case;
      return R;
   end Copy_Expr;

   function Copy_Stmt
     (S      : Stmt_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Access
   is
      function C (X : Expr_Access) return Expr_Access is
        (Copy_Expr (X, Params, Args));
      R : Stmt_Access;
   begin
      if S = null then
         return null;
      end if;
      R := new Stmt_Node (Kind => S.Kind);
      case S.Kind is
         when S_Return =>
            R.R_Val := C (S.R_Val);
         when S_Expr =>
            R.E_Val := C (S.E_Val);
         when S_Airside_Block =>
            R.A_Stmts := Copy_Block (S.A_Stmts, Params, Args);
         when S_Let | S_Mut =>
            R.L_Name        := S.L_Name;
            R.L_Ty          := Subst (S.L_Ty, Params, Args);
            R.L_Init        := C (S.L_Init);
            R.L_Tuple_Names := S.L_Tuple_Names;
            R.L_Is_Refut    := S.L_Is_Refut;
            R.L_Refut_Pat   := S.L_Refut_Pat;
            R.L_Else        := Copy_Block (S.L_Else, Params, Args);
         when S_Assign =>
            R.Asn_Lhs := C (S.Asn_Lhs);
            R.Asn_Rhs := C (S.Asn_Rhs);
         when S_While =>
            R.W_Cond  := C (S.W_Cond);
            R.W_Body  := Copy_Block (S.W_Body, Params, Args);
            R.W_Then  := Copy_Block (S.W_Then, Params, Args);
            R.W_Label := S.W_Label;
            R.W_Is_Let  := S.W_Is_Let;
            R.W_Let_Pat := S.W_Let_Pat;
            R.W_Is_Contract := S.W_Is_Contract;
            R.W_Succ_Bind   := S.W_Succ_Bind;
         when S_If =>
            R.SI_Cond        := C (S.SI_Cond);
            R.SI_Then        := Copy_Block (S.SI_Then, Params, Args);
            R.SI_Else        := Copy_Block (S.SI_Else, Params, Args);
            R.SI_Is_Contract := S.SI_Is_Contract;
            R.SI_Succ_Bind   := S.SI_Succ_Bind;
            R.SI_Fail_Bind   := S.SI_Fail_Bind;
            R.SI_Is_Let      := S.SI_Is_Let;
            R.SI_Let_Pat     := S.SI_Let_Pat;
         when S_Extract =>
            R.X_Bind := S.X_Bind;
            R.X_Expr := C (S.X_Expr);
            R.X_Err  := S.X_Err;
            R.X_Else := Copy_Block (S.X_Else, Params, Args);
            R.X_Is_Place := S.X_Is_Place;
         when S_Break =>
            R.Brk_Val   := C (S.Brk_Val);
            R.Brk_Label := S.Brk_Label;
         when S_Continue =>
            R.Cont_Label := S.Cont_Label;
         when S_Express =>
            R.Xp_Val := C (S.Xp_Val);
         when S_Fence =>
            R.Fn_Guard := S.Fn_Guard;
            R.Fn_Form  := S.Fn_Form;
         when S_Trap =>
            null;   --  §7.10: no fields to copy
         when S_Asm =>
            R.Asm_Body      := S.Asm_Body;   --  §6.11 raw body
            R.Asm_In_Regs   := S.Asm_In_Regs;
            R.Asm_Out_Regs  := S.Asm_Out_Regs;
            R.Asm_Out_Names := S.Asm_Out_Names;
            R.Asm_Clobbers  := S.Asm_Clobbers;
            for I in S.Asm_In_Exprs.First_Index ..
                     S.Asm_In_Exprs.Last_Index loop
               R.Asm_In_Exprs.Append (C (S.Asm_In_Exprs.Element (I)));
            end loop;
      end case;
      return R;
   end Copy_Stmt;

   ----------------------------------------------------------------------
   procedure Monomorphize (U : in out Kurt.Parser.Translation_Unit) is

      --  Generic templates lifted out of the unit; concrete declarations
      --  (including freshly generated instances) stay in U.
      Gen_Structs : Struct_Vectors.Vector;
      Gen_Enums   : Enum_Vectors.Vector;
      Generated   : Path_Segments.Vector;  --  mangled names already emitted
      Clo_Seq     : Natural := 0;          --  §9.9 closure-lift counter

      function Already_Generated (Name : String) return Boolean is
      begin
         for I in Generated.First_Index .. Generated.Last_Index loop
            if SU.To_String (Generated.Element (I)) = Name then
               return True;
            end if;
         end loop;
         return False;
      end Already_Generated;

      function Find_Gen_Struct (Name : String; D : out Struct_Decl)
         return Boolean is
      begin
         for I in Gen_Structs.First_Index .. Gen_Structs.Last_Index loop
            if SU.To_String (Gen_Structs.Element (I).Name) = Name then
               D := Gen_Structs.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Gen_Struct;

      function Find_Gen_Enum (Name : String; D : out Enum_Decl)
         return Boolean is
      begin
         for I in Gen_Enums.First_Index .. Gen_Enums.Last_Index loop
            if SU.To_String (Gen_Enums.Element (I).Name) = Name then
               D := Gen_Enums.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Gen_Enum;

      --  §5.9 fn templates live in U.Gen_Fns (lifted below); the sema
      --  pass checks them once under type erasure.
      function Find_Gen_Fn (Name : String; D : out Fn_Decl)
         return Boolean is
      begin
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            if SU.To_String (U.Gen_Fns.Element (I).Header.Name) = Name then
               D := U.Gen_Fns.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Gen_Fn;

      --  Forward declarations: generic-impl method instantiation (defined
      --  near the end) both drives and is driven by the type/block visitors.
      procedure Visit_Type (T : Type_Access);
      procedure Visit_Block (V : Stmt_Vectors.Vector);
      procedure Instantiate_Owner_Methods
        (Orig, Mangled : String; Args : Type_Vectors.Vector);

      --  In-place rewrite of the `self_t` placeholder to a concrete type
      --  name (the mangled owner instance). Distinct from Subst, which
      --  substitutes generic *parameters*; `self_t` is neither.
      procedure Subst_Self_Name (T : Type_Access; Concrete : String) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               if SU.To_String (T.Name) = "self_t" then
                  T.Name := SU.To_Unbounded_String (Concrete);
               end if;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  Subst_Self_Name (T.Args.Element (I), Concrete);
               end loop;
            when T_Ref =>
               Subst_Self_Name (T.Target, Concrete);
            when T_Array =>
               Subst_Self_Name (T.Elem, Concrete);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  Subst_Self_Name (T.Elems.Element (I), Concrete);
               end loop;
            when T_Range =>
               Subst_Self_Name (T.Rng_Elem, Concrete);
            when T_Dyn =>
               null;
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  Subst_Self_Name (T.Fn_Params.Element (I), Concrete);
               end loop;
               Subst_Self_Name (T.Fn_Ret, Concrete);
         end case;
      end Subst_Self_Name;

      --  Generate the concrete declaration for one instance, if needed.
      procedure Ensure_Instance (Inst : Type_Access; Mangled : String) is
         Orig : constant String := SU.To_String (Inst.Name);
         SD   : Struct_Decl;
         ED   : Enum_Decl;
      begin
         if Already_Generated (Mangled) then
            return;
         end if;

         if Find_Gen_Struct (Orig, SD) then
            if Natural (SD.Generic_Params.Length)
                 /= Natural (Inst.Args.Length)
            then
               raise Mono_Error with
                 "wrong number of type arguments for '" & Orig & "'";
            end if;
            declare
               New_D : Struct_Decl;
            begin
               New_D.Name := SU.To_Unbounded_String (Mangled);
               for I in SD.Fields.First_Index .. SD.Fields.Last_Index loop
                  New_D.Fields.Append
                    ((Name    => SD.Fields.Element (I).Name,
                      Ty      => Subst (SD.Fields.Element (I).Ty,
                                        SD.Generic_Params, Inst.Args),
                      Default => Copy_Expr (SD.Fields.Element (I).Default,
                                            SD.Generic_Params, Inst.Args),
                      Is_Mut     => SD.Fields.Element (I).Is_Mut,
                      Is_Pub     => SD.Fields.Element (I).Is_Pub,
                      Is_Airside => SD.Fields.Element (I).Is_Airside));
               end loop;
               U.Structs.Append (New_D);
            end;
            Generated.Append (SU.To_Unbounded_String (Mangled));

         elsif Find_Gen_Enum (Orig, ED) then
            if Natural (ED.Generic_Params.Length)
                 /= Natural (Inst.Args.Length)
            then
               raise Mono_Error with
                 "wrong number of type arguments for '" & Orig & "'";
            end if;
            declare
               New_D : Enum_Decl;
            begin
               New_D.Name        := SU.To_Unbounded_String (Mangled);
               New_D.Is_Contract := ED.Is_Contract;
               for I in ED.Variants.First_Index .. ED.Variants.Last_Index
               loop
                  declare
                     V  : constant Enum_Variant := ED.Variants.Element (I);
                     NV : Enum_Variant;
                  begin
                     NV.Name    := V.Name;
                     NV.Value   := V.Value;
                     NV.Is_Wild := V.Is_Wild;
                     for J in V.Payload.First_Index .. V.Payload.Last_Index
                     loop
                        NV.Payload.Append
                          ((Name    => V.Payload.Element (J).Name,
                            Ty      => Subst (V.Payload.Element (J).Ty,
                                              ED.Generic_Params, Inst.Args),
                            Default => Copy_Expr
                                         (V.Payload.Element (J).Default,
                                          ED.Generic_Params, Inst.Args),
                            others => <>));
                     end loop;
                     New_D.Variants.Append (NV);
                  end;
               end loop;
               U.Enums.Append (New_D);
            end;
            Generated.Append (SU.To_Unbounded_String (Mangled));

         else
            raise Mono_Error with
              "instantiation of unknown generic type '" & Orig & "'";
         end if;
      end Ensure_Instance;

      --  Visit a type: generate instances for any generic application and
      --  rewrite the node in place to the mangled concrete name.
      procedure Visit_Type (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Ref =>
               Visit_Type (T.Target);
            when T_Array =>
               Visit_Type (T.Elem);
            when T_Range =>
               Visit_Type (T.Rng_Elem);   --  intrinsic; no instantiation
            when T_Dyn =>
               null;
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  Visit_Type (T.Fn_Params.Element (I));
               end loop;
               Visit_Type (T.Fn_Ret);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  Visit_Type (T.Elems.Element (I));
               end loop;
            when T_Named =>
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  Visit_Type (T.Args.Element (I));   --  innermost first
               end loop;
               --  §4.5 verdict is an intrinsic built-in (like bool): it is
               --  recognised by name + args directly by Kurt.Layout, never
               --  monomorphised into a generated enum. Leave it as
               --  T_Named "verdict" with its Args intact.
               if SU.To_String (T.Name) = "verdict" then
                  null;
               elsif not T.Args.Is_Empty then
                  declare
                     Orig_N     : constant String := SU.To_String (T.Name);
                     Mangled    : constant String := Mangle (T);
                     Saved_Args : constant Type_Vectors.Vector := T.Args;
                  begin
                     Ensure_Instance (T, Mangled);
                     --  §9.1/§9.4: specialise the owner's generic-impl
                     --  methods for this instance (e.g. Box$si4$get).
                     Instantiate_Owner_Methods (Orig_N, Mangled, Saved_Args);
                     T.Name := SU.To_Unbounded_String (Mangled);
                     T.Args.Clear;
                  end;
               end if;
         end case;
      end Visit_Type;

      procedure Visit_Stmt (S : Stmt_Access);
      procedure Visit_Expr (E : Expr_Access);

      ----------------------------------------------------------------
      --  §9.9.3 capture analysis (syntactic, names only)
      ----------------------------------------------------------------

      function In_Set
        (V : Path_Segments.Vector; S : SU.Unbounded_String) return Boolean
      is
         Target : constant String := SU.To_String (S);
      begin
         for I in V.First_Index .. V.Last_Index loop
            if SU.To_String (V.Element (I)) = Target then
               return True;
            end if;
         end loop;
         return False;
      end In_Set;

      procedure Add_Once
        (V : in out Path_Segments.Vector; S : SU.Unbounded_String) is
      begin
         if not In_Set (V, S) then
            V.Append (S);
         end if;
      end Add_Once;

      function Is_Top_Level (S : SU.Unbounded_String) return Boolean is
         N : constant String := SU.To_String (S);
      begin
         for F of U.Fns loop
            if SU.To_String (F.Header.Name) = N then return True; end if;
         end loop;
         for F of U.Gen_Fns loop
            if SU.To_String (F.Header.Name) = N then return True; end if;
         end loop;
         for Cn of U.Consts loop
            if SU.To_String (Cn.Name) = N then return True; end if;
         end loop;
         for St of U.Statics loop
            if SU.To_String (St.Name) = N then return True; end if;
         end loop;
         return False;
      end Is_Top_Level;

      --  Accumulate the single-segment names read (Used) and the names a
      --  block binds (Bound). A capture is a Used name that is neither Bound
      --  nor a closure parameter nor a top-level declaration.
      procedure Scan_Expr
        (E : Expr_Access; Used, Bound : in out Path_Segments.Vector);

      procedure Scan_Stmts
        (V : Stmt_Vectors.Vector; Used, Bound : in out Path_Segments.Vector)
      is
      begin
         for I in V.First_Index .. V.Last_Index loop
            declare
               S : constant Stmt_Access := V.Element (I);
            begin
               case S.Kind is
                  when S_Return    => Scan_Expr (S.R_Val, Used, Bound);
                  when S_Expr      => Scan_Expr (S.E_Val, Used, Bound);
                  when S_Express   => Scan_Expr (S.Xp_Val, Used, Bound);
                  when S_Airside_Block =>
                     Scan_Stmts (S.A_Stmts, Used, Bound);
                  when S_Let | S_Mut =>
                     Scan_Expr (S.L_Init, Used, Bound);
                     Add_Once (Bound, S.L_Name);
                     for J in S.L_Tuple_Names.First_Index ..
                              S.L_Tuple_Names.Last_Index
                     loop
                        Add_Once (Bound, S.L_Tuple_Names.Element (J));
                     end loop;
                     if S.L_Is_Refut then
                        Scan_Stmts (S.L_Else, Used, Bound);
                        for J in S.L_Refut_Pat.Bindings.First_Index ..
                                 S.L_Refut_Pat.Bindings.Last_Index
                        loop
                           Add_Once (Bound, S.L_Refut_Pat.Bindings.Element (J));
                        end loop;
                     end if;
                  when S_Assign =>
                     Scan_Expr (S.Asn_Lhs, Used, Bound);
                     Scan_Expr (S.Asn_Rhs, Used, Bound);
                  when S_While =>
                     Scan_Expr (S.W_Cond, Used, Bound);
                     Scan_Stmts (S.W_Body, Used, Bound);
                     Scan_Stmts (S.W_Then, Used, Bound);
                  when S_If =>
                     Scan_Expr (S.SI_Cond, Used, Bound);
                     if SU.Length (S.SI_Succ_Bind) > 0 then
                        Add_Once (Bound, S.SI_Succ_Bind);
                     end if;
                     if SU.Length (S.SI_Fail_Bind) > 0 then
                        Add_Once (Bound, S.SI_Fail_Bind);
                     end if;
                     for J in S.SI_Let_Pat.Bindings.First_Index ..
                              S.SI_Let_Pat.Bindings.Last_Index
                     loop
                        Add_Once (Bound, S.SI_Let_Pat.Bindings.Element (J));
                     end loop;
                     Scan_Stmts (S.SI_Then, Used, Bound);
                     Scan_Stmts (S.SI_Else, Used, Bound);
                  when S_Extract =>
                     Scan_Expr (S.X_Expr, Used, Bound);
                     Add_Once (Bound, S.X_Bind);
                     if SU.Length (S.X_Err) > 0 then
                        Add_Once (Bound, S.X_Err);
                     end if;
                     Scan_Stmts (S.X_Else, Used, Bound);
                  when S_Break     => Scan_Expr (S.Brk_Val, Used, Bound);
                  when S_Continue | S_Fence | S_Trap | S_Asm => null;
               end case;
            end;
         end loop;
      end Scan_Stmts;

      procedure Scan_Expr
        (E : Expr_Access; Used, Bound : in out Path_Segments.Vector) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_String_Lit
               | E_Uninit | E_Type_Intrinsic =>
               null;
            when E_Path =>
               if Natural (E.Segments.Length) = 1 then
                  Add_Once (Used, E.Segments.First_Element);
               end if;
            when E_Field   => Scan_Expr (E.F_Recv, Used, Bound);
            when E_Call =>
               Scan_Expr (E.C_Callee, Used, Bound);
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  Scan_Expr (E.C_Args.Element (I), Used, Bound);
               end loop;
            when E_If =>
               Scan_Expr (E.I_Cond, Used, Bound);
               Scan_Expr (E.I_Then, Used, Bound);
               Scan_Expr (E.I_Else, Used, Bound);
            when E_Binary =>
               Scan_Expr (E.B_Lhs, Used, Bound);
               Scan_Expr (E.B_Rhs, Used, Bound);
            when E_Deref    => Scan_Expr (E.D_Inner, Used, Bound);
            when E_Struct_Lit =>
               for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index loop
                  Scan_Expr (E.SL_Fields.Element (I).Val, Used, Bound);
               end loop;
            when E_Variant_New =>
               for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index loop
                  Scan_Expr (E.VN_Fields.Element (I).Val, Used, Bound);
               end loop;
            when E_Match =>
               Scan_Expr (E.M_Scrut, Used, Bound);
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  declare
                     A : constant Match_Arm := E.M_Arms.Element (I);
                  begin
                     for J in A.Pat.Bindings.First_Index ..
                              A.Pat.Bindings.Last_Index
                     loop
                        Add_Once (Bound, A.Pat.Bindings.Element (J));
                     end loop;
                     if SU.Length (A.Pat.Bind_Name) > 0 then
                        Add_Once (Bound, A.Pat.Bind_Name);
                     end if;
                     for J in A.Pat.Slice_Elems.First_Index ..
                              A.Pat.Slice_Elems.Last_Index loop
                        if A.Pat.Slice_Elems.Element (J).Kind = SE_Bind then
                           Add_Once
                             (Bound, A.Pat.Slice_Elems.Element (J).Name);
                        end if;
                     end loop;
                     if A.Guard /= null then
                        Scan_Expr (A.Guard, Used, Bound);
                     end if;
                     Scan_Expr (A.Arm_Body, Used, Bound);
                  end;
               end loop;
            when E_Cast      => Scan_Expr (E.Cast_Inner, Used, Bound);
            when E_Unary     => Scan_Expr (E.U_Operand, Used, Bound);
            when E_Tuple_Lit =>
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
                  Scan_Expr (E.TL_Elems.Element (I), Used, Bound);
               end loop;
            when E_Question  => Scan_Expr (E.Q_Inner, Used, Bound);
            when E_Ref       => Scan_Expr (E.Rf_Place, Used, Bound);
            when E_CAS =>
               Scan_Expr (E.CAS_Tgt, Used, Bound);
               Scan_Expr (E.CAS_Exp, Used, Bound);
               Scan_Expr (E.CAS_New, Used, Bound);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  Scan_Expr (E.AL_Elems.Element (I), Used, Bound);
               end loop;
            when E_Dyn_Cast   => Scan_Expr (E.DC_Inner, Used, Bound);
            when E_Slice_Cast => Scan_Expr (E.SC_Inner, Used, Bound);
            when E_Destruct   => Scan_Expr (E.DT_Inner, Used, Bound);
            when E_Range =>
               Scan_Expr (E.Rg_Lo, Used, Bound);
               Scan_Expr (E.Rg_Hi, Used, Bound);
            when E_Closure =>
               --  A nested closure's params are bound within it; its free
               --  references to our scope are uses we must also satisfy.
               for J in E.Clo_Params.First_Index ..
                        E.Clo_Params.Last_Index
               loop
                  Add_Once (Bound, E.Clo_Params.Element (J).Name);
               end loop;
               Scan_Stmts (E.Clo_Body, Used, Bound);
         end case;
      end Scan_Expr;

      procedure Visit_Block (V : Stmt_Vectors.Vector) is
      begin
         for I in V.First_Index .. V.Last_Index loop
            Visit_Stmt (V.Element (I));
         end loop;
      end Visit_Block;

      --  §5.9.3: generate the monomorphised instance of fn template
      --  `Orig` for the (already visited / concrete) type arguments and
      --  return its mangled name. The instance is a plain fn appended to
      --  U.Fns; its body is immediately re-visited so nested generic
      --  type uses and fn invocations instantiate transitively.
      function Ensure_Fn_Instance
        (Orig : String; Type_Args : Type_Vectors.Vector) return String
      is
         Key : constant Type_Access := new AST_Type (Kind => T_Named);
         TD  : Fn_Decl;
      begin
         Key.Name := SU.To_Unbounded_String (Orig);
         Key.Args := Type_Args;
         declare
            Mangled : constant String := Mangle (Key);
         begin
            if Already_Generated (Mangled) then
               return Mangled;
            end if;
            if not Find_Gen_Fn (Orig, TD) then
               raise Mono_Error with
                 "instantiation of unknown generic subroutine '"
                 & Orig & "'";
            end if;
            if Natural (TD.Header.Generic_Params.Length)
                 /= Natural (Type_Args.Length)
            then
               raise Mono_Error with
                 "wrong number of type arguments for '" & Orig & "'";
            end if;
            --  Mark first: a recursive generic fn instantiates itself.
            Generated.Append (SU.To_Unbounded_String (Mangled));

            declare
               PNames : Path_Segments.Vector;
               New_Fn : Fn_Decl;
            begin
               for I in TD.Header.Generic_Params.First_Index ..
                        TD.Header.Generic_Params.Last_Index
               loop
                  PNames.Append (TD.Header.Generic_Params.Element (I).Name);
               end loop;

               New_Fn.Header := TD.Header;
               New_Fn.Header.Name := SU.To_Unbounded_String (Mangled);
               New_Fn.Header.Generic_Params.Clear;
               New_Fn.Header.Params.Clear;
               for I in TD.Header.Params.First_Index ..
                        TD.Header.Params.Last_Index
               loop
                  New_Fn.Header.Params.Append
                    ((Name => TD.Header.Params.Element (I).Name,
                      Ty   => Subst (TD.Header.Params.Element (I).Ty,
                                     PNames, Type_Args),
                      Is_Mut => TD.Header.Params.Element (I).Is_Mut));
               end loop;
               New_Fn.Header.Return_Type :=
                 Subst (TD.Header.Return_Type, PNames, Type_Args);
               New_Fn.Body_Stmts :=
                 Copy_Block (TD.Body_Stmts, PNames, Type_Args);

               --  Re-visit: instantiate generic types / nested generic
               --  invocations now appearing with concrete arguments.
               for I in New_Fn.Header.Params.First_Index ..
                        New_Fn.Header.Params.Last_Index
               loop
                  Visit_Type (New_Fn.Header.Params.Element (I).Ty);
               end loop;
               Visit_Type (New_Fn.Header.Return_Type);
               Visit_Block (New_Fn.Body_Stmts);

               U.Fns.Append (New_Fn);
            end;
            return Mangled;
         end;
      end Ensure_Fn_Instance;

      procedure Visit_Expr (E : Expr_Access) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_String_Lit
               | E_Uninit =>
               null;
            when E_Path =>
               for I in E.P_Type_Args.First_Index ..
                        E.P_Type_Args.Last_Index
               loop
                  Visit_Type (E.P_Type_Args.Element (I));
               end loop;
            when E_Field =>
               Visit_Expr (E.F_Recv);
            when E_Call =>
               Visit_Expr (E.C_Callee);
               --  §5.9.2 explicit instantiation `f.<T, ...>(args)`.
               if E.C_Callee.Kind = E_Path
                 and then Natural (E.C_Callee.Segments.Length) = 1
                 and then not E.C_Callee.P_Type_Args.Is_Empty
               then
                  declare
                     Mangled : constant String := Ensure_Fn_Instance
                       (SU.To_String (E.C_Callee.Segments.Last_Element),
                        E.C_Callee.P_Type_Args);
                  begin
                     E.C_Callee.Segments.Clear;
                     E.C_Callee.Segments.Append
                       (SU.To_Unbounded_String (Mangled));
                     E.C_Callee.P_Type_Args.Clear;
                  end;
               end if;
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  Visit_Expr (E.C_Args.Element (I));
               end loop;
            when E_If =>
               Visit_Expr (E.I_Cond);
               Visit_Expr (E.I_Then);
               Visit_Expr (E.I_Else);
            when E_Binary =>
               Visit_Expr (E.B_Lhs);
               Visit_Expr (E.B_Rhs);
            when E_Deref =>
               Visit_Expr (E.D_Inner);
            when E_Struct_Lit =>
               for I in E.SL_Fields.First_Index ..
                        E.SL_Fields.Last_Index
               loop
                  Visit_Expr (E.SL_Fields.Element (I).Val);
               end loop;
            when E_Range =>
               Visit_Expr (E.Rg_Lo);
               Visit_Expr (E.Rg_Hi);
            when E_Destruct =>
               Visit_Expr (E.DT_Inner);
            when E_Closure =>
               --  §9.9 lift the closure to a fresh top-level subroutine so it
               --  follows the normal sema/codegen path. The expression keeps
               --  a pointer to it (Clo_Fn_Name). A non-capturing closure
               --  behaves exactly like a subroutine value (fn pointer). A
               --  capturing closure additionally gets an anonymous capture
               --  struct `$clo_N$env` (one field per captured binding) and a
               --  hidden first parameter `self : &$clo_N$env`; references to
               --  the captures are reached by prefixing the body with
               --  `let cap = self.cap;` (capture by copy, §9.9.3).
               Clo_Seq := Clo_Seq + 1;
               declare
                  Nm : constant String :=
                    "$clo_" & Ada.Strings.Fixed.Trim
                                (Natural'Image (Clo_Seq), Ada.Strings.Left);
                  D     : Fn_Decl;
                  Used  : Path_Segments.Vector;
                  Bound : Path_Segments.Vector;
               begin
                  E.Clo_Fn_Name := SU.To_Unbounded_String (Nm);
                  --  capture set = used − bound − params − top-level
                  Scan_Stmts (E.Clo_Body, Used, Bound);
                  for P of E.Clo_Params loop
                     Add_Once (Bound, P.Name);
                  end loop;
                  E.Clo_Caps.Clear;
                  for I in Used.First_Index .. Used.Last_Index loop
                     declare
                        Cap : constant SU.Unbounded_String :=
                          Used.Element (I);
                     begin
                        if not In_Set (Bound, Cap)
                          and then not Is_Top_Level (Cap)
                        then
                           E.Clo_Caps.Append ((Name => Cap, Ty => null));
                        end if;
                     end;
                  end loop;

                  D.Header.Name := E.Clo_Fn_Name;
                  D.Header.Is_Closure := True;

                  if not E.Clo_Caps.Is_Empty then
                     --  Capturing: synthesise the env struct, the `self`
                     --  parameter, and the capture-loading prefix.
                     E.Clo_Env_Name := SU.To_Unbounded_String (Nm & "$env");
                     declare
                        Env   : Struct_Decl;
                        Self_T : constant Type_Access :=
                          new AST_Type (Kind => T_Ref);
                        Prefix : Stmt_Vectors.Vector;
                     begin
                        Self_T.Sigil  := R_Shared;
                        Self_T.Target := new AST_Type (Kind => T_Named);
                        Self_T.Target.Name := E.Clo_Env_Name;
                        D.Header.Params.Append
                          ((Name => SU.To_Unbounded_String ("self"),
                            Ty   => Self_T, Is_Mut => False));
                        for C of E.Clo_Caps loop
                           Env.Fields.Append
                             ((Name => C.Name, Ty => null, Default => null,
                               others => <>));
                           declare
                              LS : constant Stmt_Access :=
                                new Stmt_Node (Kind => S_Let);
                              FE : constant Expr_Access :=
                                new Expr_Node (Kind => E_Field);
                              SR : constant Expr_Access :=
                                new Expr_Node (Kind => E_Path);
                           begin
                              SR.Segments.Append
                                (SU.To_Unbounded_String ("self"));
                              FE.F_Recv := SR;
                              FE.F_Name := C.Name;
                              LS.L_Name := C.Name;
                              LS.L_Ty   := null;
                              LS.L_Init := FE;
                              Prefix.Append (LS);
                           end;
                        end loop;
                        Env.Name     := E.Clo_Env_Name;
                        Env.Clo_Lift := E.Clo_Fn_Name;
                        U.Structs.Append (Env);
                        for S of E.Clo_Body loop
                           Prefix.Append (S);
                        end loop;
                        E.Clo_Body := Prefix;
                     end;
                  end if;

                  for P of E.Clo_Params loop
                     D.Header.Params.Append
                       ((Name => P.Name, Ty => P.Ty, Is_Mut => False));
                  end loop;
                  D.Header.Return_Type := E.Clo_Ret;   --  null => inferred
                  D.Body_Stmts := E.Clo_Body;
                  Visit_Block (E.Clo_Body);            --  nested closures
                  U.Fns.Append (D);
               end;
            when E_Variant_New =>
               for I in E.VN_Fields.First_Index ..
                        E.VN_Fields.Last_Index
               loop
                  Visit_Expr (E.VN_Fields.Element (I).Val);
               end loop;
            when E_Match =>
               Visit_Expr (E.M_Scrut);
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  Visit_Expr (E.M_Arms.Element (I).Guard);
                  Visit_Expr (E.M_Arms.Element (I).Arm_Body);
               end loop;
            when E_Cast =>
               Visit_Expr (E.Cast_Inner);
               Visit_Type (E.Cast_Ty);
            when E_Unary =>
               Visit_Expr (E.U_Operand);
            when E_Tuple_Lit =>
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
                  Visit_Expr (E.TL_Elems.Element (I));
               end loop;
            when E_Question =>
               Visit_Expr (E.Q_Inner);
            when E_Ref =>
               Visit_Expr (E.Rf_Place);
            when E_CAS =>
               Visit_Expr (E.CAS_Tgt);
               Visit_Expr (E.CAS_Exp);
               Visit_Expr (E.CAS_New);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  Visit_Expr (E.AL_Elems.Element (I));
               end loop;
            when E_Dyn_Cast =>
               Visit_Expr (E.DC_Inner);
            when E_Slice_Cast =>
               Visit_Expr (E.SC_Inner);
            when E_Type_Intrinsic =>
               Visit_Type (E.TI_Ty);
         end case;
      end Visit_Expr;

      procedure Visit_Stmt (S : Stmt_Access) is
      begin
         case S.Kind is
            when S_Let | S_Mut =>
               Visit_Type (S.L_Ty);
               Visit_Expr (S.L_Init);
            when S_Return =>
               Visit_Expr (S.R_Val);
            when S_Expr =>
               Visit_Expr (S.E_Val);
            when S_Assign =>
               Visit_Expr (S.Asn_Lhs);
               Visit_Expr (S.Asn_Rhs);
            when S_While =>
               Visit_Expr (S.W_Cond);
               Visit_Block (S.W_Body);
               Visit_Block (S.W_Then);
            when S_If =>
               Visit_Expr (S.SI_Cond);
               Visit_Block (S.SI_Then);
               Visit_Block (S.SI_Else);
            when S_Extract =>
               Visit_Expr (S.X_Expr);
               Visit_Block (S.X_Else);
            when S_Airside_Block =>
               Visit_Block (S.A_Stmts);
            when S_Break =>
               Visit_Expr (S.Brk_Val);
            when S_Express =>
               Visit_Expr (S.Xp_Val);
            when S_Continue | S_Fence | S_Trap | S_Asm =>
               null;
         end case;
      end Visit_Stmt;

      --  §9.1/§9.4: specialise every generic-impl method whose owner is the
      --  generic type `Orig` for the concrete instance `Mangled` (with type
      --  arguments `Args`). Produces `Mangled$method` concrete subroutines —
      --  exactly the names static method dispatch resolves to — substituting
      --  the impl parameters and rewriting `self_t` to the owner instance.
      procedure Instantiate_Owner_Methods
        (Orig, Mangled : String; Args : Type_Vectors.Vector)
      is
      begin
         for GI in U.Gen_Methods.First_Index ..
                   U.Gen_Methods.Last_Index
         loop
            declare
               GM : constant Gen_Method := U.Gen_Methods.Element (GI);
            begin
               if SU.To_String (GM.Owner) = Orig then
                  declare
                     Bare     : constant String :=
                       SU.To_String (GM.Method.Header.Name);
                     New_Name : constant String := Mangled & "$" & Bare;
                     PNames   : Path_Segments.Vector;
                     New_Fn   : Fn_Decl;
                  begin
                     if not Already_Generated (New_Name) then
                        if Natural (GM.Gen_Params.Length)
                             /= Natural (Args.Length)
                        then
                           raise Mono_Error with
                             "wrong number of type arguments for impl of '"
                             & Orig & "'";
                        end if;
                        Generated.Append
                          (SU.To_Unbounded_String (New_Name));
                        for I in GM.Gen_Params.First_Index ..
                                 GM.Gen_Params.Last_Index
                        loop
                           PNames.Append (GM.Gen_Params.Element (I).Name);
                        end loop;

                        New_Fn.Header := GM.Method.Header;
                        New_Fn.Header.Name :=
                          SU.To_Unbounded_String (New_Name);
                        New_Fn.Header.Generic_Params.Clear;
                        New_Fn.Header.Params.Clear;
                        for K in GM.Method.Header.Params.First_Index ..
                                 GM.Method.Header.Params.Last_Index
                        loop
                           New_Fn.Header.Params.Append
                             ((Name => GM.Method.Header.Params
                                         .Element (K).Name,
                               Ty   => Subst
                                 (GM.Method.Header.Params.Element (K).Ty,
                                  PNames, Args),
                               Is_Mut => GM.Method.Header.Params
                                           .Element (K).Is_Mut));
                        end loop;
                        New_Fn.Header.Return_Type :=
                          Subst (GM.Method.Header.Return_Type,
                                 PNames, Args);
                        New_Fn.Body_Stmts :=
                          Copy_Block (GM.Method.Body_Stmts, PNames, Args);

                        --  self_t -> the concrete owner instance.
                        for K in New_Fn.Header.Params.First_Index ..
                                 New_Fn.Header.Params.Last_Index
                        loop
                           Subst_Self_Name
                             (New_Fn.Header.Params.Element (K).Ty, Mangled);
                        end loop;
                        Subst_Self_Name (New_Fn.Header.Return_Type, Mangled);

                        --  Re-visit for transitive instantiation.
                        for K in New_Fn.Header.Params.First_Index ..
                                 New_Fn.Header.Params.Last_Index
                        loop
                           Visit_Type (New_Fn.Header.Params.Element (K).Ty);
                        end loop;
                        Visit_Type (New_Fn.Header.Return_Type);
                        Visit_Block (New_Fn.Body_Stmts);

                        U.Fns.Append (New_Fn);
                     end if;
                  end;
               end if;
            end;
         end loop;
      end Instantiate_Owner_Methods;

   begin
      --  §9.3.4 default methods: for every `impl Type as Trait` that omits
      --  a trait method carrying a default body, synthesise the concrete
      --  `Type$method` from the default (self_t → Type). The synthesised
      --  fns are plain concrete subroutines and follow the normal
      --  sema/codegen path. Done before the generic lift so they can use,
      --  and be used by, generic instantiation.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI    : Trait_Impl renames U.Trait_Impls.Element (I);
            Conc  : constant Type_Access := new AST_Type (Kind => T_Named);
            SelfP : Path_Segments.Vector;   --  ["self_t"]
            Args1 : Type_Vectors.Vector;    --  [Conc]
         begin
            Conc.Name := TI.Ty_Name;
            SelfP.Append (SU.To_Unbounded_String ("self_t"));
            Args1.Append (Conc);

            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name)
                    = SU.To_String (TI.Trait_Name)
               then
                  declare
                     Tr : Trait_Decl renames U.Traits.Element (T);
                  begin
                     for M in Tr.Methods.First_Index ..
                              Tr.Methods.Last_Index
                     loop
                        declare
                           TM       : Trait_Method renames
                             Tr.Methods.Element (M);
                           MName    : constant String :=
                             SU.To_String (TM.Sig.Name);
                           Provided : Boolean := False;
                        begin
                           for P in TI.Methods.First_Index ..
                                    TI.Methods.Last_Index
                           loop
                              if SU.To_String (TI.Methods.Element (P))
                                   = MName
                              then
                                 Provided := True;
                              end if;
                           end loop;

                           if TM.Has_Body and then not Provided then
                              declare
                                 New_Fn : Fn_Decl;
                              begin
                                 New_Fn.Header := TM.Sig;
                                 --  §9.2.1 trait-qualified mangling: the
                                 --  synthesised default lowers to
                                 --  `Type$Trait$method`.
                                 New_Fn.Header.Name :=
                                   SU.To_Unbounded_String
                                     (SU.To_String (TI.Ty_Name) & "$"
                                      & SU.To_String (TI.Trait_Name) & "$"
                                      & MName);
                                 New_Fn.Header.Params.Clear;
                                 for K in TM.Sig.Params.First_Index ..
                                          TM.Sig.Params.Last_Index
                                 loop
                                    New_Fn.Header.Params.Append
                                      ((Name => TM.Sig.Params.Element (K)
                                                  .Name,
                                        Ty   => Subst
                                          (TM.Sig.Params.Element (K).Ty,
                                           SelfP, Args1),
                                        Is_Mut => TM.Sig.Params.Element (K)
                                                    .Is_Mut));
                                 end loop;
                                 New_Fn.Header.Return_Type :=
                                   Subst (TM.Sig.Return_Type,
                                          SelfP, Args1);
                                 New_Fn.Body_Stmts :=
                                   Copy_Block (TM.Body_Stmts,
                                               SelfP, Args1);
                                 U.Fns.Append (New_Fn);
                              end;
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            end loop;
         end;
      end loop;

      --  Lift generic templates out of U; keep only concrete declarations.
      declare
         Keep_S : Struct_Vectors.Vector;
         Keep_E : Enum_Vectors.Vector;
      begin
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            if U.Structs.Element (I).Generic_Params.Is_Empty then
               Keep_S.Append (U.Structs.Element (I));
            else
               Gen_Structs.Append (U.Structs.Element (I));
            end if;
         end loop;
         U.Structs := Keep_S;

         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if U.Enums.Element (I).Generic_Params.Is_Empty then
               Keep_E.Append (U.Enums.Element (I));
            else
               Gen_Enums.Append (U.Enums.Element (I));
            end if;
         end loop;
         U.Enums := Keep_E;
      end;

      --  §4.5 verdict is intrinsic (see Visit_Type / Kurt.Layout): it is
      --  recognised by name and never monomorphised, so no template here.

      --  Lift §5.9 fn templates into U.Gen_Fns. They are checked once by
      --  Kurt.Sema under type erasure and never reach codegen; only the
      --  instances generated below (back into U.Fns) are lowered.
      declare
         Keep_F : Fn_Vectors.Vector;
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            if U.Fns.Element (I).Header.Generic_Params.Is_Empty then
               Keep_F.Append (U.Fns.Element (I));
            else
               U.Gen_Fns.Append (U.Fns.Element (I));
            end if;
         end loop;
         U.Fns := Keep_F;
      end;

      --  Walk every type annotation in the unit and instantiate.
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            Fn : constant Fn_Decl := U.Fns.Element (I);
         begin
            for J in Fn.Header.Params.First_Index ..
                     Fn.Header.Params.Last_Index
            loop
               Visit_Type (Fn.Header.Params.Element (J).Ty);
            end loop;
            Visit_Type (Fn.Header.Return_Type);
            Visit_Type (Fn.Header.Variadic_Ty);
            Visit_Block (Fn.Body_Stmts);
         end;
      end loop;

      --  Field/payload types of concrete declarations may also name an
      --  instance (e.g. a struct field of type list.<si4>).
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         for J in U.Structs.Element (I).Fields.First_Index ..
                  U.Structs.Element (I).Fields.Last_Index
         loop
            Visit_Type (U.Structs.Element (I).Fields.Element (J).Ty);
         end loop;
      end loop;
   end Monomorphize;

end Kurt.Mono;
