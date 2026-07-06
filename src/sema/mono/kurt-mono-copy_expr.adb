separate (Kurt.Mono)
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
            R.Float_Suffix  := E.Float_Suffix;
            R.Float_Special := E.Float_Special;
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
         when E_Extract =>
            R.Ex_Inner    := C (E.Ex_Inner);
            R.Ex_Err      := E.Ex_Err;
            R.Ex_Fallback := C (E.Ex_Fallback);
         when E_CAS =>
            R.CAS_Tgt := C (E.CAS_Tgt);
            R.CAS_Exp := C (E.CAS_Exp);
            R.CAS_New := C (E.CAS_New);
            R.CAS_Ne  := E.CAS_Ne;
         when E_Array_Lit =>
            for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               R.AL_Elems.Append (C (E.AL_Elems.Element (I)));
            end loop;
            R.AL_Repeat      := E.AL_Repeat;
            R.AL_Repeat_Expr := C (E.AL_Repeat_Expr);
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
         when E_Airside_Blk =>
            R.AB_Stmts := Copy_Block (E.AB_Stmts, Params, Args);
            R.AB_Airside := E.AB_Airside;
            R.AB_Label   := E.AB_Label;
         when E_Loop =>
            R.Loop_Body := Copy_Block (E.Loop_Body, Params, Args);
      end case;
      return R;
   end Copy_Expr;
