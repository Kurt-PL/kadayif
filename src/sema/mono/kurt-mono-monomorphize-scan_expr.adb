separate (Kurt.Mono.Monomorphize)
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
         when E_Extract =>
            --  §7.2.3: `.id` (if any) is bound only within Ex_Fallback --
            --  Bound is a flat per-closure "locally introduced" set with
            --  no exit-scope popping elsewhere in this scanner either, so
            --  this mirrors the existing (slightly coarse) precision.
            Scan_Expr (E.Ex_Inner, Used, Bound);
            if SU.Length (E.Ex_Err) > 0 then
               Add_Once (Bound, E.Ex_Err);
            end if;
            Scan_Expr (E.Ex_Fallback, Used, Bound);
         when E_CAS =>
            Scan_Expr (E.CAS_Tgt, Used, Bound);
            Scan_Expr (E.CAS_Exp, Used, Bound);
            Scan_Expr (E.CAS_New, Used, Bound);
         when E_Array_Lit =>
            for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               Scan_Expr (E.AL_Elems.Element (I), Used, Bound);
            end loop;
            Scan_Expr (E.AL_Repeat_Expr, Used, Bound);
         when E_Dyn_Cast   => Scan_Expr (E.DC_Inner, Used, Bound);
         when E_Slice_Cast => Scan_Expr (E.SC_Inner, Used, Bound);
         when E_Destruct   => Scan_Expr (E.DT_Inner, Used, Bound);
         when E_Closure =>
            --  A nested closure's params are bound within it; its free
            --  references to our scope are uses we must also satisfy.
            for J in E.Clo_Params.First_Index ..
                     E.Clo_Params.Last_Index
            loop
               Add_Once (Bound, E.Clo_Params.Element (J).Name);
            end loop;
            Scan_Stmts (E.Clo_Body, Used, Bound);
         when E_Airside_Blk =>
            Scan_Stmts (E.AB_Stmts, Used, Bound);
         when E_Loop =>
            Scan_Stmts (E.Loop_Body, Used, Bound);
      end case;
   end Scan_Expr;
