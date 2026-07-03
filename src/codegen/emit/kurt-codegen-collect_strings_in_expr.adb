separate (Kurt.Codegen)
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
         when E_Destruct =>
            Collect_Strings_In_Expr (E.DT_Inner, Pool);
         when E_Airside_Blk =>
            for I in E.AB_Stmts.First_Index .. E.AB_Stmts.Last_Index loop
               Collect_Strings_In_Stmt (E.AB_Stmts.Element (I), Pool);
            end loop;
         when E_Loop =>
            for I in E.Loop_Body.First_Index .. E.Loop_Body.Last_Index loop
               Collect_Strings_In_Stmt (E.Loop_Body.Element (I), Pool);
            end loop;
         when E_Closure =>
            null;  --  §9.9 the body's strings are collected when the
                   --  synthesised closure subroutine is itself processed
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
               if E.M_Arms.Element (I).Guard /= null then
                  Collect_Strings_In_Expr (E.M_Arms.Element (I).Guard, Pool);
               end if;
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
