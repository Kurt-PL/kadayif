separate (Kurt.Mono.Monomorphize)
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
         when E_Destruct =>
            Visit_Expr (E.DT_Inner);
         when E_Airside_Blk =>
            Visit_Block (E.AB_Stmts);
         when E_Loop =>
            Visit_Block (E.Loop_Body);
         when E_Closure =>
            --  Re-entrancy: a closure already lifted by a previous
            --  monomorphisation round keeps its subroutine (whose body is
            --  walked via U.Fns); re-lifting would duplicate it.
            if SU.Length (E.Clo_Fn_Name) > 0 then
               return;
            end if;
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
         when E_Extract =>
            Visit_Expr (E.Ex_Inner);
            Visit_Expr (E.Ex_Fallback);
         when E_CAS =>
            Visit_Expr (E.CAS_Tgt);
            Visit_Expr (E.CAS_Exp);
            Visit_Expr (E.CAS_New);
         when E_Array_Lit =>
            for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               Visit_Expr (E.AL_Elems.Element (I));
            end loop;
            Visit_Expr (E.AL_Repeat_Expr);
         when E_Dyn_Cast =>
            Visit_Expr (E.DC_Inner);
         when E_Slice_Cast =>
            Visit_Expr (E.SC_Inner);
         when E_Type_Intrinsic =>
            Visit_Type (E.TI_Ty);
      end case;
   end Visit_Expr;
