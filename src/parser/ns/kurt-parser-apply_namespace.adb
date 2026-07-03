separate (Kurt.Parser)
   procedure Apply_Namespace
     (U           : in out Translation_Unit;
      NS_Prefix   : String;
      From        : Rename_From := (others => 1);
      Extra_Names : Path_Segments.Vector := Path_Segments.Empty_Vector;
      Super_Word  : String := "")
   is
      Names : Path_Segments.Vector := Extra_Names;

      function In_Names (Nm : String) return Boolean is
      begin
         for I in Names.First_Index .. Names.Last_Index loop
            if SU.To_String (Names.Element (I)) = Nm then
               return True;
            end if;
         end loop;
         return False;
      end In_Names;

      --  "area" -> "NS$area" (whole name declared); "point$area" ->
      --  "NS$point$area" (owner segment, up to the first '$', declared).
      function Mangle_Value (Nm : String) return String is
         Dollar : constant Natural := Ada.Strings.Fixed.Index (Nm, "$");
         Head   : constant String :=
           (if Dollar = 0 then Nm else Nm (Nm'First .. Dollar - 1));
      begin
         if In_Names (Head) then
            return NS_Prefix & "$" & Nm;
         end if;
         return Nm;
      end Mangle_Value;

      --  "point" -> "NS$point"; "selftype::Item" untouched (selftype is never a
      --  local declared name); "point::Assoc" -> "NS$point::Assoc".
      function Mangle_Type_Name (Nm : String) return String is
         Sep : constant Natural := Ada.Strings.Fixed.Index (Nm, "::");
      begin
         if Sep = 0 then
            if In_Names (Nm) then
               return NS_Prefix & "$" & Nm;
            end if;
            return Nm;
         end if;
         declare
            Head : constant String := Nm (Nm'First .. Sep - 1);
            Rest : constant String := Nm (Sep .. Nm'Last);
         begin
            if In_Names (Head) then
               return NS_Prefix & "$" & Head & Rest;
            end if;
            return Nm;
         end;
      end Mangle_Type_Name;

      procedure RT (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               T.Name := SU.To_Unbounded_String
                 (Mangle_Type_Name (SU.To_String (T.Name)));
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  RT (T.Args.Element (I));
               end loop;
            when T_Ref =>
               RT (T.Target);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  RT (T.Elems.Element (I));
               end loop;
            when T_Array =>
               RT (T.Elem);
            when T_Dyn =>
               T.Trait_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (T.Trait_Name)));
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  RT (T.Fn_Params.Element (I));
               end loop;
               RT (T.Fn_Ret);
         end case;
      end RT;

      procedure RE (E : Expr_Access);
      procedure RS (S : Stmt_Access);

      procedure RBlk (V : Stmt_Vectors.Vector) is
      begin
         for I in V.First_Index .. V.Last_Index loop
            RS (V.Element (I));
         end loop;
      end RBlk;

      procedure RPat (P : in out Pattern) is
      begin
         if not P.Path.Is_Empty then
            declare
               H : constant String := SU.To_String (P.Path.First_Element);
            begin
               if In_Names (H) then
                  P.Path.Replace_Element
                    (P.Path.First_Index,
                     SU.To_Unbounded_String (NS_Prefix & "$" & H));
               end if;
            end;
         end if;
      end RPat;

      procedure RE (E : Expr_Access) is
      begin
         if E = null then
            return;
         end if;
         case E.Kind is
            when E_Int_Lit | E_Float_Lit | E_Bool_Lit | E_String_Lit
               | E_Uninit =>
               null;
            when E_Path =>
               --  §10.6 a leading `super` / `srcroot` head. `super` (module
               --  close pass) steps the reference OUT of the scope being
               --  renamed — consume it and leave the remainder to an
               --  enclosing pass. `srcroot` (whole-file pass) names THIS
               --  pass's root — consume it and keep renaming the remainder.
               declare
                  Skip_Rename : Boolean := False;
               begin
                  if Super_Word /= ""
                    and then Natural (E.Segments.Length) >= 2
                    and then SU.To_String (E.Segments.First_Element)
                               = Super_Word
                  then
                     E.Segments.Delete_First;
                     Skip_Rename := Super_Word = "super";
                  end if;
                  if Skip_Rename then
                     null;
                  elsif Natural (E.Segments.Length) = 1 then
                     E.Segments.Replace_Element
                       (E.Segments.First_Index,
                        SU.To_Unbounded_String
                          (Mangle_Value
                             (SU.To_String (E.Segments.First_Element))));
                  elsif Natural (E.Segments.Length) >= 2 then
                     declare
                        H : constant String :=
                          SU.To_String (E.Segments.First_Element);
                     begin
                        if In_Names (H) then
                           E.Segments.Replace_Element
                             (E.Segments.First_Index,
                              SU.To_Unbounded_String (NS_Prefix & "$" & H));
                        end if;
                     end;
                  end if;
               end;
               for I in E.P_Type_Args.First_Index ..
                        E.P_Type_Args.Last_Index loop
                  RT (E.P_Type_Args.Element (I));
               end loop;
            when E_Field =>
               RE (E.F_Recv);
            when E_Call =>
               RE (E.C_Callee);
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  RE (E.C_Args.Element (I));
               end loop;
            when E_If =>
               RE (E.I_Cond); RE (E.I_Then); RE (E.I_Else);
            when E_Binary =>
               RE (E.B_Lhs); RE (E.B_Rhs);
            when E_Deref =>
               RE (E.D_Inner);
            when E_Struct_Lit =>
               E.SL_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.SL_Name)));
               for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index
               loop
                  RE (E.SL_Fields.Element (I).Val);
               end loop;
            when E_Variant_New =>
               E.VN_Enum := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.VN_Enum)));
               for I in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index
               loop
                  RE (E.VN_Fields.Element (I).Val);
               end loop;
            when E_Match =>
               RE (E.M_Scrut);
               for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
                  declare
                     A : Match_Arm := E.M_Arms.Element (I);
                  begin
                     RPat (A.Pat);
                     RE (A.Guard);
                     RE (A.Arm_Body);
                     E.M_Arms.Replace_Element (I, A);
                  end;
               end loop;
            when E_Cast =>
               RE (E.Cast_Inner);
               RT (E.Cast_Ty);
            when E_Unary =>
               RE (E.U_Operand);
            when E_Tuple_Lit =>
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index loop
                  RE (E.TL_Elems.Element (I));
               end loop;
            when E_Question =>
               RE (E.Q_Inner);
            when E_Ref =>
               RE (E.Rf_Place);
            when E_CAS =>
               RE (E.CAS_Tgt); RE (E.CAS_Exp); RE (E.CAS_New);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  RE (E.AL_Elems.Element (I));
               end loop;
            when E_Dyn_Cast =>
               RE (E.DC_Inner);
               E.DC_Conc := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.DC_Conc)));
               E.DC_Trait := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (E.DC_Trait)));
            when E_Slice_Cast =>
               RE (E.SC_Inner);
            when E_Type_Intrinsic =>
               RT (E.TI_Ty);
            when E_Closure =>
               for I in E.Clo_Params.First_Index .. E.Clo_Params.Last_Index
               loop
                  RT (E.Clo_Params.Element (I).Ty);
               end loop;
               RT (E.Clo_Ret);
               RBlk (E.Clo_Body);
            when E_Destruct =>
               RE (E.DT_Inner);
            when E_Airside_Blk =>
               RBlk (E.AB_Stmts);
            when E_Loop =>
               RBlk (E.Loop_Body);
         end case;
      end RE;

      procedure RS (S : Stmt_Access) is
      begin
         if S = null then
            return;
         end if;
         case S.Kind is
            when S_Return => RE (S.R_Val);
            when S_Expr    => RE (S.E_Val);
            when S_Airside_Block => RBlk (S.A_Stmts);
            when S_Let | S_Mut =>
               RT (S.L_Ty);
               RE (S.L_Init);
               if S.L_Is_Refut then
                  RPat (S.L_Refut_Pat);
               end if;
               RBlk (S.L_Else);
            when S_Assign =>
               RE (S.Asn_Lhs); RE (S.Asn_Rhs);
            when S_While =>
               RE (S.W_Cond);
               RBlk (S.W_Body);
               RBlk (S.W_Then);
               if S.W_Is_Let then
                  RPat (S.W_Let_Pat);
               end if;
            when S_If =>
               RE (S.SI_Cond);
               RBlk (S.SI_Then);
               RBlk (S.SI_Else);
               if S.SI_Is_Let then
                  RPat (S.SI_Let_Pat);
               end if;
            when S_Extract =>
               RE (S.X_Expr);
               RBlk (S.X_Else);
            when S_Break => RE (S.Brk_Val);
            when S_Continue => null;
            when S_Express => RE (S.Xp_Val);
            when S_Fence => null;
            when S_Trap => null;
            when S_Asm =>
               for I in S.Asm_In_Exprs.First_Index ..
                        S.Asm_In_Exprs.Last_Index loop
                  RE (S.Asm_In_Exprs.Element (I));
               end loop;
         end case;
      end RS;

      procedure RHeader (H : in out Fn_Header) is
      begin
         H.Name := SU.To_Unbounded_String
           (Mangle_Value (SU.To_String (H.Name)));
         for I in H.Params.First_Index .. H.Params.Last_Index loop
            RT (H.Params.Element (I).Ty);
         end loop;
         RT (H.Return_Type);
      end RHeader;
   begin
      --  1. Collect the bare top-level names U itself declares.
      for I in From.Structs .. U.Structs.Last_Index loop
         Names.Append (U.Structs.Element (I).Name);
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         Names.Append (U.Enums.Element (I).Name);
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         Names.Append (U.Traits.Element (I).Name);
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         Names.Append (U.Consts.Element (I).Name);
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         Names.Append (U.Statics.Element (I).Name);
      end loop;
      for I in From.Fns .. U.Fns.Last_Index loop
         if Ada.Strings.Fixed.Index
              (SU.To_String (U.Fns.Element (I).Header.Name), "$") = 0
         then
            Names.Append (U.Fns.Element (I).Header.Name);
         end if;
      end loop;
      for I in From.Gen_Fns .. U.Gen_Fns.Last_Index loop
         Names.Append (U.Gen_Fns.Element (I).Header.Name);
      end loop;
      for I in From.Gen_Methods .. U.Gen_Methods.Last_Index loop
         Names.Append (U.Gen_Methods.Element (I).Owner);
      end loop;

      --  2. Rename the declaration labels themselves.
      for I in From.Structs .. U.Structs.Last_Index loop
         declare
            D : Struct_Decl := U.Structs.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Structs.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         declare
            D : Enum_Decl := U.Enums.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Enums.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         declare
            D : Trait_Decl := U.Traits.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Traits.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         declare
            D : Const_Decl := U.Consts.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Consts.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         declare
            D : Static_Decl := U.Statics.Element (I);
         begin
            D.Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (D.Name)));
            U.Statics.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Trait_Impls .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl := U.Trait_Impls.Element (I);
         begin
            TI.Ty_Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (TI.Ty_Name)));
            TI.Trait_Name := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (TI.Trait_Name)));
            U.Trait_Impls.Replace_Element (I, TI);
         end;
      end loop;
      for I in From.Gen_Methods .. U.Gen_Methods.Last_Index loop
         declare
            GM : Gen_Method := U.Gen_Methods.Element (I);
         begin
            GM.Owner := SU.To_Unbounded_String
              (Mangle_Value (SU.To_String (GM.Owner)));
            if SU.Length (GM.Trait_Name) > 0 then
               GM.Trait_Name := SU.To_Unbounded_String
                 (Mangle_Value (SU.To_String (GM.Trait_Name)));
            end if;
            RHeader (GM.Method.Header);
            RBlk (GM.Method.Body_Stmts);
            U.Gen_Methods.Replace_Element (I, GM);
         end;
      end loop;

      --  3. Walk every reachable type/expr/stmt and rename references.
      for I in From.Fns .. U.Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Fns.Element (I);
         begin
            RHeader (F.Header);
            RBlk (F.Body_Stmts);
            U.Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in From.Gen_Fns .. U.Gen_Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Gen_Fns.Element (I);
         begin
            RHeader (F.Header);
            RBlk (F.Body_Stmts);
            U.Gen_Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in From.Structs .. U.Structs.Last_Index loop
         declare
            D : constant Struct_Decl := U.Structs.Element (I);
         begin
            for K in D.Fields.First_Index .. D.Fields.Last_Index loop
               RT (D.Fields.Element (K).Ty);
               RE (D.Fields.Element (K).Default);
            end loop;
            RBlk (D.Destruct_Block);
         end;
      end loop;
      for I in From.Enums .. U.Enums.Last_Index loop
         declare
            D : constant Enum_Decl := U.Enums.Element (I);
         begin
            for V in D.Variants.First_Index .. D.Variants.Last_Index loop
               for K in D.Variants.Element (V).Payload.First_Index ..
                        D.Variants.Element (V).Payload.Last_Index loop
                  RT (D.Variants.Element (V).Payload.Element (K).Ty);
                  RE (D.Variants.Element (V).Payload.Element (K).Default);
               end loop;
            end loop;
            RT (D.Discrim_Ty);
            RBlk (D.Destruct_Block);
         end;
      end loop;
      for I in From.Consts .. U.Consts.Last_Index loop
         RT (U.Consts.Element (I).Ty);
         RE (U.Consts.Element (I).Init);
      end loop;
      for I in From.Statics .. U.Statics.Last_Index loop
         RT (U.Statics.Element (I).Ty);
         RE (U.Statics.Element (I).Init);
      end loop;
      for I in From.Traits .. U.Traits.Last_Index loop
         declare
            D : Trait_Decl := U.Traits.Element (I);
         begin
            for K in D.Methods.First_Index .. D.Methods.Last_Index loop
               declare
                  M : Trait_Method := D.Methods.Element (K);
               begin
                  RHeader (M.Sig);
                  RBlk (M.Body_Stmts);
                  D.Methods.Replace_Element (K, M);
               end;
            end loop;
            for K in D.Consts.First_Index .. D.Consts.Last_Index loop
               RT (D.Consts.Element (K).Ty);
               RE (D.Consts.Element (K).Val);
            end loop;
            for K in D.Assoc_Types.First_Index ..
                     D.Assoc_Types.Last_Index loop
               RT (D.Assoc_Types.Element (K).Ty);
            end loop;
            U.Traits.Replace_Element (I, D);
         end;
      end loop;
      for I in From.Trait_Impls .. U.Trait_Impls.Last_Index loop
         declare
            TI : constant Trait_Impl := U.Trait_Impls.Element (I);
         begin
            for K in TI.Consts.First_Index .. TI.Consts.Last_Index loop
               RT (TI.Consts.Element (K).Ty);
               RE (TI.Consts.Element (K).Val);
            end loop;
            for K in TI.Assoc_Types.First_Index ..
                     TI.Assoc_Types.Last_Index loop
               RT (TI.Assoc_Types.Element (K).Ty);
            end loop;
         end;
      end loop;
      RBlk (U.Trap_Handler);
   end Apply_Namespace;
