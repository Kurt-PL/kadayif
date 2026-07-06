separate (Kurt.Mono)
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

      --  §9.3 generic trait templates (lifted below, like Gen_Structs).
      Gen_Traits : Trait_Vectors.Vector;

      function Find_Gen_Trait (Name : String; D : out Trait_Decl)
         return Boolean is
      begin
         for I in Gen_Traits.First_Index .. Gen_Traits.Last_Index loop
            if SU.To_String (Gen_Traits.Element (I).Name) = Name then
               D := Gen_Traits.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Gen_Trait;

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

      --  In-place rewrite of the `selftype` placeholder to a concrete type
      --  name (the mangled owner instance). Distinct from Subst, which
      --  substitutes generic *parameters*; `selftype` is neither.
      procedure Subst_Self_Name (T : Type_Access; Concrete : String) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               if SU.To_String (T.Name) = "selftype" then
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
            when T_Dyn =>
               null;
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  Subst_Self_Name (T.Fn_Params.Element (I), Concrete);
               end loop;
               Subst_Self_Name (T.Fn_Ret, Concrete);
         end case;
      end Subst_Self_Name;

      --  §9.8.5 destruct-family bounds cannot be validated here (the
      --  layout model that answers Satisfies_Destruct is registered only
      --  after monomorphisation), so each obligation is recorded on the
      --  unit for Kurt.Sema to validate.
      procedure Record_Bound_Checks
        (Params : Generic_Param_Vectors.Vector;
         Args   : Type_Vectors.Vector;
         Ctx    : String)
      is
      begin
         for I in Params.First_Index .. Params.Last_Index loop
            for J in Params.Element (I).Bounds.First_Index ..
                     Params.Element (I).Bounds.Last_Index
            loop
               declare
                  B : constant String :=
                    SU.To_String (Params.Element (I).Bounds.Element (J));
               begin
                  if B = "destruct" or else B = "!destruct" then
                     U.Bound_Checks.Append
                       ((Bound => SU.To_Unbounded_String (B),
                         Ty    => Args.Element
                                    (Args.First_Index
                                     + (I - Params.First_Index)),
                         Param => Params.Element (I).Name,
                         Ctx   => SU.To_Unbounded_String (Ctx)));
                  end if;
               end;
            end loop;
         end loop;
      end Record_Bound_Checks;

      --  Generate the concrete declaration for one instance, if needed.
      procedure Ensure_Instance (Inst : Type_Access; Mangled : String) is separate;

      --  Visit a type: generate instances for any generic application and
      --  rewrite the node in place to the mangled concrete name.
      procedure Visit_Type (T : Type_Access) is separate;

      --  §9.3 generate the concrete trait declaration for one instance of
      --  a generic trait (`Pair.<si4>` -> trait `Pair$si4`), substituting
      --  the type arguments through method signatures, default bodies,
      --  associated consts/types. Returns the mangled name.
      function Ensure_Trait_Instance
        (Orig : String; Args : Type_Vectors.Vector) return String
      is
         Key : constant Type_Access := new AST_Type (Kind => T_Named);
         TD  : Trait_Decl;
      begin
         Key.Name := SU.To_Unbounded_String (Orig);
         Key.Args := Args;
         declare
            Mangled : constant String := Mangle (Key);
         begin
            if Already_Generated (Mangled) then
               return Mangled;
            end if;
            if not Find_Gen_Trait (Orig, TD) then
               raise Mono_Error with
                 "instantiation of unknown generic trait '" & Orig & "'";
            end if;
            if Natural (TD.Generic_Params.Length) /= Natural (Args.Length)
            then
               raise Mono_Error with
                 "wrong number of type arguments for trait '" & Orig & "'";
            end if;
            Generated.Append (SU.To_Unbounded_String (Mangled));
            Record_Bound_Checks (TD.Generic_Params, Args, Orig);
            declare
               PNames : Path_Segments.Vector;
               New_D  : Trait_Decl;
            begin
               for I in TD.Generic_Params.First_Index ..
                        TD.Generic_Params.Last_Index
               loop
                  PNames.Append (TD.Generic_Params.Element (I).Name);
               end loop;
               New_D.Name        := SU.To_Unbounded_String (Mangled);
               New_D.Is_Pub      := TD.Is_Pub;
               New_D.Supertraits := TD.Supertraits;
               for I in TD.Methods.First_Index .. TD.Methods.Last_Index
               loop
                  declare
                     M  : constant Trait_Method := TD.Methods.Element (I);
                     NM : Trait_Method;
                  begin
                     NM.Sig := M.Sig;
                     NM.Sig.Params.Clear;
                     for K in M.Sig.Params.First_Index ..
                              M.Sig.Params.Last_Index
                     loop
                        NM.Sig.Params.Append
                          ((Name => M.Sig.Params.Element (K).Name,
                            Ty   => Subst (M.Sig.Params.Element (K).Ty,
                                           PNames, Args),
                            Is_Mut => M.Sig.Params.Element (K).Is_Mut));
                     end loop;
                     NM.Sig.Return_Type :=
                       Subst (M.Sig.Return_Type, PNames, Args);
                     NM.Has_Body := M.Has_Body;
                     if M.Has_Body then
                        NM.Body_Stmts :=
                          Copy_Block (M.Body_Stmts, PNames, Args);
                     end if;
                     New_D.Methods.Append (NM);
                  end;
               end loop;
               for I in TD.Consts.First_Index .. TD.Consts.Last_Index loop
                  New_D.Consts.Append
                    ((Name    => TD.Consts.Element (I).Name,
                      Ty      => Subst (TD.Consts.Element (I).Ty,
                                        PNames, Args),
                      Val     => Copy_Expr (TD.Consts.Element (I).Val,
                                            PNames, Args),
                      Has_Val => TD.Consts.Element (I).Has_Val));
               end loop;
               for I in TD.Assoc_Types.First_Index ..
                        TD.Assoc_Types.Last_Index
               loop
                  New_D.Assoc_Types.Append
                    ((Name => TD.Assoc_Types.Element (I).Name,
                      Ty   => Subst (TD.Assoc_Types.Element (I).Ty,
                                     PNames, Args)));
               end loop;
               U.Traits.Append (New_D);
            end;
            return Mangled;
         end;
      end Ensure_Trait_Instance;

      --  Rewrite one written generic-trait reference (name + argument
      --  list) to its mangled concrete instance, instantiating it on
      --  first sight. No-op when Args is empty (a plain trait name).
      procedure Rewrite_Trait_Ref
        (Name : in out SU.Unbounded_String;
         Args : in out Type_Vectors.Vector)
      is
      begin
         if Args.Is_Empty then
            return;
         end if;
         for I in Args.First_Index .. Args.Last_Index loop
            Visit_Type (Args.Element (I));
         end loop;
         Name := SU.To_Unbounded_String
           (Ensure_Trait_Instance (SU.To_String (Name), Args));
         Args.Clear;
      end Rewrite_Trait_Ref;

      --  Whether type T mentions any of the names in Params (a generic
      --  parameter of the enclosing template) — such a bound argument
      --  cannot be resolved to a concrete trait instance here.
      function Mentions_Param
        (T : Type_Access; Params : Generic_Param_Vectors.Vector)
         return Boolean
      is
      begin
         if T = null then
            return False;
         end if;
         case T.Kind is
            when T_Named =>
               for P of Params loop
                  if SU.To_String (P.Name) = SU.To_String (T.Name) then
                     return True;
                  end if;
               end loop;
               for A of T.Args loop
                  if Mentions_Param (A, Params) then
                     return True;
                  end if;
               end loop;
               return False;
            when T_Ref =>
               return Mentions_Param (T.Target, Params);
            when T_Array =>
               return Mentions_Param (T.Elem, Params);
            when T_Tuple =>
               for A of T.Elems loop
                  if Mentions_Param (A, Params) then
                     return True;
                  end if;
               end loop;
               return False;
            when T_Dyn =>
               return False;
            when T_Fn =>
               for A of T.Fn_Params loop
                  if Mentions_Param (A, Params) then
                     return True;
                  end if;
               end loop;
               return Mentions_Param (T.Fn_Ret, Params);
         end case;
      end Mentions_Param;

      --  §9.3 rewrite every generic-trait bound (`U: Pair.<si4>`) in a
      --  generic parameter list to its concrete instance. Bound arguments
      --  that mention a parameter of the same list (`U: Pair.<A>`) are a
      --  documented bootstrap cut.
      procedure Rewrite_Param_Bounds
        (Params : in out Generic_Param_Vectors.Vector; Ctx : String)
      is
      begin
         for K in Params.First_Index .. Params.Last_Index loop
            declare
               P : Generic_Param := Params.Element (K);
               Changed : Boolean := False;
            begin
               for J in P.Bound_Args.First_Index ..
                        P.Bound_Args.Last_Index
               loop
                  if not P.Bound_Args.Element (J).Is_Empty then
                     declare
                        BA : Type_Vectors.Vector :=
                          P.Bound_Args.Element (J);
                        BN : SU.Unbounded_String :=
                          P.Bounds.Element (J);
                     begin
                        for A of BA loop
                           if Mentions_Param (A, Params) then
                              raise Mono_Error with
                                "not yet supported: a generic-trait bound "
                                & "whose arguments mention a generic "
                                & "parameter (`"
                                & SU.To_String (P.Name) & ": "
                                & SU.To_String (BN) & ".<...>` of '"
                                & Ctx & "')";
                           end if;
                        end loop;
                        Rewrite_Trait_Ref (BN, BA);
                        P.Bounds.Replace_Element (J, BN);
                        P.Bound_Args.Replace_Element (J, BA);
                        Changed := True;
                     end;
                  end if;
               end loop;
               if Changed then
                  Params.Replace_Element (K, P);
               end if;
            end;
         end loop;
      end Rewrite_Param_Bounds;

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
                  when S_Break     => Scan_Expr (S.Brk_Val, Used, Bound);
                  when S_Continue | S_Fence | S_Trap | S_Asm => null;
               end case;
            end;
         end loop;
      end Scan_Stmts;

      procedure Scan_Expr
        (E : Expr_Access; Used, Bound : in out Path_Segments.Vector) is separate;

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
      is separate;

      procedure Visit_Expr (E : Expr_Access) is separate;

      procedure Visit_Stmt (S : Stmt_Access) is separate;

      --  §9.1/§9.4: specialise every generic-impl method whose owner is the
      --  generic type `Orig` for the concrete instance `Mangled` (with type
      --  arguments `Args`). Produces `Mangled$method` concrete subroutines —
      --  exactly the names static method dispatch resolves to — substituting
      --  the impl parameters and rewriting `selftype` to the owner instance.
      procedure Instantiate_Owner_Methods
        (Orig, Mangled : String; Args : Type_Vectors.Vector)
      is separate;

   begin
      --  Re-entrancy (§5.9.2 implicit instantiation): Kurt.Sema may
      --  request another monomorphisation round after inferring the type
      --  arguments of a bare generic call. Re-seed this run's state from
      --  the unit so already-generated declarations are neither lost nor
      --  regenerated: templates from U.Gen_*, the already-emitted set
      --  from every concrete declaration's name, and the closure-lift
      --  counter from the highest `$clo_N` already present.
      Gen_Structs := U.Gen_Structs;
      Gen_Enums   := U.Gen_Enums;
      Gen_Traits  := U.Gen_Traits;
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         Generated.Append (U.Fns.Element (I).Header.Name);
         declare
            Nm : constant String :=
              SU.To_String (U.Fns.Element (I).Header.Name);
         begin
            if Nm'Length > 5
              and then Nm (Nm'First .. Nm'First + 4) = "$clo_"
            then
               declare
                  N : Natural := 0;
               begin
                  for K in Nm'First + 5 .. Nm'Last loop
                     exit when Nm (K) not in '0' .. '9';
                     N := N * 10
                       + (Character'Pos (Nm (K)) - Character'Pos ('0'));
                  end loop;
                  if N > Clo_Seq then
                     Clo_Seq := N;
                  end if;
               end;
            end if;
         end;
      end loop;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         Generated.Append (U.Structs.Element (I).Name);
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         Generated.Append (U.Enums.Element (I).Name);
      end loop;
      for I in U.Traits.First_Index .. U.Traits.Last_Index loop
         Generated.Append (U.Traits.Element (I).Name);
      end loop;

      --  §9.3 lift generic trait templates; concrete traits stay.
      declare
         Keep_T : Trait_Vectors.Vector;
      begin
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            if U.Traits.Element (I).Generic_Params.Is_Empty then
               Keep_T.Append (U.Traits.Element (I));
            else
               Gen_Traits.Append (U.Traits.Element (I));
               U.Gen_Traits.Append (U.Traits.Element (I));
            end if;
         end loop;
         U.Traits := Keep_T;
      end;

      --  §9.3 resolve generic-trait impl targets to concrete trait
      --  instances (also renaming the impl's lowered `Type$Trait$method`
      --  symbols) BEFORE default-method synthesis, so defaults of a
      --  generic trait are synthesised from the substituted instance.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl := U.Trait_Impls.Element (I);
         begin
            if not TI.Trait_Args.Is_Empty then
               declare
                  Old : constant String := SU.To_String (TI.Trait_Name);
               begin
                  Rewrite_Trait_Ref (TI.Trait_Name, TI.Trait_Args);
                  declare
                     Pre_Old : constant String :=
                       SU.To_String (TI.Ty_Name) & "$" & Old & "$";
                     Pre_New : constant String :=
                       SU.To_String (TI.Ty_Name) & "$"
                       & SU.To_String (TI.Trait_Name) & "$";
                  begin
                     for F in U.Fns.First_Index .. U.Fns.Last_Index loop
                        declare
                           Nm : constant String :=
                             SU.To_String (U.Fns.Element (F).Header.Name);
                        begin
                           if Nm'Length > Pre_Old'Length
                             and then Nm (Nm'First ..
                                          Nm'First + Pre_Old'Length - 1)
                                        = Pre_Old
                           then
                              declare
                                 Fn : Fn_Decl := U.Fns.Element (F);
                              begin
                                 Fn.Header.Name := SU.To_Unbounded_String
                                   (Pre_New
                                    & Nm (Nm'First + Pre_Old'Length ..
                                          Nm'Last));
                                 U.Fns.Replace_Element (F, Fn);
                              end;
                           end if;
                        end;
                     end loop;
                     for G in U.Gen_Methods.First_Index ..
                              U.Gen_Methods.Last_Index
                     loop
                        declare
                           GM : Gen_Method := U.Gen_Methods.Element (G);
                        begin
                           if SU.To_String (GM.Owner)
                                = SU.To_String (TI.Ty_Name)
                             and then SU.To_String (GM.Trait_Name) = Old
                           then
                              GM.Trait_Name := TI.Trait_Name;
                              U.Gen_Methods.Replace_Element (G, GM);
                           end if;
                        end;
                     end loop;
                  end;
                  U.Trait_Impls.Replace_Element (I, TI);
               end;
            end if;
         end;
      end loop;


      --  §9.3.4 default methods: for every `impl Type as Trait` that omits
      --  a trait method carrying a default body, synthesise the concrete
      --  `Type$method` from the default (selftype → Type). The synthesised
      --  fns are plain concrete subroutines and follow the normal
      --  sema/codegen path. Done before the generic lift so they can use,
      --  and be used by, generic instantiation.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI    : Trait_Impl renames U.Trait_Impls.Element (I);
            Conc  : constant Type_Access := new AST_Type (Kind => T_Named);
            SelfP : Path_Segments.Vector;   --  ["selftype"]
            Args1 : Type_Vectors.Vector;    --  [Conc]
         begin
            Conc.Name := TI.Ty_Name;
            SelfP.Append (SU.To_Unbounded_String ("selftype"));
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

                           if TM.Has_Body and then not Provided
                             and then not Already_Generated
                               (SU.To_String (TI.Ty_Name) & "$"
                                & SU.To_String (TI.Trait_Name) & "$"
                                & MName)
                           then
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
               --  §9.1/§9.4: also kept on U itself (unlike the purely
               --  local Gen_Structs above, which does not survive past
               --  this procedure) so Kurt.Sema.Check can resolve a field
               --  access on `self` while template-checking a
               --  never-instantiated impl(...) method (spec 5.9.2).
               U.Gen_Structs.Append (U.Structs.Element (I));
            end if;
         end loop;
         U.Structs := Keep_S;

         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if U.Enums.Element (I).Generic_Params.Is_Empty then
               Keep_E.Append (U.Enums.Element (I));
            else
               Gen_Enums.Append (U.Enums.Element (I));
               U.Gen_Enums.Append (U.Enums.Element (I));
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

      --  §9.3 rewrite generic-trait bounds (`U: Pair.<si4>`) on every
      --  lifted template's generic parameter list to concrete instances.
      for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
         declare
            Fn : Fn_Decl := U.Gen_Fns.Element (I);
         begin
            if not Fn.Header.Generic_Params.Is_Empty then
               Rewrite_Param_Bounds
                 (Fn.Header.Generic_Params,
                  SU.To_String (Fn.Header.Name));
               U.Gen_Fns.Replace_Element (I, Fn);
            end if;
         end;
      end loop;
      for I in Gen_Structs.First_Index .. Gen_Structs.Last_Index loop
         declare
            D : Struct_Decl := Gen_Structs.Element (I);
         begin
            Rewrite_Param_Bounds
              (D.Generic_Params, SU.To_String (D.Name));
            Gen_Structs.Replace_Element (I, D);
         end;
      end loop;
      U.Gen_Structs := Gen_Structs;
      for I in Gen_Enums.First_Index .. Gen_Enums.Last_Index loop
         declare
            D : Enum_Decl := Gen_Enums.Element (I);
         begin
            Rewrite_Param_Bounds
              (D.Generic_Params, SU.To_String (D.Name));
            Gen_Enums.Replace_Element (I, D);
         end;
      end loop;
      U.Gen_Enums := Gen_Enums;
      for I in U.Gen_Methods.First_Index .. U.Gen_Methods.Last_Index loop
         declare
            GM : Gen_Method := U.Gen_Methods.Element (I);
         begin
            Rewrite_Param_Bounds
              (GM.Gen_Params,
               "impl of '" & SU.To_String (GM.Owner) & "'");
            U.Gen_Methods.Replace_Element (I, GM);
         end;
      end loop;

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
