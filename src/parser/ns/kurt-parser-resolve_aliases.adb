with Kurt.Layout;

separate (Kurt.Parser)

   --  §10.3 per-source-unit alias scoping.
   --
   --  Each source unit is resolved ALONE, right after it is parsed and its
   --  own `@add`/`@dyn`/`module` namespaces are known, but before it is
   --  merged into the enclosing translation unit (see main-translate.adb's
   --  Load). `Alias_Names`/`Alias_Prefixes` therefore contain exactly the
   --  aliases usable from WITHIN this one source unit: its own `@add`/
   --  `@dyn` sites (regardless of `pub` -- a unit always sees its own
   --  declarations), its own `module` namespaces (self-mapped, likewise
   --  unconditional), and anything the unit transitively inherited from a
   --  `pub`-marked import (§10.3 `@add pub`, §10.4 `@dyn pub`). A name
   --  private to some OTHER unit never appears here, so an `alias::item`
   --  reference whose head this unit never itself introduced simply fails
   --  to collapse (Prefix_Of returns "") and falls through to ordinary
   --  (failing) name resolution -- this is the alias-privacy rule itself,
   --  not a special case.
   --
   --  `module` visibility (§10.6) is different in kind: a module's mangled
   --  namespace prefix is already globally unique (it is composed from the
   --  owning file's own mangling prefix), so instead of being propagated
   --  hand-to-hand through each importer's alias table, it is checked
   --  against a single flat whole-programme registry (NS_Names/NS_Pubs)
   --  the moment a collapse step's head matches one -- see Prefix_Of.
   procedure Resolve_Aliases
     (U              : in out Translation_Unit;
      Pub_Source     : Translation_Unit;
      Cur_Prefix     : String;
      Alias_Names    : Path_Segments.Vector;
      Alias_Prefixes : Path_Segments.Vector;
      NS_Names       : Path_Segments.Vector;
      NS_Pubs        : Bool_Vectors.Vector)
   is
      --  Find the mangled prefix bound to Head. Tier 1 (Alias_Names) is
      --  this unit's own per-unit table, unconditional. Tier 2 (NS_Names)
      --  is the whole-programme `module` registry (§10.6): a match there
      --  that is NOT `pub` is a hard translation failure -- Head names a
      --  real namespace in another source unit that this unit has no
      --  right to see, and silently leaving it unresolved would let
      --  Kurt.Sema's associated-subroutine fallback (`Type::fn` — see
      --  Infer_Call) accidentally re-derive the very same mangled symbol
      --  and let the access through unchecked.
      function Prefix_Of (Head : String) return String is
      begin
         for I in Alias_Names.First_Index .. Alias_Names.Last_Index loop
            if SU.To_String (Alias_Names.Element (I)) = Head then
               return SU.To_String (Alias_Prefixes.Element (I));
            end if;
         end loop;
         for I in NS_Names.First_Index .. NS_Names.Last_Index loop
            if SU.To_String (NS_Names.Element (I)) = Head then
               if NS_Pubs.Element (I) then
                  return Head;   --  modules are self-mapped (already mangled)
               end if;
               raise Syntax_Error with
                 "module '" & Head & "' is not `pub` and is not "
                 & "accessible outside its declaring source unit "
                 & "(spec 10.6)";
            end if;
         end loop;
         return "";
      end Prefix_Of;

      --  §10.3/§10.6: the target of an `alias::item` reference shall be
      --  `pub` in the imported unit. Scans Pub_Source (the accumulated
      --  translation unit -- every source unit this one `@add`s,
      --  already merged and mangled; NOT this unit's own not-yet-merged
      --  U, which is always fully visible to itself regardless of `pub`)
      --  for Mangled; a name absent from all of them (e.g. an enum
      --  variant, which isn't independently `pub`-tracked) is not
      --  flagged here — ordinary name resolution catches a bad access.
      function Check_Pub (Mangled : String) return Boolean is
      begin
         for I in Pub_Source.Fns.First_Index ..
                  Pub_Source.Fns.Last_Index loop
            if SU.To_String (Pub_Source.Fns.Element (I).Header.Name)
                 = Mangled
            then
               return Pub_Source.Fns.Element (I).Header.Is_Pub;
            end if;
         end loop;
         for I in Pub_Source.Structs.First_Index ..
                  Pub_Source.Structs.Last_Index loop
            if SU.To_String (Pub_Source.Structs.Element (I).Name)
                 = Mangled
            then
               return Pub_Source.Structs.Element (I).Is_Pub;
            end if;
         end loop;
         for I in Pub_Source.Enums.First_Index ..
                  Pub_Source.Enums.Last_Index loop
            if SU.To_String (Pub_Source.Enums.Element (I).Name) = Mangled
            then
               return Pub_Source.Enums.Element (I).Is_Pub;
            end if;
         end loop;
         for I in Pub_Source.Traits.First_Index ..
                  Pub_Source.Traits.Last_Index loop
            if SU.To_String (Pub_Source.Traits.Element (I).Name) = Mangled
            then
               return Pub_Source.Traits.Element (I).Is_Pub;
            end if;
         end loop;
         for I in Pub_Source.Consts.First_Index ..
                  Pub_Source.Consts.Last_Index loop
            if SU.To_String (Pub_Source.Consts.Element (I).Name) = Mangled
            then
               return Pub_Source.Consts.Element (I).Is_Pub;
            end if;
         end loop;
         for I in Pub_Source.Statics.First_Index ..
                  Pub_Source.Statics.Last_Index loop
            if SU.To_String (Pub_Source.Statics.Element (I).Name) = Mangled
            then
               return Pub_Source.Statics.Element (I).Is_Pub;
            end if;
         end loop;
         --  §10.4 `@dyn` symbol: unlike ordinary top-level/module items,
         --  a non-`pub` symbol is accessible throughout its OWN source
         --  unit (not merely from the `@dyn` block itself) -- so the
         --  `pub` gate applies only when Mangled was declared in a
         --  DIFFERENT source unit than the one currently being resolved.
         for I in Pub_Source.Dyns.First_Index ..
                  Pub_Source.Dyns.Last_Index loop
            declare
               D : constant Dyn_Decl := Pub_Source.Dyns.Element (I);
            begin
               for J in D.Items.First_Index .. D.Items.Last_Index loop
                  if SU.To_String (D.Items.Element (J).Name) = Mangled then
                     if Kurt.Layout.Same_Source_Unit (Mangled, Cur_Prefix)
                     then
                        return True;
                     end if;
                     return D.Items.Element (J).Is_Pub;
                  end if;
               end loop;
            end;
         end loop;
         return True;   --  not a tracked top-level decl; let sema judge it
      end Check_Pub;

      --  §5.12.2 `use path::name;`: Use_Bare holds each imported bare
      --  identifier this unit declared; Use_Target holds the single final
      --  mangled name it resolves to (parallel vectors, populated by the
      --  loop just before the main declaration walk below). Unlike the
      --  alias table above (which only ever fires on a 2+-segment
      --  `alias::item` reference), a `use` name is substituted at any
      --  BARE (single-segment) reference matching it.
      Use_Bare   : Path_Segments.Vector;
      Use_Target : Path_Segments.Vector;

      --  Whether Mangled names a real top-level declaration -- either in
      --  this not-yet-merged unit itself, or already merged into
      --  Pub_Source (a cross-unit `use` target). Used only to validate
      --  that a `use` path actually resolves to something (spec 5.12.2's
      --  "shall name a path that resolves to a named item").
      function Decl_Exists
        (Scan : Translation_Unit; Mangled : String) return Boolean is
      begin
         for I in Scan.Fns.First_Index .. Scan.Fns.Last_Index loop
            if SU.To_String (Scan.Fns.Element (I).Header.Name) = Mangled
            then
               return True;
            end if;
         end loop;
         for I in Scan.Structs.First_Index .. Scan.Structs.Last_Index loop
            if SU.To_String (Scan.Structs.Element (I).Name) = Mangled then
               return True;
            end if;
         end loop;
         for I in Scan.Enums.First_Index .. Scan.Enums.Last_Index loop
            if SU.To_String (Scan.Enums.Element (I).Name) = Mangled then
               return True;
            end if;
         end loop;
         for I in Scan.Traits.First_Index .. Scan.Traits.Last_Index loop
            if SU.To_String (Scan.Traits.Element (I).Name) = Mangled then
               return True;
            end if;
         end loop;
         for I in Scan.Consts.First_Index .. Scan.Consts.Last_Index loop
            if SU.To_String (Scan.Consts.Element (I).Name) = Mangled then
               return True;
            end if;
         end loop;
         for I in Scan.Statics.First_Index .. Scan.Statics.Last_Index loop
            if SU.To_String (Scan.Statics.Element (I).Name) = Mangled then
               return True;
            end if;
         end loop;
         return False;
      end Decl_Exists;

      --  Collapse a >=2-segment path whose first segment is a known alias:
      --  [alias, Head, Rest...] -> [prefix & "$" & Head, Rest...].
      procedure Collapse (Segs : in out Path_Segments.Vector) is
      begin
         --  §10.6 (root unit): a surviving leading `srcroot` names the top
         --  level itself — strip it. (`@add`-ed units resolved theirs
         --  during their whole-file rename pass.)
         if Natural (Segs.Length) >= 2
           and then SU.To_String (Segs.First_Element) = "srcroot"
         then
            Segs.Delete_First;
         end if;
         --  Fixpoint: nested namespaces collapse one step per round
         --  (`a::b::f` -> `a$b::f` -> `a$b$f`).
         loop
            exit when Natural (Segs.Length) < 2;
            declare
               Pfx : constant String :=
                 Prefix_Of (SU.To_String (Segs.First_Element));
            begin
               exit when Pfx = "";
               declare
                  Second  : constant String :=
                    SU.To_String (Segs.Element (Segs.First_Index + 1));
                  Mangled : constant String := Pfx & "$" & Second;
                  Tail    : Path_Segments.Vector;
               begin
                  for I in Segs.First_Index + 2 .. Segs.Last_Index loop
                     Tail.Append (Segs.Element (I));
                  end loop;
                  if not Check_Pub (Mangled) then
                     raise Syntax_Error with
                       "'" & Second & "' is not `pub` in its namespace "
                       & "(spec 10.3/10.6)";
                  end if;
                  Segs.Clear;
                  Segs.Append (SU.To_Unbounded_String (Mangled));
                  Segs.Append (Tail);
               end;
            end;
         end loop;
      end Collapse;

      --  "alias::Item" -> "prefix$Item" (checking `pub`); anything else
      --  (no "::", or an unrecognised head) is returned unchanged, UNLESS
      --  it is a bare name matching a §5.12.2 `use` import, in which case
      --  it is substituted directly. Used for compound names stored as a
      --  single string (qualified struct-literal `SL_Name`, qualified
      --  type names).
      function Mangle_Compound (Nm : String) return String is
         Sep : constant Natural := Ada.Strings.Fixed.Index (Nm, "::");
      begin
         if Sep = 0 then
            for K in Use_Bare.First_Index .. Use_Bare.Last_Index loop
               if SU.To_String (Use_Bare.Element (K)) = Nm then
                  return SU.To_String (Use_Target.Element (K));
               end if;
            end loop;
            return Nm;
         end if;
         declare
            Head : constant String := Nm (Nm'First .. Sep - 1);
            Rest : constant String := Nm (Sep + 2 .. Nm'Last);
            Pfx  : constant String := Prefix_Of (Head);
         begin
            if Pfx = "" then
               return Nm;
            end if;
            declare
               Mangled : constant String := Pfx & "$" & Rest;
            begin
               if not Check_Pub (Mangled) then
                  raise Syntax_Error with
                    "'" & Rest & "' is not `pub` in namespace '"
                    & Head & "' (spec 10.3/10.6)";
               end if;
               return Mangled;
            end;
         end;
      end Mangle_Compound;

      procedure RT (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               declare
                  Nm : constant String := SU.To_String (T.Name);
               begin
                  T.Name := SU.To_Unbounded_String (Mangle_Compound (Nm));
               end;
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
               null;
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index
               loop
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
               if Natural (E.Segments.Length) >= 2 then
                  Collapse (E.Segments);
               elsif Natural (E.Segments.Length) = 1 then
                  --  §5.12.2 a bare name matching a `use` import is a
                  --  direct synonym for its resolved target.
                  declare
                     Nm : constant String :=
                       SU.To_String (E.Segments.First_Element);
                  begin
                     for K in Use_Bare.First_Index ..
                              Use_Bare.Last_Index loop
                        if SU.To_String (Use_Bare.Element (K)) = Nm then
                           E.Segments.Replace_Element
                             (E.Segments.First_Index,
                              Use_Target.Element (K));
                           exit;
                        end if;
                     end loop;
                  end;
               end if;
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
                 (Mangle_Compound (SU.To_String (E.SL_Name)));
               for I in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index
               loop
                  RE (E.SL_Fields.Element (I).Val);
               end loop;
            when E_Variant_New =>
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
                     if Natural (A.Pat.Path.Length) >= 2 then
                        Collapse (A.Pat.Path);
                     end if;
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
            when E_Extract =>
               RE (E.Ex_Inner); RE (E.Ex_Fallback);
            when E_CAS =>
               RE (E.CAS_Tgt); RE (E.CAS_Exp); RE (E.CAS_New);
            when E_Array_Lit =>
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
                  RE (E.AL_Elems.Element (I));
               end loop;
            when E_Dyn_Cast =>
               RE (E.DC_Inner);
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
               if S.L_Is_Refut and then Natural (S.L_Refut_Pat.Path.Length)
                                          >= 2
               then
                  Collapse (S.L_Refut_Pat.Path);
               end if;
               RBlk (S.L_Else);
            when S_Assign =>
               RE (S.Asn_Lhs); RE (S.Asn_Rhs);
            when S_While =>
               RE (S.W_Cond);
               RBlk (S.W_Body);
               RBlk (S.W_Then);
               if S.W_Is_Let and then Natural (S.W_Let_Pat.Path.Length) >= 2
               then
                  Collapse (S.W_Let_Pat.Path);
               end if;
            when S_If =>
               RE (S.SI_Cond);
               RBlk (S.SI_Then);
               RBlk (S.SI_Else);
               if S.SI_Is_Let and then Natural (S.SI_Let_Pat.Path.Length)
                                         >= 2
               then
                  Collapse (S.SI_Let_Pat.Path);
               end if;
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
   begin
      --  §5.12.2 resolve this unit's own `use` declarations FIRST (they
      --  may themselves depend on the alias table above, e.g. `use
      --  io::read;`), populating Use_Bare/Use_Target for the walk below.
      for I in U.Use_Names.First_Index .. U.Use_Names.Last_Index loop
         declare
            Nm   : constant String := SU.To_String (U.Use_Names.Element (I));
            Path : Path_Segments.Vector := U.Use_Paths.Element (I);
         begin
            --  Constraint (spec 5.12.2): a `use` name shall not already
            --  exist in the current scope -- checked against this unit's
            --  own top-level declarations and any earlier `use` in it.
            if Decl_Exists (U, Nm) then
               raise Syntax_Error with
                 "`use` name '" & Nm & "' collides with an existing "
                 & "declaration in this source unit (spec 5.12.2)";
            end if;
            for K in Use_Bare.First_Index .. Use_Bare.Last_Index loop
               if SU.To_String (Use_Bare.Element (K)) = Nm then
                  raise Syntax_Error with
                    "'" & Nm & "' is already imported by an earlier "
                    & "`use` declaration (spec 5.12.2)";
               end if;
            end loop;
            Collapse (Path);
            if Natural (Path.Length) /= 1
              or else not (Decl_Exists (U, SU.To_String (Path.First_Element))
                           or else Decl_Exists
                                     (Pub_Source,
                                      SU.To_String (Path.First_Element)))
            then
               raise Syntax_Error with
                 "`use` path for '" & Nm & "' does not resolve to a named "
                 & "item (spec 5.12.2)";
            end if;
            Use_Bare.Append (SU.To_Unbounded_String (Nm));
            Use_Target.Append (Path.First_Element);
         end;
      end loop;
      if Alias_Names.Is_Empty and then Use_Bare.Is_Empty then
         return;
      end if;
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Fns.Element (I);
         begin
            for K in F.Header.Params.First_Index ..
                     F.Header.Params.Last_Index loop
               RT (F.Header.Params.Element (K).Ty);
            end loop;
            RT (F.Header.Return_Type);
            RBlk (F.Body_Stmts);
            U.Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
         declare
            F : Fn_Decl := U.Gen_Fns.Element (I);
         begin
            for K in F.Header.Params.First_Index ..
                     F.Header.Params.Last_Index loop
               RT (F.Header.Params.Element (K).Ty);
            end loop;
            RT (F.Header.Return_Type);
            RBlk (F.Body_Stmts);
            U.Gen_Fns.Replace_Element (I, F);
         end;
      end loop;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            D : constant Struct_Decl := U.Structs.Element (I);
         begin
            for K in D.Fields.First_Index .. D.Fields.Last_Index loop
               RT (D.Fields.Element (K).Ty);
               RE (D.Fields.Element (K).Default);
            end loop;
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            D : constant Enum_Decl := U.Enums.Element (I);
         begin
            for V in D.Variants.First_Index .. D.Variants.Last_Index loop
               for K in D.Variants.Element (V).Payload.First_Index ..
                        D.Variants.Element (V).Payload.Last_Index loop
                  RT (D.Variants.Element (V).Payload.Element (K).Ty);
               end loop;
            end loop;
         end;
      end loop;
      for I in U.Consts.First_Index .. U.Consts.Last_Index loop
         RT (U.Consts.Element (I).Ty);
         RE (U.Consts.Element (I).Init);
      end loop;
      for I in U.Statics.First_Index .. U.Statics.Last_Index loop
         RT (U.Statics.Element (I).Ty);
         RE (U.Statics.Element (I).Init);
      end loop;
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : constant Trait_Impl := U.Trait_Impls.Element (I);
         begin
            for K in TI.Consts.First_Index .. TI.Consts.Last_Index loop
               RT (TI.Consts.Element (K).Ty);
               RE (TI.Consts.Element (K).Val);
            end loop;
         end;
      end loop;
      RBlk (U.Trap_Handler);
   end Resolve_Aliases;
