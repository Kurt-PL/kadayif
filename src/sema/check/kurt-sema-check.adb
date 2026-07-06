separate (Kurt.Sema)
   procedure Check
     (U           : in out Kurt.Parser.Translation_Unit;
      Error_Count : out Natural)
   is
      Errors  : Natural := 0;
      Sigs    : Sig_Vec.Vector;
      Scope   : SBind_Vec.Vector;
      --  §5.17 base index (into Scope) of the current lexical block: a name
      --  declared at-or-above this index is in the *same* scope (a duplicate
      --  declaration = TF); a same-named binding below it is an outer
      --  declaration, which the inner one legally shadows.
      Block_Base : Natural := 0;
      Cur_Ret : Type_Access;
      --  §7.6: whether the subroutine currently being checked is declared
      --  `-> never`; such a body shall not contain a `return` statement.
      Cur_Is_Never : Boolean := False;
      --  §8.2/§8.3 reference derivation tree for the body being analysed.
      Borrows : Kurt.Borrow.Tree;
      --  §8.8.2 bindings invalidated by a transfer (move).
      Moved   : Moved_Vec.Vector;
      --  §5.2 deferred-init (`let`/`mut` sans initializer) tracking.
      Init_States : Init_Vec.Vector;
      --  §5.2: True while inferring an assignment's own LHS place, so the
      --  place isn't flagged as a read of itself (Infer_Path).
      Suppress_Init_Read : Boolean := False;
      --  §6.1.8/§2.6: airside nesting depth for the statement being
      --  checked. Raised inside an `airside { ... }` block and for the whole
      --  body of an `airside fn`. `uninit` is valid only when this is > 0.
      In_Airside : Natural := 0;
      --  §5.5.1/§6.2.2: mangled name of the fn currently being checked, so
      --  a field-access check can tell its declaring source unit apart
      --  from the accessed struct's (Kurt.Layout.Same_Source_Unit).
      Cur_Fn_Name : SU.Unbounded_String;
      --  §10.4: mangled names of every subroutine declared in a `@dyn`
      --  block. Invoking one is permitted only within an `airside` region.
      Dyn_Fn_Names : Path_Segments.Vector;
      --  §6.9/§7.8: the expected type flowing into the innermost enclosing
      --  block expression's trailing `express` (steers integer-literal
      --  typing exactly like a `let` annotation would). Null when the
      --  statement being checked is not inside a block expression.
      Express_Expected : Type_Access := null;
      --  §7.8: depth of enclosing contexts a bare `express` may target — a
      --  block expression (`{ ... }` / `airside { ... }`, in value or
      --  statement position) or an extract `else` block (§7.2.3, where
      --  `express` yields the fallback value). Zero means the statement
      --  being checked sits directly in the subroutine body, where an
      --  unlabelled `express` shall not appear.
      In_Expr_Block : Natural := 0;
      --  §7.9: labels currently in scope, innermost last. A loop label
      --  is the target of `break`/`continue`; a block label is the
      --  target of `express`. Inner labels shadow outer ones of the
      --  same name, so every lookup searches innermost-first.
      type Lbl_Entry is record
         Name     : SU.Unbounded_String;
         Is_Block : Boolean := False;
      end record;
      package Lbl_Vec is new Ada.Containers.Vectors
        (Index_Type => Positive, Element_Type => Lbl_Entry);
      Label_Stack : Lbl_Vec.Vector;
      In_Loop     : Natural := 0;   --  §7.7 plain break/continue need a loop
      --  §5.9.2 type-erasure context: the generic parameters of the
      --  template currently being checked (empty for concrete fns). A
      --  generic subroutine is checked ONCE against the abstract
      --  parameters — never per instantiation — so an operation on `T`
      --  is legal only if T's bounds license it.
      Cur_Generics : Generic_Param_Vectors.Vector;

      procedure Error (Msg : String) is
      begin
         Errors := Errors + 1;
         IO.Put_Line (IO.Standard_Error, "kadayif: type error: " & Msg);
      end Error;

      function Find_Sig (Name : String; Found : out Sig) return Boolean is
      begin
         for I in Sigs.First_Index .. Sigs.Last_Index loop
            if SU.To_String (Sigs.Element (I).Name) = Name then
               Found := Sigs.Element (I);
               return True;
            end if;
         end loop;
         return False;
      end Find_Sig;

      function Lookup_Scope (Name : String) return Type_Access is
      begin
         for I in reverse Scope.First_Index .. Scope.Last_Index loop
            if SU.To_String (Scope.Element (I).Name) = Name then
               return Scope.Element (I).Ty;
            end if;
         end loop;
         return null;
      end Lookup_Scope;

      --  §2.2.1: nearest binding's mutability (innermost scope wins, matching
      --  Lookup_Scope's shadowing order). Found is set False when no local
      --  binding of that name exists.
      function Lookup_Scope_Mut
        (Name : String; Found : out Boolean) return Boolean is separate;

      --  §5.4: whether Name denotes a top-level static binding (and
      --  whether it is `static mut`). Local bindings shadow statics, so
      --  callers check Lookup_Scope first.
      function Find_Static_Decl
        (Name : String; Is_Mut : out Boolean) return Boolean is separate;

      --  §9.3: look up a method signature `M_Name` in trait `Tr_Name`.
      --  Returns the method's signature header (Found set) or leaves
      --  Found False. Searches U.Traits.
      procedure Lookup_Trait_Method
        (Tr_Name, M_Name : String;
         Sig_Out         : out Fn_Header;
         Found           : out Boolean)
      is separate;

      --  §9.3.2: the value expression of associated const Name in the
      --  `impl Ty_Name as <trait>` block (null if none). Want_Trait, when
      --  non-empty (from a qualified `(Ty as Trait)::Name` access), forces
      --  resolution to that one trait impl. §9.2.1: an unqualified access
      --  ambiguous between two distinct trait impls is a translation
      --  failure (raised here); an inherent impl's const always takes
      --  priority and is never ambiguous.
      function Find_Impl_Const
        (Ty_Name, Name, Want_Trait : String) return Expr_Access
      is separate;

      --  §9.3.2: the declared type of associated const Name in any trait
      --  named by generic parameter Gen's bounds (selftype → Gen). Found
      --  is set when located.
      procedure Find_Bound_Const
        (Gen, Name : String; Ty_Out : out Type_Access; Found : out Boolean)
      is separate;

      --  Substitute the `selftype` placeholder with concrete type Conc in
      --  a (freshly copied) type, e.g. a trait method's return type.
      function Subst_Self_T (T, Conc : Type_Access) return Type_Access is separate;

      --  §9.4: does concrete type Ty_Name implement Trait Tr_Name?
      function Type_Implements (Ty_Name, Tr_Name : String) return Boolean is separate;

      --  Is Nm the name of a declared trait?
      function Is_Trait_Name (Nm : String) return Boolean is separate;

      --  §9.2.1 resolve the mangled symbol of a method / associated item on a
      --  concrete type. An inherent `Type$item` takes priority; in its absence
      --  a unique trait impl gives `Type$Trait$item`. `Want_Trait` (non-empty)
      --  forces that trait directly — `(e as Trait).item`. Ambiguous is set
      --  when two or more trait impls provide the item and there is no inherent
      --  one and no forced trait.
      procedure Resolve_Item_Symbol
        (Ty_Name, Item, Want_Trait : String;
         Symbol     : out SU.Unbounded_String;
         Found      : out Boolean;
         Ambiguous  : out Boolean)
      is separate;

      --  §9.3 / §5.9: if generic parameter Gen carries a trait bound
      --  whose trait declares method M_Name, return its signature.
      procedure Find_Bound_Method
        (Gen, M_Name : String;
         Sig_Out     : out Fn_Header;
         Found       : out Boolean)
      is separate;

      --  Whether T names a generic parameter of the enclosing template.
      function Is_Generic_Param_Ty (T : Type_Access) return Boolean is separate;

      --  §5.9/§9.8: arithmetic and comparison on a generic parameter
      --  require a `numeric`, `integer`, or `primitive` bound. An
      --  unconstrained parameter is an opaque layout.
      function Generic_Arith_OK (T : Type_Access) return Boolean is separate;

      --  §8.11.1 destruct-satisfaction (declared + propagation) is computed
      --  once in Kurt.Layout, which holds the unit's struct/enum decls.
      --  §9.8.5 type-erasure view of `destruct`: inside a generic
      --  template a parameter satisfies `destruct` exactly when its
      --  bounds say so (`T: destruct`); `T: !destruct` and unbounded
      --  parameters are treated as copyable. A concrete type defers to
      --  the layout model.
      function Satisfies_Destruct (T : Type_Access) return Boolean is
      begin
         if T /= null and then T.Kind = T_Named
           and then T.Args.Is_Empty
         then
            for G of Cur_Generics loop
               if SU.To_String (G.Name) = SU.To_String (T.Name) then
                  for B of G.Bounds loop
                     if SU.To_String (B) = "destruct" then
                        return True;
                     end if;
                  end loop;
                  return False;
               end if;
            end loop;
         end if;
         return Kurt.Layout.Satisfies_Destruct (T);
      end Satisfies_Destruct;

      function Is_Moved (Name : String) return Boolean is
      begin
         for M of Moved loop
            if SU.To_String (M.Name) = Name then
               return True;
            end if;
         end loop;
         return False;
      end Is_Moved;

      procedure Mark_Moved (Name : String) is separate;

      --  §5.2: locate Name's deferred-init tracking entry, if any.
      function Init_Lookup
        (Name : String; Idx : out Natural) return Boolean is separate;

      --  §9.9.3: an aggregate capture (struct / tuple / array / payload enum)
      --  must be bound into the closure body by reference to its env field —
      --  it cannot be loaded as a register value, and a `with destruct`
      --  capture must not be copied into a second owner.
      function Cap_By_Ref (T : Type_Access) return Boolean is separate;

      --  §8.8.2: if E is a bare binding of a `destruct` type used as a
      --  transfer source, invalidate it (use-after-move becomes a failure).
      procedure Maybe_Move (E : Expr_Access) is separate;

      --  §8.9: a type satisfying `destruct` shall not be LOADED (copied)
      --  through a tracked reference (&T, &mut T, $T) -- only a `&raw`
      --  load is exempt. Conservative check for a direct load position
      --  (initializer, return value, call argument): E must already be
      --  Infer'd, so E.Sem_Ty and E.D_Inner.Sem_Ty (for an E_Deref) are
      --  populated.
      procedure Check_No_Destruct_Load (E : Expr_Access) is separate;

      --  §7.4 the type of the K-th payload binding of a variant pattern: by
      --  the named field when the entry is a `field = binding` rename, else
      --  by position K.
      function Pat_Field_Ty
        (Pat : Kurt.Parser.Pattern; Scrut : Type_Access;
         VN : String; K : Positive) return Type_Access is separate;

      --  §5.10.2: without `...`, a destructuring payload-binds clause
      --  shall mention every field of the variant. A bare `Enum::Variant`
      --  pattern with no binds clause matches on the discriminant only
      --  and is exempt. Shared by match / if-let / while-let / let-else.
      procedure Check_Payload_Coverage
        (Pat : Kurt.Parser.Pattern; EN, VN : String) is
      begin
         if not Pat.Has_Rest
           and then not Pat.Bindings.Is_Empty
           and then Natural (Pat.Bindings.Length)
                      /= Kurt.Layout.Variant_Field_Count (EN, VN)
         then
            Error ("pattern for '" & EN & "::" & VN & "' shall mention "
                   & "every payload field or end with `...` "
                   & "(spec 5.10.2)");
         end if;
         --  §5.10.2: `...` is permitted only for named-field payloads,
         --  not positional-field ones (whose parse-synthesised field
         --  names "0", "1", ... cannot be written as identifiers).
         if Pat.Has_Rest
           and then Kurt.Layout.Variant_Field_Count (EN, VN) > 0
           and then Kurt.Layout.Variant_Field_Name (EN, VN, 1) = "0"
         then
            Error ("`...` shall not appear in a positional-field pattern; "
                   & "'" & EN & "::" & VN & "' has positional fields "
                   & "(spec 5.10.2)");
         end if;
      end Check_Payload_Coverage;

      --  Body appears with the statement checks below; needed here for the
      --  §6.9 `airside { ... }` block expression (its body is statements).
      procedure Check_Block (Stmts : Stmt_Vectors.Vector);

      --  Declared ahead of Infer's stub (body below, with the other §7.11
      --  divergence analysis): Infer types a diverging block expression
      --  as `never` (§7.11), so it needs the predicate in scope.
      function Stmts_Diverge (V : Stmt_Vectors.Vector) return Boolean;

      --------------------------------------------------------------------
      --  Infer a type for E, attach it to E.Sem_Ty, and return it.
      --  Expected flows downward (mainly to steer integer-literal type).
      --  Neg_Ctx is set only when E is the direct operand of a unary `-`;
      --  it widens an integer literal's §3.5.1 fits-target check to admit
      --  the extra negative magnitude (e.g. `-128` into `si1`).
      --------------------------------------------------------------------
      function Infer (E : Expr_Access; Expected : Type_Access;
                       Neg_Ctx : Boolean := False)
         return Type_Access
      is separate;

      --  §6.1.8 shared check for a `uninit` value in a valid assignment
      --  position: it must occur in an airside region, and the target type
      --  must be known (so the binding's object has a determinate type).
      procedure Check_Uninit (Target : Type_Access) is separate;

      --  §7.9: a labelled `break`/`continue` shall name a loop label that is
      --  in scope. An empty label (plain break/continue) is always allowed.
      procedure Check_Loop_Label (Label : SU.Unbounded_String) is separate;

      --------------------------------------------------------------------
      --  §7.11 divergence analysis (bootstrap subset). A statement list
      --  diverges when control cannot reach its end. The diverging forms
      --  recognised here: `@trap`, `return`, `break`, `continue`,
      --  `express`, a `-> never` call, a `loop {}` with no `break`, an
      --  `if`/`else` whose both arms diverge, and an `airside` block
      --  whose body diverges.
      --  Translation-time-true: a literal `true`, or a bare identifier
      --  naming a top-level `const ... : bool = true;` (literal init).
      --  Conservative on purpose -- only these two syntactic forms.
      function Cond_Is_True (E : Expr_Access) return Boolean is separate;

      --  Translation-time-false: the mirror of Cond_Is_True, for `false`.
      --  Used to recognise an unreachable `if false { ... }` branch during
      --  §7.11 divergence/escape analysis (spec's own canonical example:
      --  `while true { if false { break; } ... }` still diverges).
      function Cond_Is_False (E : Expr_Access) return Boolean is separate;

      --  §7.11: a `loop {}` diverges only when no `break` (targeting it or
      --  an enclosing loop) and no `express` (targeting an enclosing
      --  block) is reachable in its body. Conservative: any such escape
      --  anywhere in V disqualifies it, even one bound to a nested
      --  construct — a false negative is safe; a false positive is not.
      function Has_Escape (V : Stmt_Vectors.Vector) return Boolean is separate;

      function Stmt_Diverges (S : Stmt_Access) return Boolean is separate;

      function Stmts_Diverge (V : Stmt_Vectors.Vector) return Boolean is separate;

      --------------------------------------------------------------------
      procedure Check_Stmt (S : Stmt_Access);

      --  §8.2/§8.3: map a reference sigil + store modifier to its initial
      --  permission state. `&raw` is untracked (§8.2.2): Tracked is False.
      procedure Borrow_State
        (Sigil   : Ref_Sigil;
         Store   : Ref_Store;
         State   : out Kurt.Borrow.Perm_State;
         Tracked : out Boolean)
      is separate;

      --  §8.2: when `Name` is bound to `&x`/`$x`/`&mut x` (etc.) of a simple
      --  named place, register the reference in the derivation tree and apply
      --  the §8.3 aliasing constraint at creation.
      procedure Register_Borrow (Name : String; Init : Expr_Access) is separate;

      --  §8.3: a store through `*binding` whose binding holds a tracked
      --  reference. An exclusive store asserts exclusivity; if the place is
      --  aliased by another live reference, that is a provable violation.
      procedure Register_Store (Lhs : Expr_Access) is separate;

      --  §8.4 a place outlives the call iff its storage has program lifetime
      --  ('static / 'const): a top-level `static`/`static mut` or a `const`.
      --  A local `let`/`mut` binding or a value parameter dies when the call
      --  returns, so a reference to it shall not be returned.
      function Outlives_Call (Place : String) return Boolean is separate;

      --  §8.4.3 escape verification: a returned landside reference shall not
      --  outlive its referent. The referent must have program lifetime; a
      --  reference to a local or to a value parameter escapes its scope.
      --  Provenance of a returned reference binding comes from the derivation
      --  tree (`let r = &local; return r;` is caught the same as `return
      --  &local;`). `&raw` is unmanaged (airside responsibility) and exempt.
      procedure Check_Return_Escape (E : Expr_Access) is separate;

      procedure Check_Block (Stmts : Stmt_Vectors.Vector) is separate;

      --  §5.17: a name shall be declared at most once within a scope. Flag a
      --  collision with a binding already declared in the current block;
      --  bindings below Block_Base belong to outer scopes and are shadowed.
      procedure Check_Dup_In_Scope (Name : SU.Unbounded_String) is separate;

      --  §6.10.2 conservative xlatime-foldability: literals, layout
      --  intrinsics, other consts, aggregate literals over recursively
      --  foldable parts, and pure operators over those. Shared by
      --  Validate_Consts_Statics (top-level/impl consts, spec 5.3), the
      --  struct-field default-value check below (spec 5.5.3), and (moved
      --  ahead of Check_Stmt so Check_Stmt.Check_Let can see it, spec 5.3
      --  Fix 4) the statement-position local-`const` check -- a field
      --  default / local const is a translation-time initializer exactly
      --  like a top-level const's, so the same rule governs all three.
      function Is_Xlatime_Foldable (E : Expr_Access) return Boolean
        is separate;

      procedure Check_Stmt (S : Stmt_Access) is separate;
      procedure Check_Fn_Bodies is separate;

      procedure Validate_Consts_Statics is separate;
      procedure Validate_Enums is separate;
   begin
      --  §5.17: within the top-level scope a name shall be declared at most
      --  once, uniformly across fn / struct / enum / trait / const / static.
      --  Names containing '$' are compiler-generated (monomorphised
      --  instances, lowered `Type$method` impl items) and are unique by
      --  construction, so they are excluded to avoid false positives.
      declare
         Seen : Path_Segments.Vector;

         function Is_Generated (Name : String) return Boolean is
         begin
            for I in Name'Range loop
               if Name (I) = '$' then
                  return True;
               end if;
            end loop;
            return False;
         end Is_Generated;

         procedure Note (Name : String; Kind : String) is
         begin
            if Is_Generated (Name) then
               return;
            end if;
            for I in Seen.First_Index .. Seen.Last_Index loop
               if SU.To_String (Seen.Element (I)) = Name then
                  Error ("duplicate declaration of '" & Name
                         & "' (" & Kind & "): a name shall be declared at "
                         & "most once in a scope (spec 5.17)");
                  return;
               end if;
            end loop;
            Seen.Append (SU.To_Unbounded_String (Name));
         end Note;
      begin
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            Note (SU.To_String (U.Structs.Element (I).Name), "struct");
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            Note (SU.To_String (U.Enums.Element (I).Name), "enum");
         end loop;
         for I in U.Traits.First_Index .. U.Traits.Last_Index loop
            Note (SU.To_String (U.Traits.Element (I).Name), "trait");
         end loop;
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            Note (SU.To_String (U.Consts.Element (I).Name), "const");
         end loop;
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            Note (SU.To_String (U.Statics.Element (I).Name), "static");
         end loop;
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Note (SU.To_String (U.Fns.Element (I).Header.Name), "fn");
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Note (SU.To_String (U.Gen_Fns.Element (I).Header.Name), "fn");
         end loop;
         --  §10.6: a `module` shall not share a name with another
         --  declaration in the same scope. A top-level module keeps its
         --  bare declared name in U.Module_Names; a nested module's name
         --  is '$'-prefixed by its enclosing module at Close_Module and
         --  is therefore already excluded by Is_Generated, same as any
         --  other mangled name.
         for I in U.Module_Names.First_Index .. U.Module_Names.Last_Index
         loop
            Note (SU.To_String (U.Module_Names.Element (I)), "module");
         end loop;
      end;

      --  §5.5 field-name uniqueness within a named composite (the anonymous
      --  `?` padding field is exempt) and §5.1 parameter-name uniqueness.
      declare
         procedure Check_Unique_Fields
           (Owner : String; Fields : Struct_Field_Vectors.Vector) is
         begin
            for I in Fields.First_Index .. Fields.Last_Index loop
               declare
                  N : constant String :=
                    SU.To_String (Fields.Element (I).Name);
               begin
                  if N /= "" and then N /= "?" then
                     for J in Fields.First_Index .. I - 1 loop
                        if SU.To_String (Fields.Element (J).Name) = N then
                           Error ("duplicate field '" & N & "' in " & Owner
                                  & " (spec 5.5)");
                        end if;
                     end loop;
                  end if;
               end;
            end loop;
         end Check_Unique_Fields;

         --  §5.9 generic type-parameter names shall be distinct. Shared by
         --  fn/struct/enum generic clauses — `Owner` names the declaration
         --  for the diagnostic.
         procedure Check_Unique_Generics
           (Owner : String; G : Generic_Param_Vectors.Vector) is
         begin
            for I in G.First_Index .. G.Last_Index loop
               for J in G.First_Index .. I - 1 loop
                  if SU.To_String (G.Element (J).Name)
                       = SU.To_String (G.Element (I).Name)
                  then
                     Error ("duplicate generic parameter '"
                            & SU.To_String (G.Element (I).Name)
                            & "' in '" & Owner
                            & "' (spec 5.9)");
                  end if;
               end loop;
            end loop;
         end Check_Unique_Generics;

         procedure Check_Unique_Params (H : Fn_Header) is
         begin
            Check_Unique_Generics (SU.To_String (H.Name), H.Generic_Params);
            for I in H.Params.First_Index .. H.Params.Last_Index loop
               declare
                  N : constant String :=
                    SU.To_String (H.Params.Element (I).Name);
               begin
                  if N /= "" then
                     for J in H.Params.First_Index .. I - 1 loop
                        if SU.To_String (H.Params.Element (J).Name) = N then
                           Error ("duplicate parameter '" & N
                                  & "' in subroutine '"
                                  & SU.To_String (H.Name) & "' (spec 5.1)");
                        end if;
                     end loop;
                  end if;
               end;
            end loop;
         end Check_Unique_Params;
      begin
         --  NOTE: struct/enum generic-parameter duplicate-name rejection
         --  (spec 5.9) is checked at parse time (Parse_Struct_Decl /
         --  Parse_Enum_Decl), not here: by the time Kurt.Sema.Check runs,
         --  Kurt.Mono.Monomorphize has already lifted generic struct/enum
         --  templates out of U.Structs/U.Enums into its own local
         --  worklists, so this pass never sees them (unlike U.Gen_Fns,
         --  which the Unit type does expose).
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            Check_Unique_Fields
              ("struct '" & SU.To_String (U.Structs.Element (I).Name) & "'",
               U.Structs.Element (I).Fields);
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            declare
               EnV : Enum_Variant_Vectors.Vector renames
                 U.Enums.Element (I).Variants;
               EnN : constant String :=
                 SU.To_String (U.Enums.Element (I).Name);
               Wilds : Natural := 0;
            begin
               for V in EnV.First_Index .. EnV.Last_Index loop
                  Check_Unique_Fields
                    ("variant '" & SU.To_String (EnV.Element (V).Name) & "'",
                     EnV.Element (V).Payload);
                  --  §5.7 at most one `#wild#` variant per enum.
                  if EnV.Element (V).Is_Wild then
                     Wilds := Wilds + 1;
                     if Wilds = 2 then
                        Error ("enum '" & EnN & "' declares more than one "
                               & "`#wild#` variant (spec 5.7)");
                     end if;
                  end if;
                  --  §5.7 variant-name uniqueness within the enum.
                  for W in EnV.First_Index .. V - 1 loop
                     if SU.To_String (EnV.Element (W).Name)
                          = SU.To_String (EnV.Element (V).Name)
                     then
                        Error ("duplicate variant '"
                               & SU.To_String (EnV.Element (V).Name)
                               & "' in enum '" & EnN & "' (spec 5.7)");
                     end if;
                  end loop;
                  --  §5.7 discriminant collision (explicit values and
                  --  `#wild#(V)` canonical values must be distinct).
                  for W in EnV.First_Index .. V - 1 loop
                     if EnV.Element (W).Value = EnV.Element (V).Value then
                        Error ("discriminant value"
                               & Long_Long_Integer'Image (EnV.Element (V).Value)
                               & " of variant '"
                               & SU.To_String (EnV.Element (V).Name)
                               & "' collides with variant '"
                               & SU.To_String (EnV.Element (W).Name)
                               & "' in enum '" & EnN & "' (spec 5.7)");
                     end if;
                  end loop;
               end loop;
            end;
         end loop;
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Check_Unique_Params (U.Fns.Element (I).Header);
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Check_Unique_Params (U.Gen_Fns.Element (I).Header);
         end loop;
      end;

      --  Phase 1: collect signatures (fns and @dyn prototypes).
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            Fn : constant Fn_Decl := U.Fns.Element (I);
         begin
            Sigs.Append
              ((Name         => Fn.Header.Name,
                Params       => Fn.Header.Params,
                Ret          => Fn.Header.Return_Type,
                Is_Variadic  => Fn.Header.Is_Variadic,
                Is_Never     => Fn.Header.Is_Never,
                Extern_Iface => Fn.Header.Extern_Iface,
                Is_Pub       => Fn.Header.Is_Pub));
         end;
      end loop;

      for I in U.Dyns.First_Index .. U.Dyns.Last_Index loop
         declare
            D : constant Dyn_Decl := U.Dyns.Element (I);
         begin
            for J in D.Items.First_Index .. D.Items.Last_Index loop
               declare
                  P : constant Fn_Proto := D.Items.Element (J);
               begin
                  Sigs.Append
                    ((Name         => P.Name,
                      Params       => P.Params,
                      Ret          => P.Return_Type,
                      Is_Variadic  => P.Is_Variadic,
                      Is_Never     => P.Is_Never,
                      Extern_Iface => P.Extern_Iface,
                      Is_Pub       => P.Is_Pub));
                  Dyn_Fn_Names.Append (P.Name);   --  §10.4 airside-only
               end;
            end loop;
         end;
      end loop;

      --  §9.8.5 destruct-family bound obligations deferred by Kurt.Mono:
      --  `T: destruct` rejects a non-destruct argument, `T: !destruct`
      --  rejects a destruct-satisfying one.
      for BC of U.Bound_Checks loop
         declare
            Sat : constant Boolean :=
              Kurt.Layout.Satisfies_Destruct (BC.Ty);
            B   : constant String := SU.To_String (BC.Bound);
         begin
            if B = "destruct" and then not Sat then
               Error ("type '" & Image (BC.Ty) & "' does not satisfy "
                      & "`destruct`, required by parameter '"
                      & SU.To_String (BC.Param) & "' of '"
                      & SU.To_String (BC.Ctx) & "' (spec 9.8.5)");
            elsif B = "!destruct" and then Sat then
               Error ("type '" & Image (BC.Ty) & "' satisfies `destruct` "
                      & "but parameter '" & SU.To_String (BC.Param)
                      & "' of '" & SU.To_String (BC.Ctx)
                      & "' requires `!destruct` (spec 9.8.5)");
            end if;
         end;
      end loop;

      --  §4.11.3: validate enum discriminant declarations. `with
      --  discrim(T)` shall name an integer type and every declared
      --  value shall fit in T; violations are translation failures.
      Validate_Enums;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            D : constant Kurt.Parser.Struct_Decl := U.Structs.Element (I);
            M : Cell_Count := D.Align_N;
         begin
            while M > 1 and then M mod 2 = 0 loop
               M := M / 2;
            end loop;
            if D.Align_N > 0 and then M /= 1 then
               Error ("struct '" & SU.To_String (D.Name)
                      & "': align(" & Cell_Count'Image (D.Align_N)
                      & " ) shall be a power of two (spec 4.11.5)");
            end if;

            --  §5.5.3: type-check each default-value expression against its
            --  field type (and give it a Sem_Ty for codegen to lower).
            for J in D.Fields.First_Index .. D.Fields.Last_Index loop
               declare
                  Fld : constant Struct_Field := D.Fields.Element (J);
               begin
                  if Fld.Default /= null then
                     declare
                        DT : constant Type_Access :=
                          Infer (Fld.Default, Fld.Ty);
                     begin
                        if Fld.Ty /= null and then not Assignable (Fld.Ty, DT)
                        then
                           Error ("struct '" & SU.To_String (D.Name)
                                  & "': default for field '"
                                  & SU.To_String (Fld.Name) & "' is '"
                                  & Image (DT) & "' but the field is '"
                                  & Image (Fld.Ty) & "' (spec 5.5.3)");
                        elsif not Is_Xlatime_Foldable (Fld.Default) then
                           --  §5.5.3: a field default is materialized once,
                           --  at translation time, into every struct
                           --  literal that omits the field -- it shall be
                           --  translation-time evaluable, exactly like a
                           --  const initializer (a runtime fn call or a
                           --  static read is not).
                           Error ("struct '" & SU.To_String (D.Name)
                                  & "': default for field '"
                                  & SU.To_String (Fld.Name)
                                  & "' is not evaluable at translation "
                                  & "time (spec 5.5.3, bootstrap subset: "
                                  & "literals, type intrinsics, consts, "
                                  & "aggregate literals over those, and "
                                  & "pure operators)");
                        end if;
                     end;
                  end if;
               end;
            end loop;
         end;
      end loop;

      --  §5.3 / §5.4: validate const and static declarations. Both
      --  initializers shall be translation-time evaluable; the bootstrap
      --  folds const values at use sites and emits static objects as
      --  data-section constants, so the accepted forms are restricted
      --  accordingly.
      Validate_Consts_Statics;

      --  Phase 2: analyse each fn body. Expr/Stmt nodes are heap-
      --  allocated and reached through access values, so mutating
      --  Sem_Ty updates the shared nodes in place; the vector elements
      --  (which hold those access values) need no write-back.
      --
      --  Concrete fns (incl. monomorphised instances) are checked with
      --  an empty generic context; §5.9 templates are checked ONCE under
      --  the type-erasure rule with their parameters abstract.
      Check_Fn_Bodies;

      --  §4.6: a dynamically-sized array `[T]` shall not appear as a
      --  parameter, return, struct-field, or enum-payload-field type (other
      --  than as a reference target). `let`/`mut` annotations are checked in
      --  Check_Stmt.
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         declare
            H : Fn_Header renames U.Fns.Element (I).Header;
         begin
            for P in H.Params.First_Index .. H.Params.Last_Index loop
               if Is_Unsized_Value (H.Params.Element (P).Ty) then
                  Error ("`[T]`/`dyn Trait` cannot be a parameter type "
                         & "(use a reference) (spec 4.6/9.5)");
               end if;
            end loop;
            if Is_Unsized_Value (H.Return_Type) then
               Error ("`[T]`/`dyn Trait` cannot be a return type "
                      & "(use a reference) (spec 4.6/9.5)");
            end if;
         end;
      end loop;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            SD : Struct_Decl renames U.Structs.Element (I);
         begin
            for Fi in SD.Fields.First_Index .. SD.Fields.Last_Index loop
               if Is_Unsized_Value (SD.Fields.Element (Fi).Ty) then
                  Error ("`[T]`/`dyn Trait` cannot be a struct field type "
                         & "(use a reference) (spec 4.6/9.5)");
               end if;
            end loop;
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            ED : Enum_Decl renames U.Enums.Element (I);
         begin
            for Vi in ED.Variants.First_Index .. ED.Variants.Last_Index loop
               declare
                  P : Struct_Field_Vectors.Vector renames
                    ED.Variants.Element (Vi).Payload;
               begin
                  for Fi in P.First_Index .. P.Last_Index loop
                     if Is_Unsized_Value (P.Element (Fi).Ty) then
                        Error ("`[T]`/`dyn Trait` cannot be an enum "
                               & "payload field type (use a reference) "
                               & "(spec 4.6/9.5)");
                     end if;
                  end loop;
               end;
            end loop;
         end;
      end loop;

      --  §9.2.1: two trait impls on one type providing the same method name do
      --  NOT collide at declaration time (they mangle to distinct
      --  `Type$Trait$method` symbols); the collision is resolved at each
      --  invocation — a bare `e.m()` with two providers is the TF, and
      --  `(e as Trait).m()` always disambiguates. Both are handled at the call
      --  site (see Resolve_Item_Symbol), so no declaration-time check here.

      --  §9.4.1 orphan rule: a trait implementation is permitted only when
      --  the trait declaration or the implementing type declaration is in
      --  the current translation unit. Kadayif translates one unit per run
      --  (`@add` merges into it), so the only reachable violation is an
      --  `impl ... as Trait` naming a trait this unit never declares --
      --  which is simultaneously a name-resolution failure. Rejecting it
      --  here enforces both readings.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            Tr : constant String :=
              SU.To_String (U.Trait_Impls.Element (I).Trait_Name);
         begin
            if Tr'Length > 0 and then not Is_Trait_Name (Tr) then
               Error ("`impl "
                      & SU.To_String (U.Trait_Impls.Element (I).Ty_Name)
                      & " as " & Tr & "`: no trait named '" & Tr
                      & "' is declared in this translation unit "
                      & "(spec 9.4.1)");
            end if;
         end;
      end loop;

      --  §9.4.2 duplicate detection: a type shall implement a given trait at
      --  most once within the translation unit.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         for J in I + 1 .. U.Trait_Impls.Last_Index loop
            if SU.Length (U.Trait_Impls.Element (I).Trait_Name) > 0
              and then SU.To_String (U.Trait_Impls.Element (I).Ty_Name)
                 = SU.To_String (U.Trait_Impls.Element (J).Ty_Name)
              and then SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                 = SU.To_String (U.Trait_Impls.Element (J).Trait_Name)
            then
               Error ("type '"
                      & SU.To_String (U.Trait_Impls.Element (I).Ty_Name)
                      & "' implements trait '"
                      & SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                      & "' more than once (spec 9.4.2)");
            end if;
         end loop;
      end loop;

      --  §9.1: an inherent `impl Type { ... }` (no `as Trait`) shall not
      --  define associated types -- `type Item = ...;` is a trait-impl-only
      --  construct (§9.3.1). Silently discarding it would leave a
      --  `selftype::Item` reference resolved against nothing.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
         begin
            if SU.Length (TI.Trait_Name) = 0
              and then not TI.Assoc_Types.Is_Empty
            then
               Error ("inherent `impl " & SU.To_String (TI.Ty_Name)
                      & "` defines associated type '"
                      & SU.To_String (TI.Assoc_Types.First_Element.Name)
                      & "' -- associated types are permitted only in a "
                      & "trait impl (`impl " & SU.To_String (TI.Ty_Name)
                      & " as Trait`) (spec 9.1)");
            end if;
         end;
      end loop;

      --  §9.1: two items (methods / associated fns) with the same mangled
      --  symbol on one type — e.g. two inherent `impl Type { fn a }` blocks —
      --  are a declaration-time TF (they would otherwise collide in codegen).
      for I in U.Fns.First_Index .. U.Fns.Last_Index loop
         for J in I + 1 .. U.Fns.Last_Index loop
            if SU.To_String (U.Fns.Element (I).Header.Name)
                 = SU.To_String (U.Fns.Element (J).Header.Name)
            then
               Error ("duplicate definition of '"
                      & SU.To_String (U.Fns.Element (I).Header.Name)
                      & "' (two items with the same name on one type, "
                      & "spec 9.1)");
            end if;
         end loop;
      end loop;

      --  §9.4: an `impl Type as Trait` shall provide every trait method that
      --  has no default body. A missing one would otherwise fail at link time.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Tr : constant String := SU.To_String (TI.Trait_Name);

            function Impl_Provides (Nm : String) return Boolean is
            begin
               for K in TI.Methods.First_Index .. TI.Methods.Last_Index loop
                  if SU.To_String (TI.Methods.Element (K)) = Nm then
                     return True;
                  end if;
               end loop;
               return False;
            end Impl_Provides;
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  for M in U.Traits.Element (T).Methods.First_Index ..
                           U.Traits.Element (T).Methods.Last_Index loop
                     declare
                        TM : Trait_Method renames
                          U.Traits.Element (T).Methods.Element (M);
                        MN : constant String := SU.To_String (TM.Sig.Name);
                     begin
                        if not TM.Has_Body and then not Impl_Provides (MN) then
                           Error ("`impl " & SU.To_String (TI.Ty_Name)
                                  & " as " & Tr & "` does not provide method '"
                                  & MN & "' (spec 9.4)");
                        end if;
                     end;
                  end loop;
               end if;
            end loop;
         end;
      end loop;

      --  §9.5 dyn-safety: a trait with a generic method is not a legal
      --  `&dyn Trait`/`$dyn Trait` target -- forming its dispatch table
      --  would need a vtable slot for a method that is never lowered
      --  under a fixed (unmonomorphised) symbol, an undetected translation
      --  failure that would otherwise surface only as a LINKER error.
      --  The bootstrap builds one static dispatch table per concrete
      --  `impl Type as Trait` unconditionally (not only when a `dyn`
      --  reference is actually formed), so the failure is raised here,
      --  at every such impl of a non-object-safe trait.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Tr : constant String := SU.To_String (TI.Trait_Name);
         begin
            if Tr /= "" then
               for T in U.Traits.First_Index .. U.Traits.Last_Index loop
                  if SU.To_String (U.Traits.Element (T).Name) = Tr then
                     for M in U.Traits.Element (T).Methods.First_Index ..
                              U.Traits.Element (T).Methods.Last_Index
                     loop
                        declare
                           TM : Trait_Method renames
                             U.Traits.Element (T).Methods.Element (M);
                        begin
                           if not TM.Sig.Generic_Params.Is_Empty then
                              Error ("trait '" & Tr & "' has a generic "
                                     & "method '"
                                     & SU.To_String (TM.Sig.Name)
                                     & "' and is not a valid "
                                     & "`&dyn`/`$dyn` target; `impl "
                                     & SU.To_String (TI.Ty_Name) & " as "
                                     & Tr & "` cannot form a dispatch "
                                     & "table for it (spec 9.5)");
                           end if;
                           --  §9.5: "No method shall return `selftype` by
                           --  value." A by-value `selftype` return has no
                           --  fixed size under erasure (the concrete type
                           --  is only known per-implementor), so it cannot
                           --  be a dispatch-table slot. `&selftype`/
                           --  `$selftype` returns are T_Ref, not T_Named,
                           --  so they never match this check.
                           if TM.Sig.Return_Type /= null
                             and then TM.Sig.Return_Type.Kind = T_Named
                             and then SU.To_String (TM.Sig.Return_Type.Name)
                                      = "selftype"
                           then
                              Error ("trait '" & Tr & "' has method '"
                                     & SU.To_String (TM.Sig.Name)
                                     & "' returning `selftype` by value "
                                     & "and is not a valid "
                                     & "`&dyn`/`$dyn` target; `impl "
                                     & SU.To_String (TI.Ty_Name) & " as "
                                     & Tr & "` cannot form a dispatch "
                                     & "table for it (spec 9.5)");
                           end if;
                        end;
                     end loop;
                  end if;
               end loop;
            end if;
         end;
      end loop;

      --  §9.3.1 associated-type completeness: an `impl T as Trait` shall
      --  define every associated type the trait leaves without a default, and
      --  shall not define one the trait does not declare.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Tr : constant String := SU.To_String (TI.Trait_Name);

            function Impl_Defines (Nm : String) return Boolean is
            begin
               for K in TI.Assoc_Types.First_Index ..
                        TI.Assoc_Types.Last_Index loop
                  if SU.To_String (TI.Assoc_Types.Element (K).Name) = Nm then
                     return True;
                  end if;
               end loop;
               return False;
            end Impl_Defines;
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  declare
                     TD : Trait_Decl renames U.Traits.Element (T);

                     function Trait_Has (Nm : String) return Boolean is
                     begin
                        for K in TD.Assoc_Types.First_Index ..
                                 TD.Assoc_Types.Last_Index loop
                           if SU.To_String (TD.Assoc_Types.Element (K).Name)
                                = Nm
                           then
                              return True;
                           end if;
                        end loop;
                        return False;
                     end Trait_Has;
                  begin
                     --  Every required (no-default) trait assoc type defined?
                     for K in TD.Assoc_Types.First_Index ..
                              TD.Assoc_Types.Last_Index loop
                        if TD.Assoc_Types.Element (K).Ty = null
                          and then not Impl_Defines
                            (SU.To_String (TD.Assoc_Types.Element (K).Name))
                        then
                           Error ("impl of trait '" & Tr & "' for type '"
                             & SU.To_String (TI.Ty_Name)
                             & "' is missing associated type '"
                             & SU.To_String (TD.Assoc_Types.Element (K).Name)
                             & "' (spec 9.3.1)");
                        end if;
                     end loop;
                     --  No def for an associated type the trait lacks?
                     for K in TI.Assoc_Types.First_Index ..
                              TI.Assoc_Types.Last_Index loop
                        if not Trait_Has
                          (SU.To_String (TI.Assoc_Types.Element (K).Name))
                        then
                           Error ("impl defines associated type '"
                             & SU.To_String (TI.Assoc_Types.Element (K).Name)
                             & "' not declared by trait '" & Tr
                             & "' (spec 9.3.1)");
                        end if;
                     end loop;
                  end;
               end if;
            end loop;
         end;
      end loop;

      --  §9.3.3 supertrait satisfaction: a type that implements a trait with
      --  supertrait bounds shall also implement every required supertrait.
      for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
         declare
            TI : Trait_Impl renames U.Trait_Impls.Element (I);
            Ty : constant String := SU.To_String (TI.Ty_Name);
            Tr : constant String := SU.To_String (TI.Trait_Name);
         begin
            for T in U.Traits.First_Index .. U.Traits.Last_Index loop
               if SU.To_String (U.Traits.Element (T).Name) = Tr then
                  declare
                     TD : Trait_Decl renames U.Traits.Element (T);
                  begin
                     for S in TD.Supertraits.First_Index ..
                              TD.Supertraits.Last_Index
                     loop
                        declare
                           Sup : constant String :=
                             SU.To_String (TD.Supertraits.Element (S));
                        begin
                           if not Type_Implements (Ty, Sup) then
                              Error ("type '" & Ty & "' implements trait '"
                                     & Tr & "' but not its supertrait '"
                                     & Sup & "' (spec 9.3.3)");
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            end loop;
         end;
      end loop;

      Error_Count := Errors;
   end Check;
