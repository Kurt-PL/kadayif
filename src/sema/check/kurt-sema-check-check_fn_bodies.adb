separate (Kurt.Sema.Check)
   procedure Check_Fn_Bodies is
         procedure Check_Fn (Fn : Fn_Decl) is
         begin
            Cur_Fn_Name := Fn.Header.Name;
            Cur_Generics := Fn.Header.Generic_Params;
            Scope.Clear;
            Kurt.Borrow.Clear (Borrows);
            Moved.Clear;
            Init_States.Clear;
            for J in Fn.Header.Params.First_Index ..
                     Fn.Header.Params.Last_Index
            loop
               declare
                  P : constant Param := Fn.Header.Params.Element (J);
               begin
                  if SU.Length (P.Name) > 0 then
                     Scope.Append ((Name => P.Name, Ty => P.Ty, Is_Mut => P.Is_Mut));
                  end if;
               end;
            end loop;

            if Fn.Header.Return_Type /= null then
               Cur_Ret := Fn.Header.Return_Type;
            elsif Fn.Header.Is_Closure then
               --  §9.9 a closure that omits `-> U` infers its return type
               --  from its body's first `return` (params already in scope).
               declare
                  RT : Type_Access := null;
               begin
                  for S of Fn.Body_Stmts loop
                     if S.Kind = S_Return and then S.R_Val /= null then
                        RT := Infer (S.R_Val, null);
                        exit;
                     end if;
                  end loop;
                  Cur_Ret := (if RT /= null then RT else Mk_Named ("void"));
               end;
            else
               Cur_Ret := Mk_Named ("void");
            end if;

            --  §5.1.1: the whole body of an `airside fn` is an airside
            --  region (§6.1.8 lets `uninit` appear there).
            In_Airside := (if Fn.Header.Is_Airside then 1 else 0);
            --  §7.6: a `-> never` subroutine's body shall not contain a
            --  `return` statement at all.
            Cur_Is_Never := Fn.Header.Is_Never;
            for J in Fn.Body_Stmts.First_Index ..
                     Fn.Body_Stmts.Last_Index
            loop
               Check_Stmt (Fn.Body_Stmts.Element (J));
            end loop;
            Cur_Is_Never := False;
            In_Airside := 0;

            --  §5.2/§8.4: the outermost fn-body "scope" is walked directly
            --  above (not via Check_Block, which handles every NESTED
            --  block's own scope exit), so its own deferred-init bindings
            --  need the same scope-exit destruction-obligation check here.
            for I in Init_States.First_Index .. Init_States.Last_Index loop
               if Init_States.Element (I).State = St_Maybe
                 and then Satisfies_Destruct (Init_States.Element (I).Ty)
               then
                  Error ("binding '"
                         & SU.To_String (Init_States.Element (I).Name)
                         & "' is initialized on some but not all paths "
                         & "reaching the end of its scope, and its type "
                         & "has a destructor -- the destruction "
                         & "obligation cannot be proven either way "
                         & "(spec 5.2/8.4)");
               end if;
            end loop;
            Init_States.Clear;

            --  §4.10/§7.11: a `-> never` subroutine's body shall diverge —
            --  control shall not be able to reach its end.
            if Fn.Header.Is_Never
              and then not Stmts_Diverge (Fn.Body_Stmts)
            then
               Error ("body of '-> never' subroutine '"
                      & SU.To_String (Fn.Header.Name)
                      & "' can fall through; it shall diverge "
                      & "(spec 4.10/7.11)");
            end if;
         end Check_Fn;
         --  §5.9.2/§9.1: an impl(...) method's `self` parameter still
         --  carries the `selftype` placeholder verbatim (Kurt.Mono only
         --  rewrites it -- via its own Subst_Self_Name -- when the owner
         --  is actually instantiated). Rewrite it here, in place, to the
         --  bare (still-generic) owner name, so Infer_Field's
         --  U.Gen_Structs fallback can find it. Safe to mutate in place:
         --  Kurt.Mono.Monomorphize has already run and generated every
         --  instance it will from this template by the time Kurt.Sema.
         --  Check runs.
         procedure Rewrite_Selftype (T : Type_Access; Owner : String) is
         begin
            if T = null then
               return;
            end if;
            case T.Kind is
               when T_Named =>
                  if SU.To_String (T.Name) = "selftype" then
                     T.Name := SU.To_Unbounded_String (Owner);
                  end if;
                  for I in T.Args.First_Index .. T.Args.Last_Index loop
                     Rewrite_Selftype (T.Args.Element (I), Owner);
                  end loop;
               when T_Ref =>
                  Rewrite_Selftype (T.Target, Owner);
               when T_Array =>
                  Rewrite_Selftype (T.Elem, Owner);
               when T_Tuple =>
                  for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                     Rewrite_Selftype (T.Elems.Element (I), Owner);
                  end loop;
               when T_Dyn =>
                  null;
               when T_Fn =>
                  for I in T.Fn_Params.First_Index ..
                           T.Fn_Params.Last_Index
                  loop
                     Rewrite_Selftype (T.Fn_Params.Element (I), Owner);
                  end loop;
                  Rewrite_Selftype (T.Fn_Ret, Owner);
            end case;
         end Rewrite_Selftype;
         --  §5.9.2/§9.1: template-check every impl(...) generic method
         --  once, exactly like a top-level Gen_Fn -- otherwise a method
         --  on a generic impl that no instantiation anywhere in the unit
         --  ever exercises would never be checked at all (Kurt.Mono only
         --  copies+checks a Gen_Method's body when its owner is actually
         --  instantiated). The impl's own generic parameters (GM.
         --  Gen_Params, e.g. the `T` of `impl(T) pair.<T>`) are the
         --  template's abstract type variables.
         procedure Check_Gen_Methods is
         begin
            for I in U.Gen_Methods.First_Index ..
                     U.Gen_Methods.Last_Index
            loop
               declare
                  GM    : constant Gen_Method := U.Gen_Methods.Element (I);
                  Owner : constant String := SU.To_String (GM.Owner);
                  Tmpl  : Fn_Decl := GM.Method;
               begin
                  Tmpl.Header.Generic_Params := GM.Gen_Params;
                  for J in Tmpl.Header.Params.First_Index ..
                           Tmpl.Header.Params.Last_Index
                  loop
                     Rewrite_Selftype
                       (Tmpl.Header.Params.Element (J).Ty, Owner);
                  end loop;
                  Rewrite_Selftype (Tmpl.Header.Return_Type, Owner);
                  Check_Fn (Tmpl);
               end;
            end loop;
         end Check_Gen_Methods;
         --  §8.11: type- and borrow-check each `with destruct { ... }` block
         --  as codegen will lower it — with `self` bound to an exclusive
         --  reference to the object being destroyed (`$selftype`). Synthesised
         --  here so the block is held to the same rules as any subroutine.
         procedure Check_Destruct (Nm : String; Block : Stmt_Vectors.Vector) is
            D : Fn_Decl;
            P : Param;
         begin
            if Block.Is_Empty then
               return;
            end if;
            P.Name           := SU.To_Unbounded_String ("self");
            P.Ty             := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil       := R_Excl;
            P.Ty.Target      := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String (Nm);
            D.Header.Name    := SU.To_Unbounded_String (Nm & "$destruct");
            D.Header.Params.Append (P);
            D.Body_Stmts     := Block;
            Check_Fn (D);
         end Check_Destruct;
         --  §7.10.1: type- and borrow-check the single translation-unit
         --  `@trap { ... }` handler, held to the same rules as any
         --  subroutine (it takes no parameters and returns `void`), and
         --  require it to diverge -- control shall not fall off its end.
         procedure Check_Trap_Handler is
            D : Fn_Decl;
         begin
            D.Header.Name := SU.To_Unbounded_String ("@trap$handler");
            D.Body_Stmts  := U.Trap_Handler;
            Check_Fn (D);
            if not Stmts_Diverge (U.Trap_Handler) then
               Error ("`@trap` handler can fall through; it shall "
                      & "diverge (spec 7.10.1)");
            end if;
         end Check_Trap_Handler;
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Check_Fn (U.Fns.Element (I));
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Check_Fn (U.Gen_Fns.Element (I));
         end loop;
         Check_Gen_Methods;
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            if U.Structs.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Structs.Element (I).Name),
                               U.Structs.Element (I).Destruct_Block);
            end if;
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if U.Enums.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Enums.Element (I).Name),
                               U.Enums.Element (I).Destruct_Block);
            end if;
         end loop;
         if U.Has_Trap_Handler then
            Check_Trap_Handler;
         end if;
   end Check_Fn_Bodies;
