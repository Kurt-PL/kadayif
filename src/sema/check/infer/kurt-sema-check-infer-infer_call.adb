separate (Kurt.Sema.Check.Infer)
   function Infer_Call return Type_Access is
   begin
            --  §10.4 a subroutine declared in a `@dyn` block may be
            --  invoked only within an `airside` region. The callee is a
            --  single-segment path holding the mangled `alias$item` name.
            if In_Airside = 0
              and then E.C_Callee.Kind = E_Path
              and then Natural (E.C_Callee.Segments.Length) = 1
            then
               declare
                  CN : constant String :=
                    SU.To_String (E.C_Callee.Segments.Last_Element);
               begin
                  for I in Dyn_Fn_Names.First_Index
                           .. Dyn_Fn_Names.Last_Index loop
                     if SU.To_String (Dyn_Fn_Names.Element (I)) = CN then
                        declare
                           Disp : SU.Unbounded_String;   --  `alias::item`
                        begin
                           for K in CN'Range loop
                              if CN (K) = '$' then
                                 SU.Append (Disp, "::");
                              else
                                 SU.Append (Disp, CN (K));
                              end if;
                           end loop;
                           Error ("`@dyn` subroutine '" & SU.To_String (Disp)
                                  & "' may be invoked only within an "
                                  & "`airside` region (spec 10.4)");
                        end;
                        exit;
                     end if;
                  end loop;
               end;
            end if;
            --  §6.2.3 method invocation: `e.m(args)` resolves to the
            --  inherent method `T$m` and desugars to a plain call with
            --  the receiver as first argument (§6.2.6 auto-referencing:
            --  a non-reference receiver is wrapped in `&`/`$` to match
            --  the self parameter; a reference receiver passes through).
            if E.C_Callee.Kind = E_Field then
               --  §6.2.3 qualified method invocation `(e as Trait).m(args)`:
               --  the receiver is a cast to a *trait* name. Validate that
               --  e's concrete type implements the trait and that the trait
               --  declares the method, then strip the cast so resolution
               --  proceeds against e's concrete type (the trait method is
               --  mangled identically to the inherent `Type$m`).
               if E.C_Callee.F_Recv.Kind = E_Cast
                 and then not E.C_Callee.F_Recv.Cast_Bang
                 and then not E.C_Callee.F_Recv.Cast_Disc
                 and then E.C_Callee.F_Recv.Cast_Ty /= null
                 and then E.C_Callee.F_Recv.Cast_Ty.Kind = T_Named
                 and then Is_Trait_Name
                            (SU.To_String (E.C_Callee.F_Recv.Cast_Ty.Name))
               then
                  declare
                     QTrait : constant String :=
                       SU.To_String (E.C_Callee.F_Recv.Cast_Ty.Name);
                     QInner : constant Expr_Access :=
                       E.C_Callee.F_Recv.Cast_Inner;
                     QMName : constant String :=
                       SU.To_String (E.C_Callee.F_Name);
                     QT  : constant Type_Access := Infer (QInner, null);
                     QTT : constant Type_Access :=
                       (if Is_Ref (QT) then QT.Target else QT);
                     MSig : Fn_Header;
                     MOK  : Boolean;
                  begin
                     if QTT /= null and then QTT.Kind = T_Named then
                        if not Type_Implements
                                 (SU.To_String (QTT.Name), QTrait)
                        then
                           Error ("type '" & SU.To_String (QTT.Name)
                                  & "' does not implement trait '" & QTrait
                                  & "' in qualified method `(e as " & QTrait
                                  & ").` (spec 6.2.3)");
                        else
                           Lookup_Trait_Method (QTrait, QMName, MSig, MOK);
                           if not MOK then
                              Error ("trait '" & QTrait
                                     & "' has no method '" & QMName
                                     & "' (spec 6.2.3)");
                           end if;
                        end if;
                     end if;
                     --  Strip the trait cast and force the trait so
                     --  resolution selects `Type$Trait$method`.
                     E.C_Callee.F_Recv := QInner;
                     E.C_Callee.F_Trait :=
                       SU.To_Unbounded_String (QTrait);
                  end;
               end if;
               declare
                  Recv : constant Expr_Access := E.C_Callee.F_Recv;
                  RT   : constant Type_Access := Infer (Recv, null);
                  RTT  : constant Type_Access :=
                    (if Is_Ref (RT) then RT.Target else RT);
                  S    : Sig;
               begin
                  --  §9.5 dynamic dispatch: a method call on a
                  --  `&dyn Trait` receiver. Validated against the trait
                  --  signature; the callee is left as E_Field so
                  --  codegen emits an indirect dispatch-table call.
                  if RTT /= null and then RTT.Kind = T_Dyn then
                     declare
                        MSig : Fn_Header;
                        MOK  : Boolean;
                     begin
                        Lookup_Trait_Method
                          (SU.To_String (RTT.Trait_Name),
                           SU.To_String (E.C_Callee.F_Name), MSig, MOK);
                        if not MOK then
                           Error ("trait '"
                                  & SU.To_String (RTT.Trait_Name)
                                  & "' has no method '"
                                  & SU.To_String (E.C_Callee.F_Name)
                                  & "' (spec 9.5)");
                           E.Sem_Ty := null;
                           return null;
                        end if;
                        --  §9.5 object-safety: a generic method cannot be
                        --  dispatched through a `&dyn` fat reference.
                        if not MSig.Generic_Params.Is_Empty then
                           Error ("method '"
                                  & SU.To_String (E.C_Callee.F_Name)
                                  & "' of trait '"
                                  & SU.To_String (RTT.Trait_Name)
                                  & "' is generic and is not object-safe; "
                                  & "it cannot be called through `&dyn` "
                                  & "(spec 9.5)");
                           E.Sem_Ty := null;
                           return null;
                        end if;
                        for K in E.C_Args.First_Index ..
                                 E.C_Args.Last_Index
                        loop
                           declare
                              Ig : constant Type_Access :=
                                Infer (E.C_Args.Element (K), null);
                              pragma Unreferenced (Ig);
                           begin null; end;
                        end loop;
                        E.Sem_Ty := MSig.Return_Type;
                        return E.Sem_Ty;
                     end;
                  end if;

                  --  §5.9/§9.3 type erasure: a method call on a generic
                  --  parameter is licensed by a trait bound. Validated
                  --  abstractly here against the trait signature; the
                  --  monomorphised instance resolves it to a concrete
                  --  `Type$method` via the path below. The template node
                  --  is left un-desugared (templates are never lowered).
                  if RTT /= null and then RTT.Kind = T_Named
                    and then Is_Generic_Param_Ty (RTT)
                  then
                     declare
                        MSig  : Fn_Header;
                        MOK   : Boolean;
                     begin
                        Find_Bound_Method
                          (SU.To_String (RTT.Name),
                           SU.To_String (E.C_Callee.F_Name), MSig, MOK);
                        if not MOK then
                           Error ("no trait bound on '" & Image (RTT)
                                  & "' provides method '"
                                  & SU.To_String (E.C_Callee.F_Name)
                                  & "' (spec 9.3)");
                           E.Sem_Ty := null;
                           return null;
                        end if;
                        for K in E.C_Args.First_Index ..
                                 E.C_Args.Last_Index
                        loop
                           declare
                              Ig : constant Type_Access :=
                                Infer (E.C_Args.Element (K), null);
                              pragma Unreferenced (Ig);
                           begin null; end;
                        end loop;
                        E.Sem_Ty :=
                          Subst_Self_T (MSig.Return_Type, RTT);
                        return E.Sem_Ty;
                     end;
                  end if;
                  if RTT /= null and then RTT.Kind = T_Named then
                     declare
                        Sym   : SU.Unbounded_String;
                        Fnd   : Boolean;
                        Amb   : Boolean;
                     begin
                        --  §9.2.1 inherent first, else unique trait impl;
                        --  `(e as Trait).m()` forces F_Trait.
                        Resolve_Item_Symbol
                          (SU.To_String (RTT.Name),
                           SU.To_String (E.C_Callee.F_Name),
                           SU.To_String (E.C_Callee.F_Trait),
                           Sym, Fnd, Amb);
                        if Amb then
                           Error ("call to method '"
                                  & SU.To_String (E.C_Callee.F_Name)
                                  & "' on '" & Image (RTT)
                                  & "' is ambiguous (provided by two or "
                                  & "more traits); disambiguate with "
                                  & "`(e as Trait)." & SU.To_String
                                    (E.C_Callee.F_Name) & "()` (spec 9.2.1)");
                           E.Sem_Ty := null;
                           return null;
                        elsif Fnd
                          and then Find_Sig (SU.To_String (Sym), S)
                        then
                           --  §5.12.1/§9.2: subroutines inside an `impl`
                           --  block inherit no visibility of their own --
                           --  each shall be individually marked `pub` for
                           --  external access. A non-`pub` method invoked
                           --  via `.method()` receiver syntax is therefore
                           --  callable only from the source unit that
                           --  declares the `impl`.
                           if not S.Is_Pub
                             and then not Kurt.Layout.Same_Source_Unit
                                            (SU.To_String (Sym),
                                             SU.To_String (Cur_Fn_Name))
                           then
                              Error ("method '"
                                     & SU.To_String (E.C_Callee.F_Name)
                                     & "' of '" & Image (RTT)
                                     & "' is not `pub` -- accessible only "
                                     & "within the source unit that "
                                     & "declares it (spec 5.12.1/9.2)");
                              E.Sem_Ty := null;
                              return null;
                           end if;
                           declare
                              Self_Ty : constant Type_Access :=
                                (if not S.Params.Is_Empty
                                 then S.Params.First_Element.Ty
                                 else null);
                              Recv_Arg : Expr_Access;
                              NP : constant Expr_Access :=
                                new Expr_Node (Kind => E_Path);
                           begin
                              if not Is_Ref (Self_Ty) then
                                 --  §9.2 by-value self (`self` / `mut
                                 --  self`): the receiver is passed by
                                 --  value, transferred like any by-value
                                 --  argument (Maybe_Move below) -- no
                                 --  auto-referencing. If the receiver
                                 --  expression is itself a reference, the
                                 --  ordinary argument-assignability check
                                 --  below rejects the mismatch.
                                 Recv_Arg := Recv;
                              elsif Is_Ref (RT) then
                                 Recv_Arg := Recv;
                              else
                                 Recv_Arg :=
                                   new Expr_Node (Kind => E_Ref);
                                 Recv_Arg.Rf_Sigil := Self_Ty.Sigil;
                                 Recv_Arg.Rf_Place := Recv;
                              end if;
                              E.C_Args.Prepend (Recv_Arg);
                              NP.Segments.Append (Sym);
                              E.C_Callee := NP;
                           end;
                        else
                           Error ("type '" & Image (RTT)
                                  & "' has no method '"
                                  & SU.To_String (E.C_Callee.F_Name)
                                  & "'"
                                  & (if SU.Length (E.C_Callee.F_Trait) > 0
                                     then " in trait '" & SU.To_String
                                       (E.C_Callee.F_Trait) & "'" else "")
                                  & " (spec 9.2.1)");
                           E.Sem_Ty := null;
                           return null;
                        end if;
                     end;
                  else
                     Error ("method receiver must be a named type, "
                            & "got '" & Image (RT) & "'");
                     E.Sem_Ty := null;
                     return null;
                  end if;
               end;
            end if;

            --  §5.9: an un-instantiated generic invocation
            --  `f.<T, ...>(args)` can only appear inside a template —
            --  Kurt.Mono rewrites every concrete call site to the
            --  instance name. Check the arguments abstractly; the
            --  result type would need substitution and is left
            --  unknown (downstream checks skip null types).
            if E.C_Callee.Kind = E_Path
              and then not E.C_Callee.P_Type_Args.Is_Empty
            then
               for I in E.C_Args.First_Index .. E.C_Args.Last_Index loop
                  declare
                     Ignore : constant Type_Access :=
                       Infer (E.C_Args.Element (I), null);
                     pragma Unreferenced (Ignore);
                  begin
                     null;
                  end;
               end loop;
               E.Sem_Ty := null;
               return null;
            end if;

            declare
               Callee : constant Expr_Access := E.C_Callee;
               Name   : SU.Unbounded_String;
               S      : Sig;
            begin
               if Callee.Kind = E_Path
                 and then not Callee.Segments.Is_Empty
               then
                  Name := Callee.Segments.Last_Element;
                  --  §6.1.1 associated subroutine `Type::fn(...)`: when the
                  --  final segment names no free subroutine but `Type$fn`
                  --  exists (Type = the preceding segment), resolve to the
                  --  associated function. No receiver is prepended (an
                  --  associated function has no `self`); a `self`-taking
                  --  method invoked this way receives its receiver as the
                  --  ordinary first argument.
                  if Natural (Callee.Segments.Length) >= 2 then
                     declare
                        Last_S : constant String := SU.To_String (Name);
                        Dummy  : Sig;
                     begin
                        if not Find_Sig (Last_S, Dummy) then
                           declare
                              Tn : constant String := SU.To_String
                                (Callee.Segments.Element
                                   (Callee.Segments.Last_Index - 1));
                              Sym : SU.Unbounded_String;
                              Fnd, Amb : Boolean;
                           begin
                              --  §6.1.1: inherent `Type$fn`, else unique
                              --  trait `Type$Trait$fn`; `Path_Trait` (from
                              --  `(Type as Trait)::fn`) forces the trait.
                              Resolve_Item_Symbol
                                (Tn, Last_S,
                                 SU.To_String (Callee.Path_Trait),
                                 Sym, Fnd, Amb);
                              if Amb then
                                 Error ("associated subroutine '" & Last_S
                                        & "' on '" & Tn & "' is ambiguous; "
                                        & "use `(" & Tn
                                        & " as Trait)::" & Last_S
                                        & "` (spec 9.2.1)");
                              elsif Fnd then
                                 declare
                                    NP : constant Expr_Access :=
                                      new Expr_Node (Kind => E_Path);
                                 begin
                                    NP.Segments.Append (Sym);
                                    E.C_Callee := NP;
                                    Name := Sym;
                                 end;
                              end if;
                           end;
                        end if;
                     end;
                  end if;
               end if;

               if Find_Sig (SU.To_String (Name), S) then
                  --  §6.2.1 argument-count check: a non-variadic call must
                  --  supply exactly one argument per parameter; a variadic
                  --  call must supply at least the fixed parameters.
                  declare
                     NA : constant Natural := Natural (E.C_Args.Length);
                     NP : constant Natural := Natural (S.Params.Length);
                  begin
                     if (S.Is_Variadic and then NA < NP)
                       or else (not S.Is_Variadic and then NA /= NP)
                     then
                        Error ("subroutine '" & SU.To_String (Name)
                               & "' expects"
                               & (if S.Is_Variadic then " at least" else "")
                               & Natural'Image (NP) & " argument(s), got"
                               & Natural'Image (NA) & " (spec 6.2.1)");
                     end if;
                  end;
                  --  Infer each argument, steering fixed-position
                  --  literals toward the declared parameter type.
                  for I in E.C_Args.First_Index .. E.C_Args.Last_Index
                  loop
                     declare
                        Pidx : constant Natural :=
                          S.Params.First_Index + (I - E.C_Args.First_Index);
                        Exp  : Type_Access := null;
                     begin
                        if Pidx <= S.Params.Last_Index then
                           Exp := S.Params.Element (Pidx).Ty;
                        end if;
                        declare
                           Arg_Ty : constant Type_Access :=
                             Infer (E.C_Args.Element (I), Exp);
                        begin
                           --  §8.9: `f(*r)` copies out through the
                           --  dereference.
                           Check_No_Destruct_Load (E.C_Args.Element (I));
                           --  §9.5 implicit coercion: `&T → &dyn Trait`
                           --  when T implements Trait. Wrap the argument
                           --  in an E_Dyn_Cast so codegen builds the fat
                           --  reference (value ptr + dispatch table).
                           if Exp /= null and then Is_Dyn_Ref (Exp)
                             and then Is_Ref (Arg_Ty)
                             and then Arg_Ty.Target /= null
                             and then Arg_Ty.Target.Kind = T_Named
                             and then Type_Implements
                               (SU.To_String (Arg_Ty.Target.Name),
                                SU.To_String (Exp.Target.Trait_Name))
                           then
                              declare
                                 DC : constant Expr_Access :=
                                   new Expr_Node (Kind => E_Dyn_Cast);
                              begin
                                 DC.DC_Inner := E.C_Args.Element (I);
                                 DC.DC_Conc  := Arg_Ty.Target.Name;
                                 DC.DC_Trait := Exp.Target.Trait_Name;
                                 DC.Sem_Ty   := Exp;
                                 E.C_Args.Replace_Element (I, DC);
                              end;
                           elsif Exp /= null and then Is_Slice_Ref (Exp)
                             and then Is_Ref (Arg_Ty)
                             and then Arg_Ty.Target /= null
                             and then Arg_Ty.Target.Kind = T_Array
                             and then Arg_Ty.Target.Len > 0
                             and then Same_Type (Exp.Target.Elem,
                                                 Arg_Ty.Target.Elem)
                           then
                              --  §4.6 `&[T; N] → &[T]` coercion.
                              declare
                                 SC : constant Expr_Access :=
                                   new Expr_Node (Kind => E_Slice_Cast);
                              begin
                                 SC.SC_Inner := E.C_Args.Element (I);
                                 SC.SC_Len   := Arg_Ty.Target.Len;
                                 SC.Sem_Ty   := Exp;
                                 E.C_Args.Replace_Element (I, SC);
                              end;
                           elsif Exp /= null
                             and then not Assignable (Exp, Arg_Ty)
                           then
                              Error ("argument" & Integer'Image
                                       (I - E.C_Args.First_Index + 1)
                                     & " to '" & SU.To_String (Name)
                                     & "': expected '" & Image (Exp)
                                     & "' but got '" & Image (Arg_Ty)
                                     & "'");
                           end if;
                        end;
                        --  §8.8.2: passing a `destruct`-typed binding as
                        --  an argument transfers it. NOTE (§2.2.4/§8.11
                        --  variadic binding materialization is not
                        --  implemented by this bootstrap — the variadic
                        --  clause is parsed but the callee never receives
                        --  or destroys the extras, see Kurt.Parser.
                        --  Fn_Header.Variadic_Name): do NOT move a
                        --  variadic-extra argument (Pidx beyond the fixed
                        --  parameter list). Left un-moved, it stays owned
                        --  by the caller and is destroyed by the caller's
                        --  own scope-exit drop, same as if it had not been
                        --  passed at all — avoiding an unconditional leak
                        --  (the value would otherwise vanish into an
                        --  ignored register/stack argument with no
                        --  destructor ever invoked).
                        if Pidx <= S.Params.Last_Index then
                           Maybe_Move (E.C_Args.Element (I));
                        end if;
                     end;
                  end loop;
                  --  §7.11: a call to a `-> never` subroutine is a
                  --  diverging expression; its type is `never`.
                  if S.Is_Never then
                     E.Sem_Ty := Mk_Named ("never");
                  else
                     E.Sem_Ty := S.Ret;
                  end if;
               else
                  --  §4.10: not a named subroutine — try an indirect call
                  --  through a subroutine-pointer-typed callee value.
                  declare
                     CT : constant Type_Access := Infer (Callee, null);
                     --  §9.9 a capturing-closure value (its type is the
                     --  anonymous env struct) is invoked through its lifted
                     --  subroutine, with the env address as hidden `self`.
                     Clo_Lift : SU.Unbounded_String;
                  begin
                     if CT /= null and then CT.Kind = T_Named then
                        for SI in U.Structs.First_Index ..
                                  U.Structs.Last_Index
                        loop
                           if SU.To_String (U.Structs.Element (SI).Name)
                             = SU.To_String (CT.Name)
                           then
                              Clo_Lift := U.Structs.Element (SI).Clo_Lift;
                           end if;
                        end loop;
                     end if;
                     if SU.Length (Clo_Lift) > 0 then
                        --  Closure call: check args against the lifted
                        --  subroutine's parameters after `self`.
                        E.C_Clo_Lift := Clo_Lift;
                        declare
                           LS : Sig;
                           Has : constant Boolean :=
                             Find_Sig (SU.To_String (Clo_Lift), LS);
                        begin
                           for I in E.C_Args.First_Index ..
                                    E.C_Args.Last_Index
                           loop
                              declare
                                 --  +1: skip the hidden `self` parameter.
                                 Pidx : constant Natural :=
                                   LS.Params.First_Index + 1
                                     + (I - E.C_Args.First_Index);
                                 Exp  : Type_Access := null;
                              begin
                                 if Has and then Pidx <= LS.Params.Last_Index
                                 then
                                    Exp := LS.Params.Element (Pidx).Ty;
                                 end if;
                                 declare
                                    Arg_Ty : constant Type_Access :=
                                      Infer (E.C_Args.Element (I), Exp);
                                 begin
                                    --  §8.9: `f(*r)` copies out through
                                    --  the dereference.
                                    Check_No_Destruct_Load
                                      (E.C_Args.Element (I));
                                    if Exp /= null
                                      and then not Assignable (Exp, Arg_Ty)
                                    then
                                       Error ("argument" & Integer'Image
                                                (I - E.C_Args.First_Index + 1)
                                              & " to closure: expected '"
                                              & Image (Exp) & "' but got '"
                                              & Image (Arg_Ty) & "'");
                                    end if;
                                 end;
                              end;
                           end loop;
                           E.Sem_Ty := (if Has then LS.Ret else null);
                        end;
                        --  §9.9.3: an `xfer` closure that owns `with
                        --  destruct` captures may be invoked at most once —
                        --  a second invocation would operate on already-
                        --  consumed capture storage. Its env struct is the
                        --  only closure kind that satisfies `destruct` (a
                        --  non-`xfer` closure cannot capture such bindings),
                        --  so treat invoking a bare in-scope closure binding
                        --  as transferring it; a second call to the same
                        --  name then fails the §8.8.2 use-after-transfer
                        --  check when its callee path is re-inferred.
                        if Callee.Kind = E_Path
                          and then Natural (Callee.Segments.Length) = 1
                          and then Satisfies_Destruct (CT)
                        then
                           Mark_Moved
                             (SU.To_String (Callee.Segments.Last_Element));
                        end if;
                     elsif CT /= null and then CT.Kind = T_Fn then
                        E.C_Indirect := True;
                        for I in E.C_Args.First_Index ..
                                 E.C_Args.Last_Index
                        loop
                           declare
                              Pidx : constant Natural :=
                                CT.Fn_Params.First_Index
                                  + (I - E.C_Args.First_Index);
                              Exp  : Type_Access := null;
                           begin
                              if Pidx <= CT.Fn_Params.Last_Index then
                                 Exp := CT.Fn_Params.Element (Pidx);
                              end if;
                              declare
                                 Arg_Ty : constant Type_Access :=
                                   Infer (E.C_Args.Element (I), Exp);
                              begin
                                 --  §8.9: `f(*r)` copies out through the
                                 --  dereference.
                                 Check_No_Destruct_Load
                                   (E.C_Args.Element (I));
                                 if Exp /= null
                                   and then not Assignable (Exp, Arg_Ty)
                                 then
                                    Error ("argument" & Integer'Image
                                             (I - E.C_Args.First_Index + 1)
                                           & " to subroutine pointer: "
                                           & "expected '" & Image (Exp)
                                           & "' but got '" & Image (Arg_Ty)
                                           & "'");
                                 end if;
                              end;
                           end;
                        end loop;
                        if CT.Fn_Never then
                           E.Sem_Ty := Mk_Named ("never");
                        else
                           E.Sem_Ty := CT.Fn_Ret;
                        end if;
                     else
                        Error ("call to unknown subroutine '"
                               & SU.To_String (Name) & "'");
                        for I in E.C_Args.First_Index ..
                                 E.C_Args.Last_Index
                        loop
                           declare
                              Ignore : constant Type_Access :=
                                Infer (E.C_Args.Element (I), null);
                              pragma Unreferenced (Ignore);
                           begin
                              null;
                           end;
                        end loop;
                        E.Sem_Ty := null;
                     end if;
                  end;
               end if;
               return E.Sem_Ty;
            end;

   end Infer_Call;
