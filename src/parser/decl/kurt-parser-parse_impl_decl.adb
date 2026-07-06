separate (Kurt.Parser)
   procedure Parse_Impl_Decl
     (C           : in out Cursor;
      Fns         : in out Fn_Vectors.Vector;
      Trait_Impls : in out Trait_Impl_Vectors.Vector;
      Gen_Methods : in out Gen_Method_Vectors.Vector;
      Traits      : Trait_Vectors.Vector)
   is
      Ty_Name     : SU.Unbounded_String;
      Impl_Params : Generic_Param_Vectors.Vector;  --  §9.1 `impl(...)` list
      Is_Generic  : Boolean := False;
      TI : Trait_Impl;        --  populated only for `impl Type as Trait`

      --  Replace the `selftype` placeholder with the impl type, in place; also
      --  resolve `selftype::Item` (§9.3.1) to the impl's concrete associated
      --  type. Associated-type defs must precede methods that use them.
      procedure Subst_Self (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               declare
                  NM : constant String := SU.To_String (T.Name);
               begin
                  if NM = "selftype" then
                     T.Name := Ty_Name;
                  elsif NM'Length > 10
                    and then NM (NM'First .. NM'First + 9) = "selftype::"
                  then
                     declare
                        Item : constant String :=
                          NM (NM'First + 10 .. NM'Last);
                        Res  : Type_Access := null;
                     begin
                        for I in TI.Assoc_Types.First_Index ..
                                 TI.Assoc_Types.Last_Index
                        loop
                           if SU.To_String (TI.Assoc_Types.Element (I).Name)
                                = Item
                           then
                              Res := TI.Assoc_Types.Element (I).Ty;
                           end if;
                        end loop;
                        --  §9.3.1 the impl omitted `type Item = ...` — fall
                        --  back to the trait's declared default, if any.
                        if Res = null then
                           for T in Traits.First_Index .. Traits.Last_Index
                           loop
                              if SU.To_String (Traits.Element (T).Name)
                                   = SU.To_String (TI.Trait_Name)
                              then
                                 declare
                                    TD : Trait_Decl renames Traits.Element (T);
                                 begin
                                    for K in TD.Assoc_Types.First_Index ..
                                             TD.Assoc_Types.Last_Index
                                    loop
                                       if SU.To_String
                                            (TD.Assoc_Types.Element (K).Name)
                                            = Item
                                         and then TD.Assoc_Types.Element (K).Ty
                                                    /= null
                                       then
                                          Res :=
                                            TD.Assoc_Types.Element (K).Ty;
                                       end if;
                                    end loop;
                                 end;
                              end if;
                           end loop;
                        end if;
                        if Res /= null then
                           T.all := Res.all;   --  splice the concrete type in
                        end if;
                     end;
                  end if;
               end;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  Subst_Self (T.Args.Element (I));
               end loop;
            when T_Ref =>
               Subst_Self (T.Target);
            when T_Array =>
               Subst_Self (T.Elem);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  Subst_Self (T.Elems.Element (I));
               end loop;
            when T_Dyn =>
               null;   --  `dyn Trait` names a trait, never `selftype`
            when T_Fn =>
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  Subst_Self (T.Fn_Params.Element (I));
               end loop;
               Subst_Self (T.Fn_Ret);
         end case;
      end Subst_Self;
   begin
      Expect (C, Kw_Impl, "'impl'");
      --  §9.1 / §9.4: optional `impl(P [: bound]...)` generic parameter list,
      --  immediately after `impl` and before the target type.
      if C.Cur.Kind = Punct_LParen then
         Advance (C);
         loop
            declare
               P : Generic_Param;
            begin
               P.Name := Take_Ident (C, "impl generic parameter");
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  loop
                     if C.Cur.Kind = Op_Bang then
                        Advance (C);
                        if SU.To_String
                             (Take_Ident (C, "bound name")) /= "destruct"
                        then
                           raise Syntax_Error with
                             "only `destruct` has a negative bound form "
                             & "(`!destruct`, spec 9.8.5) at line"
                             & Positive'Image (C.Cur.Line);
                        end if;
                        P.Bounds.Append
                          (SU.To_Unbounded_String ("!destruct"));
                        P.Bound_Args.Append (Type_Vectors.Empty_Vector);
                     else
                        P.Bounds.Append (Take_Ident (C, "bound name"));
                        declare
                           BA : Type_Vectors.Vector;
                        begin
                           Parse_Opt_Type_Args (C, BA);
                           P.Bound_Args.Append (BA);
                        end;
                     end if;
                     exit when C.Cur.Kind /= Op_Plus;
                     Advance (C);
                  end loop;
               end if;
               Impl_Params.Append (P);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;  --  trailing comma
         end loop;
         Expect (C, Punct_RParen, "')' to close impl generic parameters");
         Is_Generic := True;
      end if;
      Ty_Name := Take_Ident (C, "impl type name");
      --  §5.8/§9.4.2: unlike an ordinary type reference, the impl target
      --  is read here as a raw identifier rather than through Parse_Type,
      --  so it never receives Parse_Type's alias substitution -- `impl
      --  Byte as Display` would otherwise keep Ty_Name = "Byte" even
      --  though `type Byte = ui1;` makes it the very same `impl ui1 as
      --  Display`. Resolve it against the alias table the same way
      --  Parse_Type does, so the duplicate-impl check (and everything
      --  else keyed on Ty_Name) sees the underlying concrete name. Only
      --  a non-generic alias whose target is itself a plain name applies
      --  here -- an impl target is always a bare type name, never a
      --  tuple/ref/array, so a generic alias (needing `.<Args>`, which
      --  the impl-target position does not accept before the trailing
      --  generic clause below) or a non-named target cannot match.
      for I in C.Aliases.First_Index .. C.Aliases.Last_Index loop
         if C.Aliases.Element (I).Params.Is_Empty
           and then SU."=" (C.Aliases.Element (I).Name, Ty_Name)
           and then C.Aliases.Element (I).Target /= null
           and then C.Aliases.Element (I).Target.Kind = T_Named
         then
            Ty_Name := C.Aliases.Element (I).Target.Name;
         end if;
      end loop;
      --  §9.1: an identifier declared in the `impl(...)` parameter list
      --  shall not share its name with a type declaration visible in the
      --  enclosing scope — in particular not with the type being
      --  implemented (`impl(T) T { ... }`).
      for P of Impl_Params loop
         if SU.To_String (P.Name) = SU.To_String (Ty_Name) then
            raise Syntax_Error with
              "impl generic parameter '" & SU.To_String (P.Name)
              & "' shares the name of the type being implemented "
              & "(spec 9.1) at line" & Positive'Image (C.Cur.Line);
         end if;
      end loop;
      TI.Ty_Name := Ty_Name;
      --  The target's own generic clause `Owner.<P...>` binds the impl
      --  parameters to the owner; the names are recorded in Impl_Params,
      --  so the clause itself is consumed and discarded here.
      declare
         Dummy : Generic_Param_Vectors.Vector;
      begin
         Parse_Opt_Generic_Params_Bounded (C, Dummy);
      end;
      --  §9.4: `impl Type as Trait`. (`impl Type` is an inherent block.)
      if C.Cur.Kind = Kw_As then
         Advance (C);
         TI.Trait_Name := Take_Ident (C, "trait name");
         --  §9.4 generic-trait target `impl X as Foo.<si4>`.
         Parse_Opt_Type_Args (C, TI.Trait_Args);
         --  A trait may carry its own generic clause `as Trait.<...>`.
         declare
            Dummy : Generic_Param_Vectors.Vector;
         begin
            Parse_Opt_Generic_Params_Bounded (C, Dummy);
         end;
      end if;
      Expect (C, Punct_LBrace, "'{' to open impl block");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
       if C.Cur.Kind = Kw_Type then
         --  §9.3.1 associated-type definition `type Item = Concrete;`.
         Advance (C);
         declare
            ATy : Assoc_Type;
         begin
            ATy.Name := Take_Ident (C, "associated type name");
            Expect (C, Punct_Eq, "'=' in associated type definition");
            ATy.Ty := Parse_Type (C);
            Expect (C, Punct_Semi, "';' after associated type definition");
            --  Resolve `selftype::Item` style names in the concrete type and
            --  record it for the impl's method specialisation.
            Subst_Self (ATy.Ty);
            TI.Assoc_Types.Append (ATy);
         end;
       elsif C.Cur.Kind = Kw_Const then
         --  §9.3.2 associated-const definition `const NAME: type = expr;`.
         Advance (C);
         declare
            AC : Assoc_Const;
         begin
            AC.Name := Take_Ident (C, "associated const name");
            Expect (C, Punct_Colon, "':' in associated const");
            AC.Ty := Parse_Type (C);
            Expect (C, Punct_Eq, "'=' in associated const definition");
            --  §6.10.2/§9.3.2: an associated const's value is a
            --  translation-time binding exactly like a top-level `const`.
            C.Xlatime_Depth := C.Xlatime_Depth + 1;
            AC.Val := Parse_Expr (C);
            C.Xlatime_Depth := C.Xlatime_Depth - 1;
            AC.Has_Val := True;
            Expect (C, Punct_Semi, "';' after associated const");
            TI.Consts.Append (AC);
         end;
       else
         declare
            Fn : Fn_Decl := Parse_Fn_Decl (C);
            MN : constant SU.Unbounded_String := Fn.Header.Name;
         begin
            if Is_Generic then
               --  §9.1/§9.4 generic impl: keep the method as a template.
               --  `selftype` stays a placeholder and the impl parameters are
               --  free; Kurt.Mono specialises it per owner instance. The
               --  bare method name is preserved (mangled to
               --  `Owner$args$method` at instantiation time).
               Gen_Methods.Append
                 ((Owner      => Ty_Name,
                   Trait_Name => TI.Trait_Name,
                   Gen_Params => Impl_Params,
                   Method     => Fn));
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            else
               for I in Fn.Header.Params.First_Index ..
                        Fn.Header.Params.Last_Index
               loop
                  Subst_Self (Fn.Header.Params.Element (I).Ty);
               end loop;
               Subst_Self (Fn.Header.Return_Type);
               --  §9.2.1: the method is namespaced under its type. An
               --  inherent method lowers to `Type$method`; a trait-impl method
               --  to `Type$Trait$method`, so two traits providing the same
               --  method name on one type get distinct symbols and are
               --  disambiguated by `(e as Trait).m()`.
               if SU.Length (TI.Trait_Name) > 0 then
                  Fn.Header.Name := SU.To_Unbounded_String
                    (SU.To_String (Ty_Name) & "$"
                     & SU.To_String (TI.Trait_Name) & "$"
                     & SU.To_String (MN));
               else
                  Fn.Header.Name := SU.To_Unbounded_String
                    (SU.To_String (Ty_Name) & "$" & SU.To_String (MN));
               end if;
               Fns.Append (Fn);
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            end if;
         end;
       end if;
      end loop;
      Expect (C, Punct_RBrace, "'}' to close impl block");
      --  A concrete `impl Type as Trait` registers a dispatch-table
      --  candidate; a generic trait impl provides static methods only
      --  (per-instance dispatch tables are out of scope for the
      --  bootstrap), so it is not registered here.
      --  A concrete `impl Type as Trait` registers a dispatch-table
      --  candidate; an INHERENT `impl Type` (empty Trait_Name) is registered
      --  too so its associated constants are discoverable — consumers that
      --  emit dispatch tables / check trait relationships guard on a
      --  non-empty Trait_Name.
      if not Is_Generic then
         Trait_Impls.Append (TI);
      end if;
   end Parse_Impl_Decl;
