separate (Kurt.Sema.Check.Infer)
   function Infer_Closure return Type_Access is
   begin
            --  §9.9 the value type of a *non-capturing* closure is the
            --  invocable signature `fn(param types) -> return type` (it is
            --  a plain subroutine pointer). A *capturing* closure's value
            --  type is its anonymous capture struct `$clo_N$env`: each
            --  field holds a copy of a captured binding, and the value is
            --  invoked through the lifted subroutine `$clo_N(self, ...)`.
            --  The body is checked via the subroutine Kurt.Mono lifted it
            --  to; the return type is the explicit `-> U` or inferred from
            --  the body's first return (params pushed temporarily).
            declare
               RT    : Type_Access := E.Clo_Ret;
               Saved : constant Natural := Natural (Scope.Length);
               FT    : constant Type_Access :=
                 new AST_Type (Kind => T_Fn);
            begin
               --  §9.9.3 resolve each capture's type from the creating
               --  scope and finalise the anonymous capture struct (whose
               --  fields Kurt.Mono left untyped), then re-register the
               --  layout so the lifted subroutine and the closure value
               --  see the completed struct.
               if not E.Clo_Caps.Is_Empty then
                  for K in E.Clo_Caps.First_Index ..
                           E.Clo_Caps.Last_Index
                  loop
                     declare
                        CN : constant String :=
                          SU.To_String (E.Clo_Caps.Element (K).Name);
                        CT : constant Type_Access := Lookup_Scope (CN);
                        C  : Closure_Param := E.Clo_Caps.Element (K);
                     begin
                        if CT = null then
                           Error ("closure captures '" & CN & "', whose "
                                  & "type cannot be determined in the "
                                  & "enclosing scope (spec 9.9.3)");
                        end if;
                        C.Ty := CT;
                        E.Clo_Caps.Replace_Element (K, C);
                        --  §9.9.2/§9.9.3: capturing a `with destruct`
                        --  binding transfers ownership into the closure and
                        --  shall be declared `xfer`. The captured binding is
                        --  invalidated in the enclosing scope; the env type
                        --  acquires `with destruct` (it now has a
                        --  destruct-satisfying field) and its destructor
                        --  destroys the moved value at scope exit.
                        if Satisfies_Destruct (CT) then
                           if not E.Clo_Xfer then
                              Error ("closure captures the `with destruct` "
                                     & "binding '" & CN & "'; it shall be "
                                     & "declared `xfer` (spec 9.9.2)");
                           end if;
                           Mark_Moved (CN);
                        end if;
                        --  An aggregate capture (struct / tuple / array /
                        --  payload enum) lives in memory and cannot become
                        --  a register value, and a `with destruct` capture
                        --  must not be re-copied into an owned local (that
                        --  would double-destroy). So bind the body's view
                        --  of it by reference to the env field, rewriting
                        --  the prefix `let cap = self.cap;` (synthesised by
                        --  Kurt.Mono) into `let cap = &self.cap;`. Scalar
                        --  copyable captures keep their by-copy local.
                        if Cap_By_Ref (CT)
                          and then K - E.Clo_Caps.First_Index
                                     < Integer (E.Clo_Body.Length)
                        then
                           declare
                              PS : constant Stmt_Access :=
                                E.Clo_Body.Element
                                  (E.Clo_Body.First_Index
                                     + (K - E.Clo_Caps.First_Index));
                              Ref : constant Expr_Access :=
                                new Expr_Node (Kind => E_Ref);
                              RT2 : constant Type_Access :=
                                new AST_Type (Kind => T_Ref);
                           begin
                              if PS.Kind = S_Let
                                and then PS.L_Init /= null
                                and then PS.L_Init.Kind = E_Field
                              then
                                 Ref.Rf_Sigil := R_Shared;
                                 Ref.Rf_Place := PS.L_Init;
                                 PS.L_Init := Ref;
                                 RT2.Sigil  := R_Shared;
                                 RT2.Target := CT;
                                 PS.L_Ty := RT2;
                              end if;
                           end;
                        end if;
                     end;
                  end loop;
                  for SI in U.Structs.First_Index ..
                            U.Structs.Last_Index
                  loop
                     if SU.To_String (U.Structs.Element (SI).Name)
                       = SU.To_String (E.Clo_Env_Name)
                     then
                        declare
                           SD : Struct_Decl := U.Structs.Element (SI);
                        begin
                           for K in SD.Fields.First_Index ..
                                    SD.Fields.Last_Index
                           loop
                              declare
                                 FF : Struct_Field := SD.Fields.Element (K);
                              begin
                                 FF.Ty := E.Clo_Caps.Element (K).Ty;
                                 SD.Fields.Replace_Element (K, FF);
                              end;
                           end loop;
                           U.Structs.Replace_Element (SI, SD);
                        end;
                     end if;
                  end loop;
                  Kurt.Layout.Register (U);
               end if;

               for P of E.Clo_Params loop
                  Scope.Append ((Name => P.Name, Ty => P.Ty, others => <>));
               end loop;
               if RT = null then
                  for S of E.Clo_Body loop
                     if S.Kind = S_Return and then S.R_Val /= null then
                        RT := Infer (S.R_Val, null);
                        exit;
                     end if;
                  end loop;
               end if;
               while Natural (Scope.Length) > Saved loop
                  Scope.Delete_Last;
               end loop;
               if RT = null then
                  RT := Mk_Named ("void");
               end if;

               --  Propagate the return type (resolved here, where the
               --  captures are in scope) onto the lifted subroutine, so its
               --  own Check_Fn does not re-infer it before the
               --  capture-loading prefix `let`s have entered scope.
               for FI in U.Fns.First_Index .. U.Fns.Last_Index loop
                  if SU.To_String (U.Fns.Element (FI).Header.Name)
                    = SU.To_String (E.Clo_Fn_Name)
                    and then U.Fns.Element (FI).Header.Return_Type = null
                  then
                     declare
                        LF : Fn_Decl := U.Fns.Element (FI);
                     begin
                        LF.Header.Return_Type := RT;
                        U.Fns.Replace_Element (FI, LF);
                     end;
                  end if;
               end loop;

               if not E.Clo_Caps.Is_Empty then
                  --  Capturing: the value is the anonymous env struct.
                  E.Sem_Ty := Mk_Named (SU.To_String (E.Clo_Env_Name));
                  return E.Sem_Ty;
               end if;

               for P of E.Clo_Params loop
                  FT.Fn_Params.Append (P.Ty);
               end loop;
               FT.Fn_Ret := RT;
               E.Sem_Ty := FT;
               return FT;
            end;

   end Infer_Closure;
