separate (Kurt.Sema.Check.Infer)
   function Infer_Path return Type_Access is
   begin
            if Natural (E.Segments.Length) = 1 then
               declare
                  Name : constant String :=
                    SU.To_String (E.Segments.Last_Element);
                  T    : Type_Access := Lookup_Scope (Name);
               begin
                  --  §8.8.2: a binding shall not be used after it has been
                  --  transferred (moved).
                  if Is_Moved (Name) then
                     Error ("use of '" & Name & "' after it was "
                            & "transferred (moved) (spec 8.8.2)");
                  end if;
                  if T = null then
                     --  §5.3: a const name is replaced by its
                     --  translation-time value at each use site.
                     for I in U.Consts.First_Index ..
                              U.Consts.Last_Index
                     loop
                        if SU.To_String (U.Consts.Element (I).Name)
                          = Name
                        then
                           E.P_Assoc_Val := U.Consts.Element (I).Init;
                           E.Sem_Ty := U.Consts.Element (I).Ty;
                           return E.Sem_Ty;
                        end if;
                     end loop;
                     --  §5.4: a static binding (global object).
                     for I in U.Statics.First_Index ..
                              U.Statics.Last_Index
                     loop
                        if SU.To_String (U.Statics.Element (I).Name)
                          = Name
                        then
                           --  §2.6: `static mut` access (read as well as
                           --  store) is an airside-only operation.
                           if U.Statics.Element (I).Is_Mut
                             and then In_Airside = 0
                           then
                              Error ("access to `static mut` '" & Name
                                     & "' is permitted only in an "
                                     & "`airside` region (spec 2.6)");
                           end if;
                           T := U.Statics.Element (I).Ty;
                           E.Sem_Ty := T;
                           return T;
                        end if;
                     end loop;
                     --  §4.10: a bare subroutine name used as a value is
                     --  a subroutine pointer; its type is built from the
                     --  signature. (As a call callee the name is resolved
                     --  in E_Call, not here.)
                     declare
                        FS : Sig;
                     begin
                        if Find_Sig (Name, FS) then
                           declare
                              FP : constant Type_Access :=
                                new AST_Type (Kind => T_Fn);
                           begin
                              for I in FS.Params.First_Index ..
                                       FS.Params.Last_Index
                              loop
                                 FP.Fn_Params.Append
                                   (FS.Params.Element (I).Ty);
                              end loop;
                              FP.Fn_Ret      := FS.Ret;
                              FP.Fn_Variadic := FS.Is_Variadic;
                              FP.Fn_Never    := FS.Is_Never;
                              E.P_Is_Fn_Ptr  := True;
                              E.Sem_Ty       := FP;
                              return FP;
                           end;
                        end if;
                     end;
                     Error ("unknown identifier '" & Name & "'");
                  end if;
                  E.Sem_Ty := T;
                  return T;
               end;
            elsif Natural (E.Segments.Length) = 2 then
               --  `Enum::Variant` evaluates to a value of the enum.
               declare
                  EN : constant String :=
                    SU.To_String (E.Segments.First_Element);
                  VN : constant String :=
                    SU.To_String (E.Segments.Last_Element);
               begin
                  if Kurt.Layout.Is_Enum (EN)
                    and then Kurt.Layout.Has_Variant (EN, VN)
                  then
                     E.Sem_Ty := Mk_Named (EN);
                     return E.Sem_Ty;
                  --  Generic enum: the concrete instance comes from the
                  --  expected type (post-monomorphisation).
                  elsif Expected /= null and then Expected.Kind = T_Named
                    and then Kurt.Layout.Is_Enum
                               (SU.To_String (Expected.Name))
                    and then Kurt.Layout.Has_Variant
                               (SU.To_String (Expected.Name), VN)
                  then
                     E.Sem_Ty := Expected;
                     return E.Sem_Ty;
                  end if;
                  --  §9.3.2 associated-const access `Type::NAME`.
                  --  Concrete type: inline the impl's value expression.
                  declare
                     CV : constant Expr_Access :=
                       Find_Impl_Const (EN, VN);
                  begin
                     if CV /= null then
                        E.P_Assoc_Val := CV;
                        E.Sem_Ty := Infer (CV, Expected);
                        return E.Sem_Ty;
                     end if;
                  end;
                  --  Generic parameter: `T::NAME` in a template. The
                  --  value is resolved per instance; here only the type
                  --  (selftype → T) is needed for checking.
                  declare
                     CT  : Type_Access;
                     OKc : Boolean;
                  begin
                     Find_Bound_Const (EN, VN, CT, OKc);
                     if OKc then
                        E.Sem_Ty := Subst_Self_T
                          (CT, Mk_Named (EN));
                        return E.Sem_Ty;
                     end if;
                  end;
               end;
               --  Otherwise a namespaced call callee (handled in E_Call).
               E.Sem_Ty := null;
               return null;
            else
               E.Sem_Ty := null;
               return null;
            end if;

   end Infer_Path;
