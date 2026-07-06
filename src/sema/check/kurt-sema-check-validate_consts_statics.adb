separate (Kurt.Sema.Check)
   procedure Validate_Consts_Statics is
         --  Is_Xlatime_Foldable (§6.10.2) now lives as its own Check
         --  subunit (kurt-sema-check-is_xlatime_foldable.adb) so the
         --  struct-field default-value check (spec 5.5.3) can share it.

         --  A static initializer must fold to one scalar data word: a
         --  literal, a negated literal, or (§5.4/§6.10.2, extending the
         --  bootstrap subset) a small-integer arithmetic expression over
         --  literals and already-declared `const`s -- folded here via
         --  Kurt.Parser.Fold_Int_Expr and rewritten in place to a literal
         --  so Kurt.Codegen.Emit's static-initializer emitter (which only
         --  understands a bare/negated literal, spec 5.4) sees one, the
         --  same way a `const` reference is substituted via P_Assoc_Val.
         function Is_Static_Init (D : in out Kurt.Parser.Static_Decl)
           return Boolean
         is
            Folded : Long_Long_Integer;
         begin
            if D.Init = null then
               return False;
            end if;
            if D.Init.Kind in E_Int_Lit | E_Float_Lit | E_Bool_Lit
              or else (D.Init.Kind = E_Unary
                       and then D.Init.U_Operand /= null
                       and then D.Init.U_Operand.Kind in
                                  E_Int_Lit | E_Float_Lit)
            then
               return True;
            end if;
            if Is_Integer_Type (D.Ty)
              and then Fold_Int_Expr (U, D.Init, Folded)
            then
               declare
                  Lit : constant Expr_Access :=
                    new Expr_Node (Kind => E_Int_Lit);
               begin
                  Lit.Int_V  := Folded;
                  Lit.Sem_Ty := D.Init.Sem_Ty;
                  D.Init := Lit;
               end;
               return True;
            end if;
            return False;
         end Is_Static_Init;
      begin
         for I in U.Consts.First_Index .. U.Consts.Last_Index loop
            declare
               D  : constant Kurt.Parser.Const_Decl := U.Consts.Element (I);
               IT : constant Type_Access := Infer (D.Init, D.Ty);
            begin
               if not Assignable (D.Ty, IT) then
                  Error ("const '" & SU.To_String (D.Name)
                         & "': initializer type '" & Image (IT)
                         & "' does not match '" & Image (D.Ty) & "'");
               elsif not Is_Xlatime_Foldable (D.Init) then
                  Error ("const '" & SU.To_String (D.Name)
                         & "': initializer is not evaluable at "
                         & "translation time (spec 5.3, bootstrap "
                         & "subset: literals, type intrinsics, consts, "
                         & "and pure operators)");
               end if;
            end;
         end loop;

         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            declare
               D  : Kurt.Parser.Static_Decl := U.Statics.Element (I);
               IT : constant Type_Access := Infer (D.Init, D.Ty);
            begin
               --  §4.12: `static X: ? = e;` synthesises the type from the
               --  initialiser, exactly like an omitted `let` annotation.
               if D.Ty = null then
                  D.Ty := IT;
                  U.Statics.Replace_Element (I, D);
               end if;
               if not (Is_Integer_Type (D.Ty)
                       or else Is_Float_Type (D.Ty)
                       or else (D.Ty.Kind = T_Named
                                and then SU.To_String (D.Ty.Name)
                                       = "bool"))
               then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': bootstrap supports scalar statics only, "
                         & "got '" & Image (D.Ty) & "'");
               elsif not Assignable (D.Ty, IT) then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': initializer type '" & Image (IT)
                         & "' does not match '" & Image (D.Ty) & "'");
               elsif not Is_Static_Init (D) then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': initializer shall be evaluable at "
                         & "translation time (spec 5.4, bootstrap "
                         & "subset: a literal, or a small-integer "
                         & "arithmetic expression over literals and "
                         & "consts)");
               else
                  --  Is_Static_Init may have rewritten D.Init to the
                  --  folded literal (integer arithmetic case) -- write
                  --  the (possibly updated) copy back.
                  U.Statics.Replace_Element (I, D);
               end if;
            end;
         end loop;

         --  §5.3: an impl-associated const (`impl Type { const NAME:
         --  T = e; }` or the trait-impl-side value of a trait's
         --  associated const) is a translation-time binding exactly like
         --  a top-level `const` -- it shall undergo the same
         --  Assignable/Is_Xlatime_Foldable validation. Covers both
         --  inherent impls and `impl Type as Trait` (both live in
         --  U.Trait_Impls; an inherent impl just has an empty
         --  Trait_Name).
         for I in U.Trait_Impls.First_Index .. U.Trait_Impls.Last_Index loop
            declare
               TI : Trait_Impl renames U.Trait_Impls.Element (I);
            begin
               for J in TI.Consts.First_Index .. TI.Consts.Last_Index loop
                  declare
                     AC : Assoc_Const renames TI.Consts.Element (J);
                  begin
                     if AC.Val /= null then
                        declare
                           IT : constant Type_Access := Infer (AC.Val, AC.Ty);
                        begin
                           if not Assignable (AC.Ty, IT) then
                              Error ("impl '" & SU.To_String (TI.Ty_Name)
                                     & "': associated const '"
                                     & SU.To_String (AC.Name)
                                     & "': initializer type '" & Image (IT)
                                     & "' does not match '"
                                     & Image (AC.Ty) & "'");
                           elsif not Is_Xlatime_Foldable (AC.Val) then
                              Error ("impl '" & SU.To_String (TI.Ty_Name)
                                     & "': associated const '"
                                     & SU.To_String (AC.Name)
                                     & "': initializer is not evaluable "
                                     & "at translation time (spec 5.3, "
                                     & "bootstrap subset: literals, type "
                                     & "intrinsics, consts, aggregate "
                                     & "literals over those, and pure "
                                     & "operators)");
                           end if;
                        end;
                     end if;
                  end;
               end loop;
            end;
         end loop;
   end Validate_Consts_Statics;
