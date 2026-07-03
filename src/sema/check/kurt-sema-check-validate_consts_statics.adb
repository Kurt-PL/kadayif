separate (Kurt.Sema.Check)
   procedure Validate_Consts_Statics is
         --  Conservative xlatime-foldability (§6.10.2): literals, layout
         --  intrinsics, other consts, and pure operators over them.
         function Is_Xlatime_Foldable (E : Expr_Access) return Boolean is
         begin
            if E = null then
               return False;
            end if;
            case E.Kind is
               when E_Int_Lit | E_Float_Lit | E_Bool_Lit
                  | E_Type_Intrinsic =>
                  return True;
               when E_Unary =>
                  return Is_Xlatime_Foldable (E.U_Operand);
               when E_Binary =>
                  return Is_Xlatime_Foldable (E.B_Lhs)
                    and then Is_Xlatime_Foldable (E.B_Rhs);
               when E_Cast =>
                  return Is_Xlatime_Foldable (E.Cast_Inner);
               when E_Path =>
                  if Natural (E.Segments.Length) = 1 then
                     for I in U.Consts.First_Index ..
                              U.Consts.Last_Index
                     loop
                        if SU."=" (U.Consts.Element (I).Name,
                                   E.Segments.Last_Element)
                        then
                           return True;
                        end if;
                     end loop;
                  end if;
                  return False;
               when others =>
                  return False;
            end case;
         end Is_Xlatime_Foldable;

         --  A static initializer must fold to one scalar data word: a
         --  literal or a negated literal.
         function Is_Static_Init (E : Expr_Access) return Boolean is
           (E /= null
            and then (E.Kind in E_Int_Lit | E_Float_Lit | E_Bool_Lit
                      or else (E.Kind = E_Unary
                               and then E.U_Operand /= null
                               and then E.U_Operand.Kind in
                                 E_Int_Lit | E_Float_Lit)));
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
               D  : constant Kurt.Parser.Static_Decl :=
                 U.Statics.Element (I);
               IT : constant Type_Access := Infer (D.Init, D.Ty);
            begin
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
               elsif not Is_Static_Init (D.Init) then
                  Error ("static '" & SU.To_String (D.Name)
                         & "': initializer shall be evaluable at "
                         & "translation time (spec 5.4, bootstrap "
                         & "subset: a literal)");
               end if;
            end;
         end loop;
   end Validate_Consts_Statics;
