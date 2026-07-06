separate (Kurt.Sema.Check)
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
         when E_Struct_Lit =>
            --  Aggregate construction is itself a pure operation; the
            --  whole literal is xlatime-foldable exactly when every
            --  field value is (spec 6.10: "the prerequisite excludes
            --  only expressions whose input values are not determined
            --  during translation").
            for K in E.SL_Fields.First_Index .. E.SL_Fields.Last_Index loop
               if not Is_Xlatime_Foldable (E.SL_Fields.Element (K).Val) then
                  return False;
               end if;
            end loop;
            return True;
         when E_Variant_New =>
            for K in E.VN_Fields.First_Index .. E.VN_Fields.Last_Index loop
               if not Is_Xlatime_Foldable (E.VN_Fields.Element (K).Val) then
                  return False;
               end if;
            end loop;
            return True;
         when E_Array_Lit =>
            for K in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index loop
               if not Is_Xlatime_Foldable (E.AL_Elems.Element (K)) then
                  return False;
               end if;
            end loop;
            return True;
         when E_Path =>
            if Natural (E.Segments.Length) = 1 then
               for I in U.Consts.First_Index .. U.Consts.Last_Index loop
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
