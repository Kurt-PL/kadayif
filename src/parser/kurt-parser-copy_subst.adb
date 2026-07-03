separate (Kurt.Parser)
   function Copy_Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is
      R : Type_Access;
   begin
      if T = null then
         return null;
      end if;
      if T.Kind = T_Named and then T.Args.Is_Empty then
         for I in Params.First_Index .. Params.Last_Index loop
            if SU."=" (Params.Element (I), T.Name) then
               return Args.Element
                 (Args.First_Index + (I - Params.First_Index));
            end if;
         end loop;
      end if;
      R := new AST_Type'(T.all);   --  shallow copy (incl. discriminant)
      case R.Kind is
         when T_Named =>
            R.Args := Type_Vectors.Empty_Vector;
            for I in T.Args.First_Index .. T.Args.Last_Index loop
               R.Args.Append (Copy_Subst (T.Args.Element (I), Params, Args));
            end loop;
         when T_Ref =>
            R.Target := Copy_Subst (T.Target, Params, Args);
         when T_Array =>
            R.Elem := Copy_Subst (T.Elem, Params, Args);
         when T_Tuple =>
            R.Elems := Type_Vectors.Empty_Vector;
            for I in T.Elems.First_Index .. T.Elems.Last_Index loop
               R.Elems.Append (Copy_Subst (T.Elems.Element (I), Params, Args));
            end loop;
         when T_Fn =>
            R.Fn_Params := Type_Vectors.Empty_Vector;
            for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
               R.Fn_Params.Append
                 (Copy_Subst (T.Fn_Params.Element (I), Params, Args));
            end loop;
            R.Fn_Ret := Copy_Subst (T.Fn_Ret, Params, Args);
         when others =>
            null;
      end case;
      return R;
   end Copy_Subst;
