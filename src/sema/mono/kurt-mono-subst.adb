separate (Kurt.Mono)
   function Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is
   begin
      if T = null then
         return null;
      end if;
      case T.Kind is
         when T_Named =>
            --  A bare name matching a parameter is replaced by the arg.
            if T.Args.Is_Empty then
               for I in Params.First_Index .. Params.Last_Index loop
                  if SU.To_String (Params.Element (I))
                       = SU.To_String (T.Name)
                  then
                     return Subst
                       (Args.Element (Args.First_Index + (I - Params.First_Index)),
                        Path_Segments.Empty_Vector, Type_Vectors.Empty_Vector);
                  end if;
               end loop;
            end if;
            --  Otherwise copy, substituting inside any nested arguments.
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Named);
            begin
               R.Name := T.Name;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  R.Args.Append (Subst (T.Args.Element (I), Params, Args));
               end loop;
               return R;
            end;
         when T_Ref =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Ref);
            begin
               R.Sigil      := T.Sigil;
               R.R_Volatile := T.R_Volatile;
               R.R_Store    := T.R_Store;
               R.Target     := Subst (T.Target, Params, Args);
               return R;
            end;
         when T_Tuple =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Tuple);
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  R.Elems.Append (Subst (T.Elems.Element (I), Params, Args));
               end loop;
               return R;
            end;
         when T_Array =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Array);
            begin
               R.Elem := Subst (T.Elem, Params, Args);
               R.Len  := T.Len;
               return R;
            end;
         when T_Dyn =>
            return T;   --  trait object carries no substitutable parts
         when T_Fn =>
            declare
               R : constant Type_Access := new AST_Type (Kind => T_Fn);
            begin
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  R.Fn_Params.Append
                    (Subst (T.Fn_Params.Element (I), Params, Args));
               end loop;
               R.Fn_Ret      := Subst (T.Fn_Ret, Params, Args);
               R.Fn_Variadic := T.Fn_Variadic;
               R.Fn_Airside  := T.Fn_Airside;
               R.Fn_Never    := T.Fn_Never;
               R.Fn_Extern   := T.Fn_Extern;
               return R;
            end;
      end case;
   end Subst;
