separate (Kurt.Mono.Monomorphize)
   function Ensure_Fn_Instance
     (Orig : String; Type_Args : Type_Vectors.Vector) return String
   is
      Key : constant Type_Access := new AST_Type (Kind => T_Named);
      TD  : Fn_Decl;
   begin
      Key.Name := SU.To_Unbounded_String (Orig);
      Key.Args := Type_Args;
      declare
         Mangled : constant String := Mangle (Key);
      begin
         if Already_Generated (Mangled) then
            return Mangled;
         end if;
         if not Find_Gen_Fn (Orig, TD) then
            raise Mono_Error with
              "instantiation of unknown generic subroutine '"
              & Orig & "'";
         end if;
         if Natural (TD.Header.Generic_Params.Length)
              /= Natural (Type_Args.Length)
         then
            raise Mono_Error with
              "wrong number of type arguments for '" & Orig & "'";
         end if;
         --  Mark first: a recursive generic fn instantiates itself.
         Generated.Append (SU.To_Unbounded_String (Mangled));

         declare
            PNames : Path_Segments.Vector;
            New_Fn : Fn_Decl;
         begin
            for I in TD.Header.Generic_Params.First_Index ..
                     TD.Header.Generic_Params.Last_Index
            loop
               PNames.Append (TD.Header.Generic_Params.Element (I).Name);
            end loop;

            New_Fn.Header := TD.Header;
            New_Fn.Header.Name := SU.To_Unbounded_String (Mangled);
            New_Fn.Header.Generic_Params.Clear;
            New_Fn.Header.Params.Clear;
            for I in TD.Header.Params.First_Index ..
                     TD.Header.Params.Last_Index
            loop
               New_Fn.Header.Params.Append
                 ((Name => TD.Header.Params.Element (I).Name,
                   Ty   => Subst (TD.Header.Params.Element (I).Ty,
                                  PNames, Type_Args),
                   Is_Mut => TD.Header.Params.Element (I).Is_Mut));
            end loop;
            New_Fn.Header.Return_Type :=
              Subst (TD.Header.Return_Type, PNames, Type_Args);
            New_Fn.Body_Stmts :=
              Copy_Block (TD.Body_Stmts, PNames, Type_Args);

            --  Re-visit: instantiate generic types / nested generic
            --  invocations now appearing with concrete arguments.
            for I in New_Fn.Header.Params.First_Index ..
                     New_Fn.Header.Params.Last_Index
            loop
               Visit_Type (New_Fn.Header.Params.Element (I).Ty);
            end loop;
            Visit_Type (New_Fn.Header.Return_Type);
            Visit_Block (New_Fn.Body_Stmts);

            U.Fns.Append (New_Fn);
         end;
         return Mangled;
      end;
   end Ensure_Fn_Instance;
