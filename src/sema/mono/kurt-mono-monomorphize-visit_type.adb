separate (Kurt.Mono.Monomorphize)
   procedure Visit_Type (T : Type_Access) is
   begin
      if T = null then
         return;
      end if;
      case T.Kind is
         when T_Ref =>
            Visit_Type (T.Target);
         when T_Array =>
            Visit_Type (T.Elem);
         when T_Dyn =>
            null;
         when T_Fn =>
            for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
               Visit_Type (T.Fn_Params.Element (I));
            end loop;
            Visit_Type (T.Fn_Ret);
         when T_Tuple =>
            for I in T.Elems.First_Index .. T.Elems.Last_Index loop
               Visit_Type (T.Elems.Element (I));
            end loop;
         when T_Named =>
            for I in T.Args.First_Index .. T.Args.Last_Index loop
               Visit_Type (T.Args.Element (I));   --  innermost first
            end loop;
            --  §4.5 verdict is an intrinsic built-in (like bool): it is
            --  recognised by name + args directly by Kurt.Layout, never
            --  monomorphised into a generated enum. Leave it as
            --  T_Named "verdict" with its Args intact.
            if SU.To_String (T.Name) = "verdict" then
               null;
            elsif not T.Args.Is_Empty then
               declare
                  Orig_N     : constant String := SU.To_String (T.Name);
                  Mangled    : constant String := Mangle (T);
                  Saved_Args : constant Type_Vectors.Vector := T.Args;
               begin
                  Ensure_Instance (T, Mangled);
                  --  §9.1/§9.4: specialise the owner's generic-impl
                  --  methods for this instance (e.g. Box$si4$get).
                  Instantiate_Owner_Methods (Orig_N, Mangled, Saved_Args);
                  T.Name := SU.To_Unbounded_String (Mangled);
                  T.Args.Clear;
               end;
            end if;
      end case;
   end Visit_Type;
