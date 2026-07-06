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
            --  §4.7: resolve a non-literal array length (`[T; N]` where N
            --  is a `const` or arithmetic over consts/literals) here --
            --  the single choke point ahead of every Kurt.Layout.Size_Of
            --  query in the pipeline (Visit_Type runs as part of
            --  Kurt.Mono.Monomorphize, which precedes both
            --  Kurt.Layout.Register and Kurt.Sema.Check; see
            --  main-translate.adb). See the note on T_Array.Len_Expr in
            --  kurt-parser.ads.
            if T.Len_Expr /= null then
               declare
                  N : Long_Long_Integer;
               begin
                  if not Fold_Int_Expr (U, T.Len_Expr, N) then
                     raise Mono_Error with
                       "array length is not evaluable at translation "
                       & "time (spec 4.7)";
                  elsif N <= 0 then
                     raise Mono_Error with
                       "array length must be a positive integer, got"
                       & N'Image & " (spec 4.7)";
                  elsif N > Long_Long_Integer (Natural'Last) then
                     raise Mono_Error with
                       "array length exceeds the representable range "
                       & "(spec 4.7)";
                  end if;
                  T.Len := Natural (N);
                  T.Len_Expr := null;
               end;
            end if;
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
            else
               --  §5.9: "A type constructor shall not appear in a
               --  position that expects a type without being applied to
               --  arguments." Args is empty and the name is not
               --  `verdict`; if it names a generic struct/enum template
               --  (lifted into Gen_Structs/Gen_Enums above, ahead of this
               --  traversal), the type position names the *constructor*,
               --  not a concrete, sized type -- a translation failure
               --  even when the position is never exercised at an
               --  instantiation site.
               declare
                  Dummy_S : Struct_Decl;
                  Dummy_E : Enum_Decl;
                  Orig_N  : constant String := SU.To_String (T.Name);
               begin
                  if Find_Gen_Struct (Orig_N, Dummy_S)
                    or else Find_Gen_Enum (Orig_N, Dummy_E)
                  then
                     raise Mono_Error with
                       "generic type '" & Orig_N & "' used without type "
                       & "arguments in a type position (spec 5.9)";
                  end if;
               end;
            end if;
      end case;
   end Visit_Type;
