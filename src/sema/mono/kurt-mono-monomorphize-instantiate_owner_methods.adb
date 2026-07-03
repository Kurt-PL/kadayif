separate (Kurt.Mono.Monomorphize)
   procedure Instantiate_Owner_Methods
     (Orig, Mangled : String; Args : Type_Vectors.Vector)
   is
   begin
      for GI in U.Gen_Methods.First_Index ..
                U.Gen_Methods.Last_Index
      loop
         declare
            GM : constant Gen_Method := U.Gen_Methods.Element (GI);
         begin
            if SU.To_String (GM.Owner) = Orig then
               declare
                  Bare     : constant String :=
                    SU.To_String (GM.Method.Header.Name);
                  New_Name : constant String := Mangled & "$" & Bare;
                  PNames   : Path_Segments.Vector;
                  New_Fn   : Fn_Decl;
               begin
                  if not Already_Generated (New_Name) then
                     if Natural (GM.Gen_Params.Length)
                          /= Natural (Args.Length)
                     then
                        raise Mono_Error with
                          "wrong number of type arguments for impl of '"
                          & Orig & "'";
                     end if;
                     Generated.Append
                       (SU.To_Unbounded_String (New_Name));
                     for I in GM.Gen_Params.First_Index ..
                              GM.Gen_Params.Last_Index
                     loop
                        PNames.Append (GM.Gen_Params.Element (I).Name);
                     end loop;

                     New_Fn.Header := GM.Method.Header;
                     New_Fn.Header.Name :=
                       SU.To_Unbounded_String (New_Name);
                     New_Fn.Header.Generic_Params.Clear;
                     New_Fn.Header.Params.Clear;
                     for K in GM.Method.Header.Params.First_Index ..
                              GM.Method.Header.Params.Last_Index
                     loop
                        New_Fn.Header.Params.Append
                          ((Name => GM.Method.Header.Params
                                      .Element (K).Name,
                            Ty   => Subst
                              (GM.Method.Header.Params.Element (K).Ty,
                               PNames, Args),
                            Is_Mut => GM.Method.Header.Params
                                        .Element (K).Is_Mut));
                     end loop;
                     New_Fn.Header.Return_Type :=
                       Subst (GM.Method.Header.Return_Type,
                              PNames, Args);
                     New_Fn.Body_Stmts :=
                       Copy_Block (GM.Method.Body_Stmts, PNames, Args);

                     --  selftype -> the concrete owner instance.
                     for K in New_Fn.Header.Params.First_Index ..
                              New_Fn.Header.Params.Last_Index
                     loop
                        Subst_Self_Name
                          (New_Fn.Header.Params.Element (K).Ty, Mangled);
                     end loop;
                     Subst_Self_Name (New_Fn.Header.Return_Type, Mangled);

                     --  Re-visit for transitive instantiation.
                     for K in New_Fn.Header.Params.First_Index ..
                              New_Fn.Header.Params.Last_Index
                     loop
                        Visit_Type (New_Fn.Header.Params.Element (K).Ty);
                     end loop;
                     Visit_Type (New_Fn.Header.Return_Type);
                     Visit_Block (New_Fn.Body_Stmts);

                     U.Fns.Append (New_Fn);
                  end if;
               end;
            end if;
         end;
      end loop;
   end Instantiate_Owner_Methods;
