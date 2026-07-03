separate (Kurt.Sema.Check)
   procedure Find_Bound_Const
     (Gen, Name : String; Ty_Out : out Type_Access; Found : out Boolean)
   is
   begin
      Found := False;
      Ty_Out := null;
      for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
         if SU.To_String (Cur_Generics.Element (I).Name) = Gen then
            declare
               B : Path_Segments.Vector renames
                 Cur_Generics.Element (I).Bounds;
            begin
               for J in B.First_Index .. B.Last_Index loop
                  for T in U.Traits.First_Index .. U.Traits.Last_Index
                  loop
                     if SU.To_String (U.Traits.Element (T).Name)
                          = SU.To_String (B.Element (J))
                     then
                        declare
                           Tr : Trait_Decl renames
                             U.Traits.Element (T);
                        begin
                           for K in Tr.Consts.First_Index ..
                                    Tr.Consts.Last_Index
                           loop
                              if SU.To_String
                                   (Tr.Consts.Element (K).Name) = Name
                              then
                                 Ty_Out := Tr.Consts.Element (K).Ty;
                                 Found := True;
                                 return;
                              end if;
                           end loop;
                        end;
                     end if;
                  end loop;
               end loop;
            end;
         end if;
      end loop;
   end Find_Bound_Const;
