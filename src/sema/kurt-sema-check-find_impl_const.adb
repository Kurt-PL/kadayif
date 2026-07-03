separate (Kurt.Sema.Check)
   function Find_Impl_Const
     (Ty_Name, Name : String) return Expr_Access
   is
   begin
      for I in U.Trait_Impls.First_Index ..
               U.Trait_Impls.Last_Index
      loop
         if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
         then
            declare
               TI : Trait_Impl renames U.Trait_Impls.Element (I);
            begin
               for J in TI.Consts.First_Index .. TI.Consts.Last_Index
               loop
                  if SU.To_String (TI.Consts.Element (J).Name) = Name
                  then
                     return TI.Consts.Element (J).Val;
                  end if;
               end loop;
               --  §9.3.2 the impl omitted the const — fall back to the
               --  trait's default value, if the trait declares one.
               for T in U.Traits.First_Index .. U.Traits.Last_Index loop
                  if SU.To_String (U.Traits.Element (T).Name)
                       = SU.To_String (TI.Trait_Name)
                  then
                     for K in U.Traits.Element (T).Consts.First_Index ..
                              U.Traits.Element (T).Consts.Last_Index loop
                        if SU.To_String
                             (U.Traits.Element (T).Consts.Element (K).Name)
                             = Name
                          and then U.Traits.Element (T).Consts.Element (K)
                                     .Has_Val
                        then
                           return U.Traits.Element (T).Consts.Element (K)
                                    .Val;
                        end if;
                     end loop;
                  end if;
               end loop;
            end;
         end if;
      end loop;
      return null;
   end Find_Impl_Const;
