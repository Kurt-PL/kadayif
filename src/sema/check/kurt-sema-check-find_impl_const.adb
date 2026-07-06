separate (Kurt.Sema.Check)
   function Find_Impl_Const
     (Ty_Name, Name, Want_Trait : String) return Expr_Access
   is
      Result    : Expr_Access := null;
      Result_Tr : SU.Unbounded_String;
      Second_Tr : SU.Unbounded_String;
      Ambiguous : Boolean := False;
   begin
      for I in U.Trait_Impls.First_Index ..
               U.Trait_Impls.Last_Index
      loop
         if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
         then
            declare
               TI  : Trait_Impl renames U.Trait_Impls.Element (I);
               Tr  : constant String := SU.To_String (TI.Trait_Name);
               Val : Expr_Access := null;
            begin
               --  §9.2.1: a qualified access `(Ty as Trait)::Name` names
               --  one specific trait impl -- every other candidate is
               --  irrelevant to it.
               if Want_Trait = "" or else Tr = Want_Trait then
                  for J in TI.Consts.First_Index .. TI.Consts.Last_Index
                  loop
                     if SU.To_String (TI.Consts.Element (J).Name) = Name
                     then
                        Val := TI.Consts.Element (J).Val;
                        exit;
                     end if;
                  end loop;
                  if Val = null then
                     --  §9.3.2 the impl omitted the const — fall back to
                     --  the trait's default value, if the trait declares
                     --  one.
                     for T in U.Traits.First_Index .. U.Traits.Last_Index
                     loop
                        if SU.To_String (U.Traits.Element (T).Name) = Tr
                        then
                           for K in U.Traits.Element (T).Consts.First_Index
                                 .. U.Traits.Element (T).Consts.Last_Index
                           loop
                              if SU.To_String
                                   (U.Traits.Element (T).Consts.Element (K)
                                      .Name) = Name
                                and then U.Traits.Element (T).Consts
                                           .Element (K).Has_Val
                              then
                                 Val := U.Traits.Element (T).Consts
                                          .Element (K).Val;
                              end if;
                           end loop;
                        end if;
                     end loop;
                  end if;
               end if;
               if Val /= null then
                  if Want_Trait /= "" then
                     --  Qualified access always resolves directly to the
                     --  named trait impl.
                     return Val;
                  elsif Tr = "" then
                     --  An inherent impl's const always takes priority
                     --  (mirrors inherent-vs-trait method resolution) and
                     --  cannot itself be ambiguous (§9.1 forbids name
                     --  collisions between inherent impls).
                     return Val;
                  elsif Result = null then
                     Result    := Val;
                     Result_Tr := TI.Trait_Name;
                  elsif SU.To_String (Result_Tr) /= Tr then
                     Ambiguous := True;
                     Second_Tr := TI.Trait_Name;
                  end if;
               end if;
            end;
         end if;
      end loop;
      if Ambiguous then
         Error ("associated const '" & Name & "' on '" & Ty_Name
                & "' is ambiguous between trait '"
                & SU.To_String (Result_Tr) & "' and trait '"
                & SU.To_String (Second_Tr) & "'; use `(" & Ty_Name
                & " as Trait)::" & Name & "` (spec 9.2.1)");
         return null;
      end if;
      return Result;
   end Find_Impl_Const;
