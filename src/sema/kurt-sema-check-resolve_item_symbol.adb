separate (Kurt.Sema.Check)
   procedure Resolve_Item_Symbol
     (Ty_Name, Item, Want_Trait : String;
      Symbol     : out SU.Unbounded_String;
      Found      : out Boolean;
      Ambiguous  : out Boolean)
   is
      Dummy : Sig;
   begin
      Symbol := SU.Null_Unbounded_String;
      Found := False;
      Ambiguous := False;
      if Want_Trait /= "" then
         Symbol := SU.To_Unbounded_String
           (Ty_Name & "$" & Want_Trait & "$" & Item);
         Found := Find_Sig (SU.To_String (Symbol), Dummy);
         return;
      end if;
      if Find_Sig (Ty_Name & "$" & Item, Dummy) then
         Symbol := SU.To_Unbounded_String (Ty_Name & "$" & Item);
         Found := True;
         return;
      end if;
      declare
         Count : Natural := 0;
      begin
         for I in U.Trait_Impls.First_Index ..
                  U.Trait_Impls.Last_Index loop
            if SU.To_String (U.Trait_Impls.Element (I).Ty_Name) = Ty_Name
            then
               declare
                  Cand : constant String := Ty_Name & "$"
                    & SU.To_String (U.Trait_Impls.Element (I).Trait_Name)
                    & "$" & Item;
               begin
                  if Find_Sig (Cand, Dummy) then
                     Count := Count + 1;
                     Symbol := SU.To_Unbounded_String (Cand);
                  end if;
               end;
            end if;
         end loop;
         if Count = 1 then
            Found := True;
         elsif Count >= 2 then
            Ambiguous := True;
            Symbol := SU.Null_Unbounded_String;
         end if;
      end;
   end Resolve_Item_Symbol;
