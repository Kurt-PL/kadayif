separate (Kurt.Sema.Check)
   procedure Lookup_Trait_Method
     (Tr_Name, M_Name : String;
      Sig_Out         : out Fn_Header;
      Found           : out Boolean)
   is
   begin
      Found := False;
      for I in U.Traits.First_Index .. U.Traits.Last_Index loop
         if SU.To_String (U.Traits.Element (I).Name) = Tr_Name then
            declare
               Tr : Trait_Decl renames U.Traits.Element (I);
            begin
               for J in Tr.Methods.First_Index ..
                        Tr.Methods.Last_Index
               loop
                  if SU.To_String (Tr.Methods.Element (J).Sig.Name)
                       = M_Name
                  then
                     Sig_Out := Tr.Methods.Element (J).Sig;
                     Found := True;
                     return;
                  end if;
               end loop;
            end;
         end if;
      end loop;
   end Lookup_Trait_Method;
