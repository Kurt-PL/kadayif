separate (Kurt.Codegen)
   function Method_Field_Index (Tr_Name, M_Name : String) return Integer is
   begin
      for I in Unit_Traits.First_Index .. Unit_Traits.Last_Index loop
         if SU.To_String (Unit_Traits.Element (I).Name) = Tr_Name then
            declare
               Tr : Trait_Decl renames Unit_Traits.Element (I);
               S  : constant Natural := Natural (Tr.Supertraits.Length);
            begin
               for J in Tr.Methods.First_Index .. Tr.Methods.Last_Index loop
                  if SU.To_String (Tr.Methods.Element (J).Sig.Name)
                       = M_Name
                  then
                     return 3 + S + (J - Tr.Methods.First_Index);
                  end if;
               end loop;
            end;
         end if;
      end loop;
      return -1;
   end Method_Field_Index;
