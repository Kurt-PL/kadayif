separate (Kurt.Sema.Check)
   procedure Find_Bound_Method
     (Gen, M_Name : String;
      Sig_Out     : out Fn_Header;
      Found       : out Boolean)
   is
   begin
      Found := False;
      for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
         if SU.To_String (Cur_Generics.Element (I).Name) = Gen then
            declare
               B : Path_Segments.Vector renames
                 Cur_Generics.Element (I).Bounds;
            begin
               for J in B.First_Index .. B.Last_Index loop
                  Lookup_Trait_Method
                    (SU.To_String (B.Element (J)), M_Name,
                     Sig_Out, Found);
                  if Found then
                     return;
                  end if;
               end loop;
            end;
         end if;
      end loop;
   end Find_Bound_Method;
