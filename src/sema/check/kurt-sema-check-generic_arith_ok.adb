separate (Kurt.Sema.Check)
   function Generic_Arith_OK (T : Type_Access) return Boolean is
   begin
      if T = null or else T.Kind /= T_Named then
         return False;
      end if;
      for I in Cur_Generics.First_Index .. Cur_Generics.Last_Index loop
         if SU.To_String (Cur_Generics.Element (I).Name)
              = SU.To_String (T.Name)
         then
            declare
               B : constant Path_Segments.Vector :=
                 Cur_Generics.Element (I).Bounds;
            begin
               for J in B.First_Index .. B.Last_Index loop
                  declare
                     N : constant String := SU.To_String (B.Element (J));
                  begin
                     if N = "numeric" or else N = "integer"
                       or else N = "primitive"
                     then
                        return True;
                     end if;
                  end;
               end loop;
               return False;
            end;
         end if;
      end loop;
      return False;
   end Generic_Arith_OK;
