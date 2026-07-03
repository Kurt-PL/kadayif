separate (Kurt.Sema.Check)
   function Cap_By_Ref (T : Type_Access) return Boolean is
   begin
      if T = null then
         return False;
      end if;
      case T.Kind is
         when T_Tuple | T_Array =>
            return True;
         when T_Named =>
            declare
               N : constant String := SU.To_String (T.Name);
            begin
               return Kurt.Layout.Is_Struct (N)
                 or else (Kurt.Layout.Is_Enum (N)
                          and then Kurt.Layout.Enum_Has_Payload (N));
            end;
         when others =>
            return False;
      end case;
   end Cap_By_Ref;
