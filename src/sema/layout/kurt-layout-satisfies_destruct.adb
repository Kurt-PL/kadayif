separate (Kurt.Layout)
   function Satisfies_Destruct (T : Type_Access) return Boolean is
   begin
      if T = null then
         return False;
      end if;
      case T.Kind is
         when T_Named =>
            declare
               N  : constant String := SU.To_String (T.Name);
               SD : Struct_Decl;
               ED : Enum_Decl;
            begin
               if Find_Struct (N, SD) then
                  if SD.Has_Destruct then
                     return True;
                  end if;
                  for F of SD.Fields loop
                     if Satisfies_Destruct (F.Ty) then
                        return True;
                     end if;
                  end loop;
                  return False;
               elsif Find_Enum (N, ED) then
                  if ED.Has_Destruct then
                     return True;
                  end if;
                  for V of ED.Variants loop
                     for F of V.Payload loop
                        if Satisfies_Destruct (F.Ty) then
                           return True;
                        end if;
                     end loop;
                  end loop;
                  return False;
               end if;
               return False;
            end;
         when T_Array =>
            return Satisfies_Destruct (T.Elem);
         when T_Tuple =>
            for E of T.Elems loop
               if Satisfies_Destruct (E) then
                  return True;
               end if;
            end loop;
            return False;
         when T_Ref =>
            --  §8.1: the `$` (exclusive) sigil is intrinsically
            --  bodyless-`destruct` regardless of referent — including
            --  the slice/trait-object-exclusive forms `$[T]`/`$dyn Trait`
            --  — so a `$`-typed binding is never copyable, only
            --  transferable.
            return T.Sigil = R_Excl;
         when others =>
            return False;
      end case;
   end Satisfies_Destruct;
