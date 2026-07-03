separate (Kurt.Sema.Check)
   procedure Validate_Enums is
   begin
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            D  : constant Kurt.Parser.Enum_Decl := U.Enums.Element (I);
            EN : constant String := SU.To_String (D.Name);
         begin
            if D.Discrim_Ty /= null then
               if Is_Void_Type (D.Discrim_Ty) then
                  declare
                     Has_Wild_Canon : Boolean := False;
                  begin
                     for J in D.Variants.First_Index .. D.Variants.Last_Index loop
                        if D.Variants.Element (J).Wild_Canon then
                           Has_Wild_Canon := True;
                        end if;
                     end loop;
                     if Natural (D.Variants.Length) > 1 or else Has_Wild_Canon then
                        Error ("enum '" & EN & "': `with discrim(void)` requires "
                               & "at most one variant and no #wild#(V) canonical value (spec 4.11.3)");
                     end if;
                  end;
               elsif not Is_Integer_Type (D.Discrim_Ty) then
                  Error ("enum '" & EN & "': `with discrim(T)` requires "
                         & "an integer type or void, got '"
                         & Image (D.Discrim_Ty) & "' (spec 4.11.3)");
               else
                  declare
                     Sz  : constant Natural :=
                       Kurt.Layout.Size_Of (D.Discrim_Ty);
                     Sgn : constant Boolean :=
                       Kurt.Layout.Enum_Disc_Signed (EN);
                     Lo  : Long_Long_Integer := 0;
                     Hi  : Long_Long_Integer := Long_Long_Integer'Last;
                  begin
                     if Sgn and then Sz < 8 then
                        Lo := -(2 ** (8 * Sz - 1));
                        Hi := 2 ** (8 * Sz - 1) - 1;
                     elsif not Sgn and then Sz < 8 then
                        Lo := 0;
                        Hi := 2 ** (8 * Sz) - 1;
                     elsif not Sgn then
                        Lo := 0;   --  ui8: any representable literal fits
                     end if;
                     for J in D.Variants.First_Index ..
                              D.Variants.Last_Index
                     loop
                        declare
                           V : constant Long_Long_Integer :=
                             D.Variants.Element (J).Value;
                        begin
                           if V < Lo or else V > Hi then
                              Error ("enum '" & EN & "': discriminant"
                                     & V'Image & " does not fit in `"
                                     & Image (D.Discrim_Ty)
                                     & "` (spec 4.11.3)");
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            end if;

            --  §5.7 at most one `#wild#` variant per enum. (Variant-name
            --  uniqueness and discriminant-collision are enforced during
            --  discriminant resolution.) A pure rejection of an ill-formed
            --  declaration; never affects a valid enum.
            declare
               Wild_Count : Natural := 0;
            begin
               for J in D.Variants.First_Index .. D.Variants.Last_Index loop
                  if D.Variants.Element (J).Is_Wild then
                     Wild_Count := Wild_Count + 1;
                  end if;
               end loop;
               if Wild_Count > 1 then
                  Error ("enum '" & EN & "' declares" & Wild_Count'Image
                         & " `#wild#` variants; at most one is permitted "
                         & "(spec 5.7)");
               end if;
            end;
         end;
      end loop;

      --  §4.11.5: `align(N)` requires N to be a power of two.
   end Validate_Enums;
