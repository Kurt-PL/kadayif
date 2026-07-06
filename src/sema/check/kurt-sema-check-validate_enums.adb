separate (Kurt.Sema.Check)
   procedure Validate_Enums is
      --  §8.4.3: a lifetime name shall be unique within its `with
      --  lifetime` clause (checked across all its chains together, for
      --  both struct and enum declarations — there is no other pass
      --  that walks U.Structs/U.Enums specifically for this, so it is
      --  hung off Validate_Enums, which Check already calls).
      procedure Validate_Lifetime_Chains is separate;
   begin
      Validate_Lifetime_Chains;
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
                       Natural (Kurt.Layout.Size_Of (D.Discrim_Ty));
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

            --  §7.2: a `with [!]contract` enum shall have exactly two
            --  branches (one explicit variant, one `#wild#`).
            if D.Is_Contract
              and then Natural (D.Variants.Length) /= 2
            then
               Error ("enum '" & EN & "' declares `with "
                      & (if D.Contract_Inv then "!" else "") & "contract` "
                      & "but has" & D.Variants.Length'Image
                      & " variants; a contract enum shall have exactly "
                      & "two (spec 7.2)");
            end if;

            --  §7.2 inverted-pair symmetry: if A declares `-> B`, B shall
            --  declare `-> A` back, and the truthy/falsey payload types
            --  shall cross-match (A's success = B's failure, and vice
            --  versa).
            if D.Is_Contract and then D.Inv_Type /= null
              and then D.Inv_Type.Kind = T_Named
            then
               declare
                  BN : constant String := SU.To_String (D.Inv_Type.Name);
               begin
                  if not Kurt.Layout.Is_Enum (BN) then
                     Error ("enum '" & EN & "' declares an inverted pair "
                            & "'" & BN & "', which is not a known enum "
                            & "(spec 7.2)");
                  elsif not Kurt.Layout.Is_Contract_Enum (BN) then
                     Error ("enum '" & EN & "' declares an inverted pair "
                            & "'" & BN & "', which does not itself "
                            & "declare `with [!]contract` (spec 7.2)");
                  elsif Kurt.Layout.Contract_Inv_Type_Name (BN) /= EN then
                     Error ("enum '" & EN & "' declares `-> " & BN
                            & "`, but '" & BN & "' does not declare a "
                            & "symmetric `-> " & EN & "` back (spec 7.2)");
                  else
                     --  Payload cross-match: A's success = B's failure,
                     --  A's failure = B's success (spec 7.2).
                     declare
                        A_SV : constant String :=
                          Kurt.Layout.Contract_Success_Variant (EN);
                        A_FV : constant String :=
                          Kurt.Layout.Contract_Fail_Variant (EN);
                        B_SV : constant String :=
                          Kurt.Layout.Contract_Success_Variant (BN);
                        B_FV : constant String :=
                          Kurt.Layout.Contract_Fail_Variant (BN);
                        A_SC : constant Natural :=
                          Kurt.Layout.Variant_Field_Count (EN, A_SV);
                        A_FC : constant Natural :=
                          Kurt.Layout.Variant_Field_Count (EN, A_FV);
                        B_SC : constant Natural :=
                          Kurt.Layout.Variant_Field_Count (BN, B_SV);
                        B_FC : constant Natural :=
                          Kurt.Layout.Variant_Field_Count (BN, B_FV);
                     begin
                        if A_SC /= B_FC or else A_FC /= B_SC
                          or else (A_SC > 0 and then A_SC = B_FC
                            and then not Same_Type
                              (Kurt.Layout.Variant_Field_Type (EN, A_SV, 1),
                               Kurt.Layout.Variant_Field_Type (BN, B_FV, 1)))
                          or else (A_FC > 0 and then A_FC = B_SC
                            and then not Same_Type
                              (Kurt.Layout.Variant_Field_Type (EN, A_FV, 1),
                               Kurt.Layout.Variant_Field_Type (BN, B_SV, 1)))
                        then
                           Error ("enum '" & EN & "' and its inverted "
                                  & "pair '" & BN & "' have mismatched "
                                  & "success/failure payload types "
                                  & "(spec 7.2)");
                        end if;
                     end;
                  end if;
               end;
            end if;
         end;
      end loop;

      --  §4.11.5: `align(N)` requires N to be a power of two.
   end Validate_Enums;
