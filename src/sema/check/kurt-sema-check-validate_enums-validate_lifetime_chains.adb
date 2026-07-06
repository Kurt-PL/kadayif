separate (Kurt.Sema.Check.Validate_Enums)
   procedure Validate_Lifetime_Chains is
      --  §8.4.3 "A lifetime name shall be unique within its `with
      --  lifetime` clause" — Owner names the struct/enum for the
      --  diagnostic; Chains is its full clause (every chain together).
      procedure Check_Unique
        (Owner : String; Chains : Kurt.Parser.Lifetime_Chain_Vectors.Vector)
      is
         Seen : Path_Segments.Vector;
      begin
         for Ch of Chains loop
            for P in Ch.First_Index .. Ch.Last_Index loop
               declare
                  Nm : constant String := SU.To_String (Ch.Element (P));
               begin
                  for S of Seen loop
                     if SU.To_String (S) = Nm then
                        Error ("lifetime '" & Nm & "' repeated in " & Owner
                               & "'s `with lifetime` clause: a lifetime "
                               & "name shall be unique within its clause "
                               & "(spec 8.4.3)");
                     end if;
                  end loop;
                  Seen.Append (SU.To_Unbounded_String (Nm));
               end;
            end loop;
         end loop;
      end Check_Unique;

      function In_Chains
        (Chains : Kurt.Parser.Lifetime_Chain_Vectors.Vector; Nm : String)
         return Boolean
      is
      begin
         for Ch of Chains loop
            for P in Ch.First_Index .. Ch.Last_Index loop
               if SU.To_String (Ch.Element (P)) = Nm then
                  return True;
               end if;
            end loop;
         end loop;
         return False;
      end In_Chains;

      --  §8.4.3 "A reference annotated with a lifetime not declared in
      --  the enclosing `with lifetime` clause and not inferable by
      --  elision shall not appear." Checked only when the declaration
      --  HAS a clause: a field's explicit top-level annotation shall
      --  then name a chain lifetime, the field's own implicit lifetime
      --  identifier (its name, §8.4.2), or a permanent lifetime
      --  ('static/'const, §8.4.1). Clause-less declarations are exempt —
      --  their annotations may refer to generic lifetime parameters,
      --  which the bootstrap erases at parse time and cannot re-check.
      procedure Check_Annotations
        (Owner  : String;
         Chains : Kurt.Parser.Lifetime_Chain_Vectors.Vector;
         Fields : Struct_Field_Vectors.Vector)
      is
      begin
         if Chains.Is_Empty then
            return;
         end if;
         for F of Fields loop
            if F.Ty /= null and then F.Ty.Kind = T_Ref
              and then SU.Length (F.Ty.R_Life) > 0
            then
               declare
                  Nm : constant String := SU.To_String (F.Ty.R_Life);
               begin
                  if Nm /= "static" and then Nm /= "const"
                    and then Nm /= SU.To_String (F.Name)
                    and then not In_Chains (Chains, Nm)
                  then
                     Error ("lifetime '" & Nm & "' annotating field '"
                            & SU.To_String (F.Name) & "' of " & Owner
                            & " is not declared in its `with lifetime` "
                            & "clause and is not inferable by elision "
                            & "(spec 8.4.3)");
                  end if;
               end;
            end if;
         end loop;
      end Check_Annotations;
   begin
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            Owner : constant String :=
              "struct '" & SU.To_String (U.Structs.Element (I).Name) & "'";
         begin
            Check_Unique (Owner, U.Structs.Element (I).Lifetime_Chains);
            Check_Annotations
              (Owner, U.Structs.Element (I).Lifetime_Chains,
               U.Structs.Element (I).Fields);
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            Owner : constant String :=
              "enum '" & SU.To_String (U.Enums.Element (I).Name) & "'";
         begin
            Check_Unique (Owner, U.Enums.Element (I).Lifetime_Chains);
            for V of U.Enums.Element (I).Variants loop
               Check_Annotations
                 (Owner, U.Enums.Element (I).Lifetime_Chains, V.Payload);
            end loop;
         end;
      end loop;
   end Validate_Lifetime_Chains;
