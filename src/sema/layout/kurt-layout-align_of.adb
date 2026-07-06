separate (Kurt.Layout)
   function Align_Of (T : Kurt.Parser.Type_Access) return Cell_Count is
   begin
      if T = null then
         return 8;
      end if;
      case T.Kind is
         when T_Ref =>
            return 8;
         when T_Array =>
            --  §4.6: an array aligns as its element type.
            return Align_Of (T.Elem);
         when T_Fn =>
            --  §4.10: a subroutine pointer is pointer-sized/aligned.
            return Kurt.Address_Cells;
         when T_Dyn =>
            --  §9.5: a bare `dyn Trait` is unsized; only `&dyn Trait`
            --  (a fat ref) is sized. Align as a pointer pair.
            return 8;
         when T_Tuple =>
            declare
               A : Cell_Count := 1;
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  A := Cell_Count'Max (A, Align_Of (T.Elems.Element (I)));
               end loop;
               --  §4.2: a type whose size is zero has alignment zero.
               if Size_Of (T) = 0 then
                  return 0;
               end if;
               return A;
            end;
         when T_Named =>
            declare
               N : constant String := SU.To_String (T.Name);
               D : Struct_Decl;
            begin
               if Is_Verdict (N) then
                  --  §4.5: max of the discriminant (1) and the alignments of
                  --  the payload element types.
                  declare
                     A : Cell_Count := 1;
                  begin
                     for I in T.Args.First_Index .. T.Args.Last_Index loop
                        A := Cell_Count'Max
                          (A, Align_Of (T.Args.Element (I)));
                     end loop;
                     return A;
                  end;
               elsif Find_Struct (N, D) then
                  --  §4.2: a type whose size is zero has alignment zero
                  --  (e.g. `struct empty {}`).
                  if Size_Of (T) = 0 then
                     return 0;
                  end if;
                  declare
                     A : Cell_Count := 1;
                  begin
                     --  §4.11.4: a packed struct has alignment 1.
                     if not D.Repr_Packed then
                        for I in D.Fields.First_Index ..
                                 D.Fields.Last_Index
                        loop
                           A := Cell_Count'Max
                             (A, Align_Of (D.Fields.Element (I).Ty));
                        end loop;
                     end if;
                     --  §4.11.5: align(N) raises the minimum alignment.
                     return Cell_Count'Max (A, D.Align_N);
                  end;
               elsif Is_Enum (N) then
                  --  §4.2: zero size (e.g. a single empty variant with a
                  --  void discriminant) means alignment zero.
                  if Enum_Size (N) = 0 then
                     return 0;
                  end if;
                  return Enum_Align (N);
               else
                  return Size_Of (T);  --  numeric: align == size
               end if;
            end;
      end case;
   end Align_Of;
