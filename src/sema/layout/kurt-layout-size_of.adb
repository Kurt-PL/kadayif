separate (Kurt.Layout)
   function Size_Of (T : Kurt.Parser.Type_Access) return Cell_Count is
   begin
      if T = null then
         return 8;
      end if;
      case T.Kind is
         --  §4.7: "An array type `[T; N]` whose `N * T@size` ... exceeds
         --  the greatest value representable by `uaddr` ... shall not
         --  appear" — overflow in a size/offset computation is a
         --  translation failure at the point of declaration, not a
         --  silent wraparound. `Cell_Count` here is checked (not
         --  modular), so an overflow raises Constraint_Error; the
         --  handler below converts it to the proper diagnostic instead
         --  of letting it escape as an uncaught "internal error".
         when T_Ref =>
            --  §9.5 / §4.6: a fat reference is two pointers — a reference
            --  to a trait object (ptr + dtable) or to a slice `[T]`
            --  (ptr + len). A thin reference is one pointer.
            if T.Target /= null
              and then (T.Target.Kind = T_Dyn
                        or else (T.Target.Kind = T_Array
                                 and then T.Target.Len = 0))
            then
               return 16;
            end if;
            return 8;  --  pointer width (host aarch64)
         when T_Array =>
            --  §4.6: N elements at the element stride. Every Kurt type's
            --  size is a multiple of its alignment, so stride = size.
            --  An unsized slice (Len = 0) has no value size of its own.
            return T.Len * Size_Of (T.Elem);
         when T_Dyn =>
            --  §9.5: `dyn Trait` is unsized (a placeholder); a reference
            --  to it is the fat pair handled in Ref-size code. Report the
            --  fat-pair size so a stray query is harmless.
            return 16;
         when T_Fn =>
            --  §4.10: a bare subroutine pointer equals `(&raw void)@size`
            --  (one word). §9.9.2: an INVOCABLE type (`/.T/ -> U` / `xfer
            --  /.T/ -> U`) is the two-word tuple `.{ &raw void, &raw void
            --  }` -- field .0 the callable descriptor, field .1 the state
            --  pointer.
            if T.Fn_Invocable then
               return 2 * Kurt.Address_Cells;
            end if;
            return Kurt.Address_Cells;
         when T_Tuple =>
            --  §4.7 / §4.11: positional fields, KSA-packed.
            declare
               Off : Cell_Count := 0;
               Aln : Cell_Count := 1;
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  declare
                     FT : constant Type_Access := T.Elems.Element (I);
                  begin
                     Off := Ceil (Off, Align_Of (FT)) + Size_Of (FT);
                     Aln := Cell_Count'Max (Aln, Align_Of (FT));
                  end;
               end loop;
               return Ceil (Off, Aln);
            end;
         when T_Named =>
            declare
               N : constant String := SU.To_String (T.Name);
               D : Struct_Decl;
            begin
               --  §4.3.2: uiN/siN occupy N cells (N * cellbits bits).
               if N = "ui1" or else N = "si1" then return 1;
               elsif N = "ui2" or else N = "si2" then return 2;
               elsif N = "ui4" or else N = "si4" then return 4;
               elsif N = "ui8" or else N = "si8" then return 8;
               elsif N = "ui16" or else N = "si16" then return 16;
               elsif N = "ui32" or else N = "si32" then return 32;
               --  Floating-point types (§4): size = (1 + e + m) bits / 8.
               elsif N = "fe5m10" or else N = "fe8m7" then return 2;
               elsif N = "fe8m23" then return 4;
               elsif N = "fe11m52" then return 8;
               elsif N = "fe15m112" then return 16;
               elsif N = "fe19m236" then return 32;
               elsif N = "uaddr" or else N = "saddr" then
                  return Kurt.Address_Cells;
               elsif N = "bool" then return 1;
               elsif N = "void" then return 0;
               elsif Is_Verdict (N) then
                  --  §4.5 verdict.<Ok, Err>: ui1 discriminant + the larger
                  --  payload, from the type arguments.
                  declare
                     A   : constant Cell_Count := Align_Of (T);
                     POf : constant Cell_Count := Ceil (1, A);
                     PSz : Cell_Count := 0;
                  begin
                     for I in T.Args.First_Index .. T.Args.Last_Index loop
                        PSz := Cell_Count'Max
                          (PSz, Size_Of (T.Args.Element (I)));
                     end loop;
                     if PSz = 0 then
                        return Ceil (1, A);   --  e.g. verdict.<void, void>
                     end if;
                     return Ceil (POf + PSz, A);
                  end;
               elsif Is_Enum (N) then
                  return Enum_Size (N);
               elsif Find_Struct (N, D) then
                  --  §4.11.2 struct layout (§4.11.4 packed: no
                  --  inter-field padding; §4.11.5 align(N) raises the
                  --  minimum alignment, which rounds the total size).
                  declare
                     Off : Cell_Count := 0;
                     Aln : Cell_Count := 1;
                  begin
                     for I in D.Fields.First_Index .. D.Fields.Last_Index
                     loop
                        declare
                           FT : constant Type_Access :=
                             D.Fields.Element (I).Ty;
                        begin
                           if not D.Repr_Packed then
                              Off := Ceil (Off, Align_Of (FT));
                              Aln := Cell_Count'Max (Aln, Align_Of (FT));
                           end if;
                           Off := Off + Size_Of (FT);
                        end;
                     end loop;
                     if D.Repr_Packed then
                        Aln := 1;
                     end if;
                     Aln := Cell_Count'Max (Aln, D.Align_N);
                     return Ceil (Off, Aln);
                  end;
               else
                  return 8;  --  unknown named type
               end if;
            end;
      end case;
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Size_Of;
