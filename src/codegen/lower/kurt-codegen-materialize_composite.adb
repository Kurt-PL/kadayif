separate (Kurt.Codegen)
   function Materialize_Composite
     (F : IO.File_Type; ST : in out Lower_State;
      Ty : Type_Access; Init : Expr_Access)
      return Cell_Count
   is
      Aln : constant Cell_Count :=
        Cell_Count'Max (Kurt.Layout.Align_Of (Ty), 1);
      Off : constant Cell_Count :=
        ((ST.Next_Offset + Aln - 1) / Aln) * Aln;
      Sz  : constant Cell_Count := Cell_Count'Max (Sizeof (Ty), 1);

      procedure Zero_Fill (At_Off, At_Sz : Cell_Count) is
         Curr   : Cell_Count := At_Off;
         Rem_Sz : Cell_Count := At_Sz;
      begin
         while Rem_Sz >= 8 loop
            IO.Put_Line (F, "    str     xzr, [x29, #" & Img (Curr) & "]");
            Curr := Curr + 8;
            Rem_Sz := Rem_Sz - 8;
         end loop;
         if Rem_Sz >= 4 then
            IO.Put_Line (F, "    str     wzr, [x29, #" & Img (Curr) & "]");
            Curr := Curr + 4;
            Rem_Sz := Rem_Sz - 4;
         end if;
         if Rem_Sz >= 2 then
            IO.Put_Line (F, "    strh    wzr, [x29, #" & Img (Curr) & "]");
            Curr := Curr + 2;
            Rem_Sz := Rem_Sz - 2;
         end if;
         if Rem_Sz >= 1 then
            IO.Put_Line (F, "    strb    wzr, [x29, #" & Img (Curr) & "]");
         end if;
      end Zero_Fill;

      --  Store the value currently in x9/w9 into [x29, #At_Off] using the
      --  width implied by At_Sz cells (mirrors Lower_Stmt's Store_Sized).
      procedure Store_Sized (At_Off, At_Sz : Cell_Count) is
         Loc : constant String := ", [x29, #" & Img (At_Off) & "]";
      begin
         if At_Sz >= 8 then
            IO.Put_Line (F, "    str     x9" & Loc);
         elsif At_Sz = 4 then
            IO.Put_Line (F, "    str     w9" & Loc);
         elsif At_Sz = 2 then
            IO.Put_Line (F, "    strh    w9" & Loc);
         elsif At_Sz = 1 then
            IO.Put_Line (F, "    strb    w9" & Loc);
         end if;
      end Store_Sized;
   begin
      ST.Next_Offset := Off + Sz;

      case Init.Kind is
         when E_Struct_Lit =>
            Zero_Fill (Off, Sz);
            declare
               SN : constant String :=
                 (if Init.Sem_Ty /= null
                  then SU.To_String (Init.Sem_Ty.Name)
                  else SU.To_String (Init.SL_Name));
            begin
               for I in Init.SL_Fields.First_Index ..
                        Init.SL_Fields.Last_Index
               loop
                  declare
                     FI  : constant Field_Init := Init.SL_Fields.Element (I);
                     FN  : constant String := SU.To_String (FI.Name);
                     FT  : constant Type_Access :=
                       Kurt.Layout.Field_Type (SN, FN);
                     FOf : constant Cell_Count :=
                       Off + Kurt.Layout.Field_Offset (SN, FN);
                     BI  : constant Natural :=
                       (if FI.Val.Kind = E_Path
                          and then Natural (FI.Val.Segments.Length) = 1
                        then Find_Binding
                               (ST, SU.To_String
                                  (FI.Val.Segments.Last_Element))
                        else 0);
                  begin
                     if Is_Aggregate_Type (FT) and then BI /= 0 then
                        Emit_Mem_Copy
                          (F, "x29", ST.Bindings.Element (BI).Offset,
                           "x29", FOf, Sizeof (FT));
                     else
                        Lower_Expr_Into_Reg (F, FI.Val, 9, ST);
                        Store_Sized (FOf, Sizeof (FT));
                     end if;
                     --  §8.8.2 a transferred field source is not dropped
                     --  at its own scope exit.
                     Note_Move (F, ST, FI.Val);
                  end;
               end loop;

               --  §5.5.3: fill each omitted field from its default-value
               --  expression, evaluated here at the point of construction.
               for K in 1 .. Kurt.Layout.Struct_Field_Count (SN) loop
                  declare
                     FN  : constant String :=
                       Kurt.Layout.Struct_Field_Name (SN, K);
                     Dfl : constant Expr_Access :=
                       Kurt.Layout.Field_Default (SN, FN);
                     Supplied : Boolean := False;
                  begin
                     for I in Init.SL_Fields.First_Index ..
                              Init.SL_Fields.Last_Index
                     loop
                        if SU.To_String (Init.SL_Fields.Element (I).Name)
                             = FN
                        then
                           Supplied := True;
                        end if;
                     end loop;
                     if not Supplied and then Dfl /= null then
                        Lower_Expr_Into_Reg (F, Dfl, 9, ST);
                        Store_Sized
                          (Off + Kurt.Layout.Field_Offset (SN, FN),
                           Sizeof (Kurt.Layout.Field_Type (SN, FN)));
                     end if;
                  end;
               end loop;
            end;

         when E_Variant_New =>
            Zero_Fill (Off, Sz);
            declare
               EN : constant String :=
                 (if Init.Sem_Ty /= null
                  then SU.To_String (Init.Sem_Ty.Name)
                  else SU.To_String (Init.VN_Enum));
               VN : constant String := SU.To_String (Init.VN_Variant);
            begin
               --  A void discriminant (§4.11.3) stores nothing.
               if Kurt.Layout.Enum_Disc_Size (EN) > 0 then
                  Lower_Imm (F, 9,
                    (if VN = "#wild#"
                     then Kurt.Layout.Implicit_Wild_Value (EN)
                     else Kurt.Layout.Variant_Value (EN, VN)),
                    False);
                  Store_Sized (Off, Kurt.Layout.Enum_Disc_Size (EN));
               end if;
               for I in Init.VN_Fields.First_Index ..
                        Init.VN_Fields.Last_Index
               loop
                  declare
                     FI   : constant Field_Init :=
                       Init.VN_Fields.Element (I);
                     FN   : constant String := SU.To_String (FI.Name);
                     ST_T : constant Type_Access := Init.Sem_Ty;
                     FO   : constant Long_Long_Integer :=
                       (if ST_T /= null
                        then Kurt.Layout.Variant_Field_Offset_By_Name
                               (ST_T, VN, FN)
                        else Kurt.Layout.Variant_Field_Offset_By_Name
                               (EN, VN, FN));
                     FT   : constant Type_Access :=
                       (if ST_T /= null
                        then Kurt.Layout.Variant_Field_Type_By_Name
                               (ST_T, VN, FN)
                        else Kurt.Layout.Variant_Field_Type_By_Name
                               (EN, VN, FN));
                  begin
                     Lower_Expr_Into_Reg (F, FI.Val, 9, ST);
                     Store_Sized (Off + Cell_Count (FO), Sizeof (FT));
                     --  §8.8.2 a transferred payload source is not
                     --  dropped at its own scope exit.
                     Note_Move (F, ST, FI.Val);
                  end;
               end loop;
            end;

         when E_Tuple_Lit =>
            for I in Init.TL_Elems.First_Index .. Init.TL_Elems.Last_Index
            loop
               declare
                  Idx : constant Natural := I - Init.TL_Elems.First_Index;
               begin
                  Lower_Expr_Into_Reg (F, Init.TL_Elems.Element (I), 9, ST);
                  Store_Sized
                    (Off + Kurt.Layout.Tuple_Field_Offset (Ty, Idx),
                     Sizeof (Kurt.Layout.Tuple_Field_Type (Ty, Idx)));
               end;
            end loop;

         when E_Array_Lit =>
            --  §6.1.6 array / repeat literal, element-wise into the slot
            --  at the element stride. Fat-reference (`&dyn` / slice)
            --  elements are not covered here (bootstrap scope).
            declare
               ESz   : constant Cell_Count := Sizeof (Ty.Elem);
               Is_FP : constant Boolean := Is_Float (Ty.Elem);

               procedure Store_Elem_At (EO : Cell_Count) is
               begin
                  if Is_FP then
                     IO.Put_Line
                       (F, "    str     "
                           & (if ESz = 4 then "s0" else "d0")
                           & ", [x29, #" & Img (EO) & "]");
                  else
                     Store_Sized (EO, ESz);
                  end if;
               end Store_Elem_At;
            begin
               if Init.AL_Repeat > 0 then
                  if Is_FP then
                     Lower_Float_Into_D
                       (F, Init.AL_Elems.First_Element, 0, ST);
                  else
                     Lower_Expr_Into_Reg
                       (F, Init.AL_Elems.First_Element, 9, ST);
                  end if;
                  for I in 0 .. Init.AL_Repeat - 1 loop
                     Store_Elem_At (Off + I * ESz);
                  end loop;
               else
                  for I in Init.AL_Elems.First_Index ..
                           Init.AL_Elems.Last_Index
                  loop
                     if Is_FP then
                        Lower_Float_Into_D
                          (F, Init.AL_Elems.Element (I), 0, ST);
                     else
                        Lower_Expr_Into_Reg
                          (F, Init.AL_Elems.Element (I), 9, ST);
                     end if;
                     Store_Elem_At
                       (Off
                        + Cell_Count (I - Init.AL_Elems.First_Index)
                          * ESz);
                     --  §8.8.2 a destruct-typed element supplied by a
                     --  binding is transferred: clear the source's drop
                     --  flag so it is not also destroyed.
                     Note_Move (F, ST, Init.AL_Elems.Element (I));
                  end loop;
               end if;
            end;

         when others =>
            raise Codegen_Error with
              "not yet supported: this composite literal form as a "
              & "materialised temporary (bootstrap)";
      end case;

      return Off;
   end Materialize_Composite;
