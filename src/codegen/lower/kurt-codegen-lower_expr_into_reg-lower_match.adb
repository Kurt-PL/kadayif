separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Match (E : Expr_Access) is
      FN      : constant String  := SU.To_String (ST.Fn_Name);
      Idx     : constant Natural := ST.If_Idx;
      L_End   : constant String  := "Lmatch_" & FN & "_end_" & Img (Idx);
      Scrut_T : constant Type_Access := Type_Of_Expr (E.M_Scrut, ST);

      --  An enum scrutinee bound to a local is matched in place: the
      --  discriminant sits at the binding's slot start and payload fields
      --  are bound as slot+offset aliases (no copy).
      Enum_Binding : Boolean := False;
      Base         : Cell_Count := 0;
      EN           : SU.Unbounded_String;
      --  §7.4.2 a `[T;N]` array binding matched by slice patterns in place.
      Array_Binding : Boolean := False;
      Arr_Base      : Cell_Count := 0;
      --  item(e)/§5.10.2 a struct binding matched by a struct pattern
      --  (`point { x, y }`) in place: field bindings alias the scrutinee's
      --  slot + field offset (no copy). Only engaged when some arm
      --  actually uses the struct-pattern shape -- otherwise the scrutinee
      --  falls through to the existing scalar/whole-value path unchanged.
      Struct_Binding : Boolean := False;
      SBase          : Cell_Count := 0;
      SN             : SU.Unbounded_String;
      --  §5.10.1 a tuple binding matched by `.{ ... }` patterns in place:
      --  positional bindings alias the scrutinee's slot + field offset.
      Tuple_Binding : Boolean := False;
      TBase         : Cell_Count := 0;

      function Is_Struct_Pat (P : Pattern) return Boolean is
        (P.Kind = Pat_Variant and then Natural (P.Path.Length) = 1
         and then (not P.Bindings.Is_Empty or else P.Has_Rest));

      --  §5.10.1 `#wild#(name)` raw-representation binding: the matched
      --  value's cells viewed as a `&[ui1]` slice. Materialise the fat
      --  reference (ptr = the value's frame address, len = its size) in a
      --  fresh 16-byte temp and register the binding there.
      function Mk_Repr_Slice_Ty return Type_Access is
         Arr : constant Type_Access :=
           new AST_Type'(Kind => T_Array,
                         Elem => new AST_Type'
                           (Kind => T_Named,
                            Name => SU.To_Unbounded_String ("ui1"),
                            Args => <>),
                         Len => 0, Len_Expr => null);
      begin
         return new AST_Type'(Kind => T_Ref, Sigil => R_Shared,
                              R_Volatile => False, R_Store => RS_None,
                              R_Life => SU.Null_Unbounded_String,
                              Target => Arr);
      end Mk_Repr_Slice_Ty;

      procedure Bind_Wild_Repr
        (Name : SU.Unbounded_String; Base : Cell_Count; Sz : Cell_Count)
      is
         Tmp : constant Cell_Count :=
           ((ST.Next_Offset + 7) / 8) * 8;
      begin
         ST.Next_Offset := Tmp + 16;
         IO.Put_Line (F, "    add     x9, x29, #" & Img (Base));
         IO.Put_Line (F, "    str     x9, [x29, #" & Img (Tmp) & "]");
         Lower_Imm (F, 9, Long_Long_Integer (Sz), True);
         IO.Put_Line (F, "    str     x9, [x29, #" & Img (Tmp + 8) & "]");
         ST.Bindings.Append
           ((Name => Name, Offset => Tmp, Ty => Mk_Repr_Slice_Ty));
      end Bind_Wild_Repr;

      --  §5.10 integer / range sub-pattern test against the Sz-cell value
      --  at [x29, #Base]: load it (sign- or zero-extended to 64 bits per
      --  the value type's signedness), compare, and fall through to
      --  L_Next on a mismatch.
      procedure Test_Scalar_At
        (P : Pattern; Ty : Type_Access; Base : Cell_Count; L_Next : String)
      is
         Sz     : constant Cell_Count := Sizeof (Ty);
         Signed : constant Boolean := Is_Signed_Int (Ty);
         Loc    : constant String := ", [x29, #" & Img (Base) & "]";
         C_Lt   : constant String := (if Signed then "lt" else "lo");
         C_Gt   : constant String := (if Signed then "gt" else "hi");
         C_Ge   : constant String := (if Signed then "ge" else "hs");
      begin
         if Sz = 1 then
            IO.Put_Line (F, "    ldrb    w9" & Loc);
            if Signed then
               IO.Put_Line (F, "    sxtb    x9, w9");
            end if;
         elsif Sz = 2 then
            IO.Put_Line (F, "    ldrh    w9" & Loc);
            if Signed then
               IO.Put_Line (F, "    sxth    x9, w9");
            end if;
         elsif Sz = 4 then
            IO.Put_Line (F, "    ldr     w9" & Loc);
            if Signed then
               IO.Put_Line (F, "    sxtw    x9, w9");
            end if;
         else
            IO.Put_Line (F, "    ldr     x9" & Loc);
         end if;
         if P.Kind = Pat_Int then
            Lower_Imm (F, 10, P.Int_V, True);
            IO.Put_Line (F, "    cmp     x9, x10");
            IO.Put_Line (F, "    b.ne    " & L_Next);
         else   --  Pat_Range
            Lower_Imm (F, 10, P.Int_V, True);
            IO.Put_Line (F, "    cmp     x9, x10");
            IO.Put_Line (F, "    b." & C_Lt & "    " & L_Next);
            Lower_Imm (F, 10, P.Range_Hi, True);
            IO.Put_Line (F, "    cmp     x9, x10");
            IO.Put_Line (F, "    b."
              & (if P.Range_Incl then C_Gt else C_Ge)
              & "    " & L_Next);
         end if;
      end Test_Scalar_At;

      --  §7.4 item(a): recursively lower a nested payload sub-pattern P
      --  against the value at frame offset Base (type Ty), within the
      --  CURRENT arm -- any failing test (a nested discriminant mismatch)
      --  branches to that arm's own L_Next, exactly like any other failing
      --  sub-test within one arm (spec 7.4, sema counterpart: Bind_Nested
      --  in Kurt.Sema.Check.Infer.Infer_Match).
      procedure Bind_Nested_CG
        (P : Pattern; Ty : Type_Access; Base : Cell_Count; L_Next : String)
      is
      begin
         case P.Kind is
            when Pat_Wild =>
               if SU.Length (P.Bind_Name) > 0 then
                  ST.Bindings.Append
                    ((Name => P.Bind_Name, Offset => Base, Ty => Ty));
               end if;
               if SU.Length (P.Wild_Bind) > 0 then
                  Bind_Wild_Repr (P.Wild_Bind, Base, Sizeof (Ty));
               end if;
            when Pat_Int | Pat_Range =>
               --  §5.10 `#`-attached scalar test on a payload/tuple field
               --  (`name # sub` arrives as the sub-pattern carrying
               --  Bind_Name).
               Test_Scalar_At (P, Ty, Base, L_Next);
               if SU.Length (P.Bind_Name) > 0 then
                  ST.Bindings.Append
                    ((Name => P.Bind_Name, Offset => Base, Ty => Ty));
               end if;
            when Pat_Tuple =>
               --  §5.10.1 positional decomposition of the tuple at Base.
               for K in 1 .. Natural (P.Bindings.Length) loop
                  declare
                     FOff : constant Cell_Count :=
                       Base + Kurt.Layout.Tuple_Field_Offset (Ty, K - 1);
                     FT   : constant Type_Access :=
                       Kurt.Layout.Tuple_Field_Type (Ty, K - 1);
                  begin
                     if SU.Length (P.Bindings.Element (K)) > 0 then
                        ST.Bindings.Append
                          ((Name   => P.Bindings.Element (K),
                            Offset => FOff, Ty => FT));
                     end if;
                     if K <= Natural (P.Sub_Pats.Length)
                       and then P.Sub_Pats.Element (K) /= null
                     then
                        Bind_Nested_CG
                          (P.Sub_Pats.Element (K).all, FT, FOff, L_Next);
                     end if;
                  end;
               end loop;
            when Pat_Variant =>
               if Natural (P.Path.Length) = 1
                 and then (not P.Bindings.Is_Empty or else P.Has_Rest)
               then
                  --  Nested struct pattern: no discriminant, field offsets
                  --  only (named-field lookup with positional fallback,
                  --  matching the sema side).
                  declare
                     Snm : constant String := SU.To_String (Ty.Name);
                  begin
                     for K in 1 .. Natural (P.Bindings.Length) loop
                        declare
                           FName : constant String :=
                             (if K <= Natural (P.Bind_Fields.Length)
                                and then SU.Length
                                  (P.Bind_Fields.Element (K)) > 0
                              then SU.To_String (P.Bind_Fields.Element (K))
                              elsif SU.Length (P.Bindings.Element (K)) > 0
                              then SU.To_String (P.Bindings.Element (K))
                              else Kurt.Layout.Struct_Field_Name (Snm, K));
                           FOff : constant Cell_Count :=
                             Base + Kurt.Layout.Field_Offset (Snm, FName);
                           FT   : constant Type_Access :=
                             Kurt.Layout.Field_Type (Snm, FName);
                        begin
                           if SU.Length (P.Bindings.Element (K)) > 0 then
                              ST.Bindings.Append
                                ((Name   => P.Bindings.Element (K),
                                  Offset => FOff, Ty => FT));
                           end if;
                           if K <= Natural (P.Sub_Pats.Length)
                             and then P.Sub_Pats.Element (K) /= null
                           then
                              Bind_Nested_CG
                                (P.Sub_Pats.Element (K).all, FT, FOff,
                                 L_Next);
                           end if;
                        end;
                     end loop;
                  end;
               elsif Natural (P.Path.Length) = 1 then
                  ST.Bindings.Append
                    ((Name => P.Path.First_Element, Offset => Base,
                      Ty => Ty));
               else
                  declare
                     EN2  : constant String := SU.To_String (Ty.Name);
                     VN2  : constant String :=
                       SU.To_String (P.Path.Last_Element);
                     DS2  : constant Cell_Count :=
                       Kurt.Layout.Enum_Disc_Size (EN2);
                  begin
                     if DS2 > 0 then
                        Load_From_Frame (Base, DS2);
                        Lower_Imm
                          (F, 10, Kurt.Layout.Variant_Value (EN2, VN2),
                           False);
                        IO.Put_Line (F, "    cmp     w9, w10");
                        IO.Put_Line (F, "    b.ne    " & L_Next);
                     end if;
                     for K in 1 .. Natural (P.Bindings.Length) loop
                        declare
                           FOff : constant Cell_Count :=
                             Base + Pat_Field_Off (P, Ty, VN2, K);
                           FT   : constant Type_Access :=
                             Pat_Field_Ty (P, Ty, VN2, K);
                        begin
                           if SU.Length (P.Bindings.Element (K)) > 0 then
                              ST.Bindings.Append
                                ((Name   => P.Bindings.Element (K),
                                  Offset => FOff, Ty => FT));
                           end if;
                           if K <= Natural (P.Sub_Pats.Length)
                             and then P.Sub_Pats.Element (K) /= null
                           then
                              Bind_Nested_CG
                                (P.Sub_Pats.Element (K).all, FT, FOff,
                                 L_Next);
                           end if;
                        end;
                     end loop;
                  end;
               end if;
            when others =>
               null;   --  item(b): not yet shipped.
         end case;
      end Bind_Nested_CG;
   begin
      ST.If_Idx := ST.If_Idx + 1;

      if Scrut_T /= null and then Scrut_T.Kind = T_Named
        and then Kurt.Layout.Is_Struct (SU.To_String (Scrut_T.Name))
        and then E.M_Scrut.Kind = E_Path
        and then Natural (E.M_Scrut.Segments.Length) = 1
      then
         declare
            Has_SF : Boolean := False;
         begin
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               if Is_Struct_Pat (E.M_Arms.Element (I).Pat) then
                  Has_SF := True;
               end if;
            end loop;
            if Has_SF then
               declare
                  Bi : constant Natural :=
                    Find_Binding (ST, SU.To_String
                                    (E.M_Scrut.Segments.Last_Element));
               begin
                  if Bi /= 0 then
                     Struct_Binding := True;
                     SBase := ST.Bindings.Element (Bi).Offset;
                     SN    := Scrut_T.Name;
                  end if;
               end;
            end if;
         end;
      end if;

      if Scrut_T /= null and then Scrut_T.Kind = T_Tuple
        and then E.M_Scrut.Kind = E_Path
        and then Natural (E.M_Scrut.Segments.Length) = 1
      then
         declare
            Bi : constant Natural :=
              Find_Binding (ST, SU.To_String
                              (E.M_Scrut.Segments.Last_Element));
         begin
            if Bi /= 0 then
               Tuple_Binding := True;
               TBase := ST.Bindings.Element (Bi).Offset;
            end if;
         end;
      end if;

      if Scrut_T /= null and then Scrut_T.Kind = T_Named
        and then Kurt.Layout.Is_Enum (SU.To_String (Scrut_T.Name))
        and then E.M_Scrut.Kind = E_Path
        and then Natural (E.M_Scrut.Segments.Length) = 1
      then
         declare
            Bi : constant Natural :=
              Find_Binding (ST, SU.To_String
                              (E.M_Scrut.Segments.Last_Element));
         begin
            if Bi /= 0 then
               Enum_Binding := True;
               Base := ST.Bindings.Element (Bi).Offset;
               EN   := Scrut_T.Name;
            end if;
         end;
      elsif Scrut_T /= null and then Scrut_T.Kind = T_Array
        and then Scrut_T.Len > 0
        and then E.M_Scrut.Kind = E_Path
        and then Natural (E.M_Scrut.Segments.Length) = 1
      then
         declare
            Bi : constant Natural :=
              Find_Binding (ST, SU.To_String
                              (E.M_Scrut.Segments.Last_Element));
         begin
            if Bi /= 0 then
               Array_Binding := True;
               Arr_Base := ST.Bindings.Element (Bi).Offset;
            end if;
         end;
      end if;

      if Enum_Binding then
         declare
            Ename     : constant String  := SU.To_String (EN);
            Disc_Size : constant Cell_Count :=
              Kurt.Layout.Enum_Disc_Size (Ename);
         begin
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
               begin
                  case Arm.Pat.Kind is
                     when Pat_Wild =>
                        --  §7.4: a guard on a catch-all may fail, so it needs
                        --  a fall-through label to the following arm.
                        declare
                           Saved : constant Natural :=
                             Natural (ST.Bindings.Length);
                        begin
                           if SU.Length (Arm.Pat.Wild_Bind) > 0 then
                              Bind_Wild_Repr
                                (Arm.Pat.Wild_Bind, Base, Sizeof (Scrut_T));
                           end if;
                           if Arm.Guard /= null then
                              Lower_Expr_Into_Reg
                                (F, Arm.Guard, Target_Reg, ST);
                              IO.Put_Line (F, "    cbz     w"
                                              & Img (Target_Reg)
                                              & ", " & L_Next);
                           end if;
                           Lower_Expr_Into_Reg
                             (F, Arm.Arm_Body, Target_Reg, ST);
                           while Natural (ST.Bindings.Length) > Saved loop
                              ST.Bindings.Delete_Last;
                           end loop;
                           IO.Put_Line (F, "    b       " & L_End);
                           if Arm.Guard /= null then
                              IO.Put_Line (F, L_Next & ":");
                           end if;
                        end;
                     when Pat_Variant =>
                        if Natural (Arm.Pat.Path.Length) = 1 then
                           --  §5.10.1 bare-identifier catch-all over an enum:
                           --  matches unconditionally, binding the whole value.
                           declare
                              Saved : constant Natural :=
                                Natural (ST.Bindings.Length);
                           begin
                              ST.Bindings.Append
                                ((Name   => Arm.Pat.Path.First_Element,
                                  Offset => Base,
                                  Ty     => Scrut_T));
                              if Arm.Guard /= null then
                                 Lower_Expr_Into_Reg
                                   (F, Arm.Guard, Target_Reg, ST);
                                 IO.Put_Line
                                   (F, "    cbz     w" & Img (Target_Reg)
                                       & ", " & L_Next);
                              end if;
                              Lower_Expr_Into_Reg
                                (F, Arm.Arm_Body, Target_Reg, ST);
                              while Natural (ST.Bindings.Length) > Saved loop
                                 ST.Bindings.Delete_Last;
                              end loop;
                              IO.Put_Line (F, "    b       " & L_End);
                              IO.Put_Line (F, L_Next & ":");
                           end;
                        else
                        declare
                           VN  : constant String := SU.To_String
                             (Arm.Pat.Path.Last_Element);
                           Saved : constant Natural :=
                             Natural (ST.Bindings.Length);
                        begin
                           --  A void discriminant (§4.11.3: single
                           --  variant) matches unconditionally.
                           if Disc_Size > 0 then
                              Load_From_Frame (Base, Disc_Size);
                              Lower_Imm (F, 10,
                                Kurt.Layout.Variant_Value (Ename, VN),
                                False);
                              IO.Put_Line (F, "    cmp     w9, w10");
                              IO.Put_Line (F, "    b.ne    " & L_Next);
                           end if;
                           --  Bind payload fields as slot+offset aliases;
                           --  item(a) a nested-pattern slot recurses (its
                           --  own discriminant test shares this arm's
                           --  L_Next) instead of binding a plain name.
                           for K in 1 .. Natural (Arm.Pat.Bindings.Length)
                           loop
                              declare
                                 FOff : constant Cell_Count :=
                                   Base
                                     + Pat_Field_Off (Arm.Pat, Scrut_T, VN, K);
                                 FT   : constant Type_Access :=
                                   Pat_Field_Ty (Arm.Pat, Scrut_T, VN, K);
                              begin
                                 if SU.Length
                                      (Arm.Pat.Bindings.Element (K)) > 0
                                 then
                                    ST.Bindings.Append
                                      ((Name   => Arm.Pat.Bindings.Element
                                                    (K),
                                        Offset => FOff, Ty => FT));
                                 end if;
                                 if K <= Natural (Arm.Pat.Sub_Pats.Length)
                                   and then Arm.Pat.Sub_Pats.Element (K)
                                              /= null
                                 then
                                    Bind_Nested_CG
                                      (Arm.Pat.Sub_Pats.Element (K).all, FT,
                                       FOff, L_Next);
                                 end if;
                              end;
                           end loop;
                           --  §7.4: guard runs with payload bindings in scope;
                           --  on failure fall through to the next arm.
                           if Arm.Guard /= null then
                              Lower_Expr_Into_Reg
                                (F, Arm.Guard, Target_Reg, ST);
                              IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                              & ", " & L_Next);
                           end if;
                           Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                           while Natural (ST.Bindings.Length) > Saved loop
                              ST.Bindings.Delete_Last;
                           end loop;
                           IO.Put_Line (F, "    b       " & L_End);
                           IO.Put_Line (F, L_Next & ":");
                        end;
                        end if;
                     when Pat_Int | Pat_Range | Pat_Slice | Pat_Tuple =>
                        raise Program_Error with
                          "codegen: numeric/slice/tuple pattern on enum "
                          & "scrutinee";
                  end case;
               end;
            end loop;
         end;
      elsif Array_Binding then
         --  §7.4.2 slice patterns over a `[T;N]` binding. N is static, so the
         --  length test is resolved at compile time; element positions are
         --  fixed offsets (front before `...`, back after).
         declare
            N     : constant Cell_Count := Scrut_T.Len;
            ESize : constant Cell_Count := Sizeof (Scrut_T.Elem);
            Wide  : constant Boolean := ESize > 4;
            SR    : constant String := (if Wide then "x9" else "w9");
            CR    : constant String := (if Wide then "x10" else "w10");
         begin
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
               begin
                  if Arm.Pat.Kind = Pat_Wild then
                     declare
                        Saved : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        if SU.Length (Arm.Pat.Wild_Bind) > 0 then
                           Bind_Wild_Repr
                             (Arm.Pat.Wild_Bind, Arr_Base,
                              Sizeof (Scrut_T));
                        end if;
                        Lower_Expr_Into_Reg
                          (F, Arm.Arm_Body, Target_Reg, ST);
                        while Natural (ST.Bindings.Length) > Saved loop
                           ST.Bindings.Delete_Last;
                        end loop;
                        IO.Put_Line (F, "    b       " & L_End);
                     end;
                  elsif Arm.Pat.Kind = Pat_Slice then
                     declare
                        SE       : Slice_Elem_Vectors.Vector renames
                          Arm.Pat.Slice_Elems;
                        Rest_At  : Integer := -1;
                        K        : Cell_Count := 0;  --  non-rest elem count
                     begin
                        for J in SE.First_Index .. SE.Last_Index loop
                           if SE.Element (J).Kind = SE_Rest then
                              Rest_At := J;
                           else
                              K := K + 1;
                           end if;
                        end loop;
                        --  Static length filter; skip arms that cannot match.
                        if (Rest_At < 0 and then N = K)
                          or else (Rest_At >= 0 and then N >= K)
                        then
                           declare
                              Saved   : constant Natural :=
                                Natural (ST.Bindings.Length);
                              Front   : Cell_Count := 0;  -- idx before rest
                              Back    : Cell_Count := 0;  -- count after rest
                              Has_Cmp : Boolean := False;

                              --  Element J's array index, given its position.
                              function Arr_Idx
                                (Pos : Cell_Count; After : Boolean;
                                 Back_Pos : Cell_Count)
                                return Cell_Count is
                                (if After then N - Back + Back_Pos else Pos);

                              Seen_Rest : Boolean := False;
                           begin
                              --  count trailing elements after the rest
                              if Rest_At >= 0 then
                                 for J in Rest_At + 1 .. SE.Last_Index loop
                                    Back := Back + 1;
                                 end loop;
                              end if;
                              for J in SE.First_Index .. SE.Last_Index loop
                                 declare
                                    El  : constant Slice_Elem :=
                                      SE.Element (J);
                                    AIdx : Cell_Count;
                                 begin
                                    if El.Kind = SE_Rest then
                                       Seen_Rest := True;
                                    else
                                       if Seen_Rest then
                                          AIdx := Arr_Idx (0, True,
                                            Cell_Count ((J - Rest_At) - 1));
                                       else
                                          AIdx := Front;
                                          Front := Front + 1;
                                       end if;
                                       declare
                                          Off : constant Cell_Count :=
                                            Arr_Base + AIdx * ESize;
                                       begin
                                          if El.Kind = SE_Int then
                                             if Wide then
                                                IO.Put_Line (F,
                                                  "    ldr     x9, [x29, #"
                                                  & Img (Off) & "]");
                                             else
                                                Load_From_Frame (Off, ESize);
                                             end if;
                                             Lower_Imm (F, 10, El.Int_V, Wide);
                                             IO.Put_Line (F, "    cmp     "
                                               & SR & ", " & CR);
                                             IO.Put_Line (F, "    b.ne    "
                                               & L_Next);
                                             Has_Cmp := True;
                                          elsif El.Kind = SE_Bind then
                                             ST.Bindings.Append
                                               ((Name   => El.Name,
                                                 Offset => Off,
                                                 Ty     => Scrut_T.Elem));
                                          end if;
                                       end;
                                    end if;
                                 end;
                              end loop;
                              Lower_Expr_Into_Reg
                                (F, Arm.Arm_Body, Target_Reg, ST);
                              while Natural (ST.Bindings.Length) > Saved loop
                                 ST.Bindings.Delete_Last;
                              end loop;
                              IO.Put_Line (F, "    b       " & L_End);
                              if Has_Cmp then
                                 IO.Put_Line (F, L_Next & ":");
                              end if;
                           end;
                        end if;
                     end;
                  end if;
               end;
            end loop;
         end;
      elsif Struct_Binding then
         --  item(e)/§5.10.2: a struct scrutinee matched by a struct
         --  pattern. No discriminant exists, so a struct-pattern arm
         --  matches unconditionally (subject to its guard); field
         --  bindings alias the scrutinee's slot + field offset.
         declare
            Snm : constant String := SU.To_String (SN);
         begin
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
               begin
                  if Arm.Pat.Kind = Pat_Wild then
                     declare
                        Saved : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        if SU.Length (Arm.Pat.Wild_Bind) > 0 then
                           Bind_Wild_Repr
                             (Arm.Pat.Wild_Bind, SBase, Sizeof (Scrut_T));
                        end if;
                        if Arm.Guard /= null then
                           Lower_Expr_Into_Reg
                             (F, Arm.Guard, Target_Reg, ST);
                           IO.Put_Line (F, "    cbz     w"
                                           & Img (Target_Reg)
                                           & ", " & L_Next);
                        end if;
                        Lower_Expr_Into_Reg
                          (F, Arm.Arm_Body, Target_Reg, ST);
                        while Natural (ST.Bindings.Length) > Saved loop
                           ST.Bindings.Delete_Last;
                        end loop;
                        IO.Put_Line (F, "    b       " & L_End);
                        if Arm.Guard /= null then
                           IO.Put_Line (F, L_Next & ":");
                        end if;
                     end;
                  elsif Is_Struct_Pat (Arm.Pat) then
                     declare
                        Saved : constant Natural :=
                          Natural (ST.Bindings.Length);
                        Need_Next : Boolean := Arm.Guard /= null;
                     begin
                        for K in 1 .. Natural (Arm.Pat.Bindings.Length) loop
                           declare
                              FName : constant String :=
                                (if K <= Natural
                                     (Arm.Pat.Bind_Fields.Length)
                                   and then SU.Length
                                     (Arm.Pat.Bind_Fields.Element (K)) > 0
                                 then SU.To_String
                                   (Arm.Pat.Bind_Fields.Element (K))
                                 elsif SU.Length
                                   (Arm.Pat.Bindings.Element (K)) > 0
                                 then SU.To_String
                                   (Arm.Pat.Bindings.Element (K))
                                 else Kurt.Layout.Struct_Field_Name (Snm, K));
                              FOff : constant Cell_Count :=
                                SBase + Kurt.Layout.Field_Offset (Snm, FName);
                              FT   : constant Type_Access :=
                                Kurt.Layout.Field_Type (Snm, FName);
                           begin
                              if SU.Length
                                   (Arm.Pat.Bindings.Element (K)) > 0
                              then
                                 ST.Bindings.Append
                                   ((Name   => Arm.Pat.Bindings.Element (K),
                                     Offset => FOff, Ty => FT));
                              end if;
                              if K <= Natural (Arm.Pat.Sub_Pats.Length)
                                and then Arm.Pat.Sub_Pats.Element (K)
                                           /= null
                              then
                                 Need_Next := True;
                                 Bind_Nested_CG
                                   (Arm.Pat.Sub_Pats.Element (K).all, FT,
                                    FOff, L_Next);
                              end if;
                           end;
                        end loop;
                        if Arm.Guard /= null then
                           Lower_Expr_Into_Reg
                             (F, Arm.Guard, Target_Reg, ST);
                           IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                           & ", " & L_Next);
                        end if;
                        Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                        while Natural (ST.Bindings.Length) > Saved loop
                           ST.Bindings.Delete_Last;
                        end loop;
                        IO.Put_Line (F, "    b       " & L_End);
                        if Need_Next then
                           IO.Put_Line (F, L_Next & ":");
                        end if;
                     end;
                  elsif Natural (Arm.Pat.Path.Length) = 1 then
                     --  §5.10.1 bare-identifier catch-all: alias the whole
                     --  struct value to the name.
                     declare
                        Saved : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        ST.Bindings.Append
                          ((Name   => Arm.Pat.Path.First_Element,
                            Offset => SBase,
                            Ty     => Scrut_T));
                        if Arm.Guard /= null then
                           Lower_Expr_Into_Reg
                             (F, Arm.Guard, Target_Reg, ST);
                           IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                           & ", " & L_Next);
                        end if;
                        Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                        while Natural (ST.Bindings.Length) > Saved loop
                           ST.Bindings.Delete_Last;
                        end loop;
                        IO.Put_Line (F, "    b       " & L_End);
                        if Arm.Guard /= null then
                           IO.Put_Line (F, L_Next & ":");
                        end if;
                     end;
                  else
                     raise Program_Error with
                       "codegen: unsupported pattern kind on struct "
                       & "scrutinee";
                  end if;
               end;
            end loop;
         end;
      elsif Tuple_Binding then
         --  §5.10.1 `.{ ... }` patterns over a tuple binding: positional
         --  bindings alias the scrutinee's slot + field offsets; a
         --  `#`-attached sub-pattern tests in place and falls through to
         --  the next arm on a mismatch.
         for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
            declare
               Arm    : constant Match_Arm := E.M_Arms.Element (I);
               L_Next : constant String :=
                 "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
               Saved  : constant Natural := Natural (ST.Bindings.Length);
               Need_Next : Boolean := Arm.Guard /= null;
            begin
               if Arm.Pat.Kind = Pat_Wild then
                  if SU.Length (Arm.Pat.Wild_Bind) > 0 then
                     Bind_Wild_Repr
                       (Arm.Pat.Wild_Bind, TBase, Sizeof (Scrut_T));
                  end if;
               elsif Arm.Pat.Kind = Pat_Tuple then
                  for K in 1 .. Natural (Arm.Pat.Bindings.Length) loop
                     declare
                        FOff : constant Cell_Count :=
                          TBase
                            + Kurt.Layout.Tuple_Field_Offset
                                (Scrut_T, K - 1);
                        FT   : constant Type_Access :=
                          Kurt.Layout.Tuple_Field_Type (Scrut_T, K - 1);
                     begin
                        if SU.Length (Arm.Pat.Bindings.Element (K)) > 0
                        then
                           ST.Bindings.Append
                             ((Name   => Arm.Pat.Bindings.Element (K),
                               Offset => FOff, Ty => FT));
                        end if;
                        if K <= Natural (Arm.Pat.Sub_Pats.Length)
                          and then Arm.Pat.Sub_Pats.Element (K) /= null
                        then
                           Need_Next := True;
                           Bind_Nested_CG
                             (Arm.Pat.Sub_Pats.Element (K).all, FT, FOff,
                              L_Next);
                        end if;
                     end;
                  end loop;
               elsif Arm.Pat.Kind = Pat_Variant
                 and then Natural (Arm.Pat.Path.Length) = 1
                 and then Arm.Pat.Bindings.Is_Empty
                 and then not Arm.Pat.Has_Rest
               then
                  --  §5.10.1 bare-identifier catch-all: alias the whole
                  --  tuple value to the name.
                  ST.Bindings.Append
                    ((Name   => Arm.Pat.Path.First_Element,
                      Offset => TBase, Ty => Scrut_T));
               else
                  raise Program_Error with
                    "codegen: unsupported pattern kind on tuple scrutinee";
               end if;
               if Arm.Guard /= null then
                  Lower_Expr_Into_Reg (F, Arm.Guard, Target_Reg, ST);
                  IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                  & ", " & L_Next);
               end if;
               Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
               while Natural (ST.Bindings.Length) > Saved loop
                  ST.Bindings.Delete_Last;
               end loop;
               IO.Put_Line (F, "    b       " & L_End);
               if Need_Next then
                  IO.Put_Line (F, L_Next & ":");
               end if;
            end;
         end loop;
      else
         --  Scalar scrutinee (integer, or unit enum value): stash it in a
         --  frame slot (not the stack pointer, so an arm's `b` to the end
         --  needs no fix-up) and compare in a register per arm.
         declare
            Wide   : constant Boolean := Sizeof (Scrut_T) > 4;
            SR     : constant String := (if Wide then "x9" else "w9");
            CR     : constant String := (if Wide then "x10" else "w10");
            Slot   : constant Cell_Count := ST.Next_Offset;
            --  §6.6/§5.10: a `lo..hi` range pattern over an unsigned
            --  scrutinee must fall through on the unsigned (carry-based)
            --  conditions, not the signed (overflow-based) ones.
            Signed : constant Boolean := Is_Signed_Int (Scrut_T);
            C_Lt   : constant String := (if Signed then "lt" else "lo");
            C_Gt   : constant String := (if Signed then "gt" else "hi");
            C_Ge   : constant String := (if Signed then "ge" else "hs");
         begin
            ST.Next_Offset := ST.Next_Offset + 8;
            Lower_Expr_Into_Reg (F, E.M_Scrut, 9, ST);
            IO.Put_Line (F, "    str     " & (if Wide then "x9" else "w9")
                            & ", [x29, #" & Img (Slot) & "]");
            for I in E.M_Arms.First_Index .. E.M_Arms.Last_Index loop
               declare
                  Arm    : constant Match_Arm := E.M_Arms.Element (I);
                  L_Next : constant String :=
                    "Lmarm_" & FN & "_" & Img (Idx) & "_" & Img (I);
                  Val    : Long_Long_Integer := 0;
                  Is_Cmp : Boolean := True;
               begin
                  case Arm.Pat.Kind is
                     when Pat_Wild    => Is_Cmp := False;
                     when Pat_Range   => Is_Cmp := False;
                     when Pat_Slice | Pat_Tuple =>
                        raise Program_Error with
                          "codegen: slice/tuple pattern on scalar scrutinee";
                     when Pat_Int     => Val := Arm.Pat.Int_V;
                     when Pat_Variant =>
                        if Natural (Arm.Pat.Path.Length) = 1 then
                           --  §5.10.1 bare-identifier catch-all binding.
                           Is_Cmp := False;
                        else
                           Val := Kurt.Layout.Variant_Value
                             (SU.To_String (Arm.Pat.Path.First_Element),
                              SU.To_String (Arm.Pat.Path.Last_Element));
                        end if;
                  end case;
                  --  §7.4: a guard or a range test, like an equality test,
                  --  needs a fall-through label to the next arm even on an
                  --  otherwise catch-all arm.
                  declare
                     Is_Range  : constant Boolean :=
                       Arm.Pat.Kind = Pat_Range;
                     Need_Next : constant Boolean :=
                       Is_Cmp or else Is_Range or else Arm.Guard /= null;
                  begin
                     if Is_Range then
                        --  §5.10 `lo..hi` / `lo..=hi`: fall through to the
                        --  next arm unless lo <= scrut (< | <=) hi.
                        IO.Put_Line (F, "    ldr     " & SR
                                        & ", [x29, #" & Img (Slot) & "]");
                        Lower_Imm (F, 10, Arm.Pat.Int_V, Wide);
                        IO.Put_Line (F, "    cmp     " & SR & ", " & CR);
                        IO.Put_Line (F, "    b." & C_Lt & "    " & L_Next);
                        Lower_Imm (F, 10, Arm.Pat.Range_Hi, Wide);
                        IO.Put_Line (F, "    cmp     " & SR & ", " & CR);
                        IO.Put_Line (F, "    b."
                          & (if Arm.Pat.Range_Incl then C_Gt else C_Ge)
                          & "    " & L_Next);
                     elsif Is_Cmp then
                        IO.Put_Line (F, "    ldr     " & SR
                                        & ", [x29, #" & Img (Slot) & "]");
                        Lower_Imm (F, 10, Val, Wide);
                        IO.Put_Line (F, "    cmp     " & SR & ", " & CR);
                        IO.Put_Line (F, "    b.ne    " & L_Next);
                     end if;
                     --  §5.10 binding pattern `name # sub`: alias `name` to
                     --  the scrutinee's frame slot for the guard and body.
                     declare
                        B_Saved : constant Natural :=
                          Natural (ST.Bindings.Length);
                     begin
                        if SU.Length (Arm.Pat.Bind_Name) > 0 then
                           ST.Bindings.Append
                             ((Name   => Arm.Pat.Bind_Name,
                               Offset => Slot,
                               Ty     => Scrut_T));
                        end if;
                        --  §5.10.1 `#wild#(name)`: the stashed scalar's
                        --  cells viewed as `&[ui1]`.
                        if Arm.Pat.Kind = Pat_Wild
                          and then SU.Length (Arm.Pat.Wild_Bind) > 0
                        then
                           Bind_Wild_Repr
                             (Arm.Pat.Wild_Bind, Slot, Sizeof (Scrut_T));
                        end if;
                        --  §5.10.1 bare-identifier catch-all: alias the name
                        --  to the scrutinee's slot for the guard and body.
                        if Arm.Pat.Kind = Pat_Variant
                          and then Natural (Arm.Pat.Path.Length) = 1
                        then
                           ST.Bindings.Append
                             ((Name   => Arm.Pat.Path.First_Element,
                               Offset => Slot,
                               Ty     => Scrut_T));
                        end if;
                        if Arm.Guard /= null then
                           Lower_Expr_Into_Reg (F, Arm.Guard, Target_Reg, ST);
                           IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                           & ", " & L_Next);
                        end if;
                        Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                        while Natural (ST.Bindings.Length) > B_Saved loop
                           ST.Bindings.Delete_Last;
                        end loop;
                     end;
                     IO.Put_Line (F, "    b       " & L_End);
                     if Need_Next then
                        IO.Put_Line (F, L_Next & ":");
                     end if;
                  end;
               end;
            end loop;
         end;
      end if;

      IO.Put_Line (F, L_End & ":");
   end Lower_Match;
