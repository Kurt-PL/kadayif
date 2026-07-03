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
      Base         : Natural := 0;
      EN           : SU.Unbounded_String;
      --  §7.4.2 a `[T;N]` array binding matched by slice patterns in place.
      Array_Binding : Boolean := False;
      Arr_Base      : Natural := 0;
   begin
      ST.If_Idx := ST.If_Idx + 1;

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
            Disc_Size : constant Natural :=
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
                        if Arm.Guard /= null then
                           Lower_Expr_Into_Reg (F, Arm.Guard, Target_Reg, ST);
                           IO.Put_Line (F, "    cbz     w" & Img (Target_Reg)
                                           & ", " & L_Next);
                        end if;
                        Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                        IO.Put_Line (F, "    b       " & L_End);
                        if Arm.Guard /= null then
                           IO.Put_Line (F, L_Next & ":");
                        end if;
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
                           --  Bind payload fields as slot+offset aliases.
                           for K in 1 .. Natural (Arm.Pat.Bindings.Length)
                           loop
                              ST.Bindings.Append
                                ((Name   => Arm.Pat.Bindings.Element (K),
                                  Offset => Base
                                    + Pat_Field_Off (Arm.Pat, Scrut_T, VN, K),
                                  Ty     => Pat_Field_Ty
                                              (Arm.Pat, Scrut_T, VN, K)));
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
                     when Pat_Int | Pat_Range | Pat_Slice =>
                        raise Program_Error with
                          "codegen: numeric/slice pattern on enum scrutinee";
                  end case;
               end;
            end loop;
         end;
      elsif Array_Binding then
         --  §7.4.2 slice patterns over a `[T;N]` binding. N is static, so the
         --  length test is resolved at compile time; element positions are
         --  fixed offsets (front before `...`, back after).
         declare
            N     : constant Natural := Scrut_T.Len;
            ESize : constant Natural := Sizeof (Scrut_T.Elem);
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
                     Lower_Expr_Into_Reg (F, Arm.Arm_Body, Target_Reg, ST);
                     IO.Put_Line (F, "    b       " & L_End);
                  elsif Arm.Pat.Kind = Pat_Slice then
                     declare
                        SE       : Slice_Elem_Vectors.Vector renames
                          Arm.Pat.Slice_Elems;
                        Rest_At  : Integer := -1;
                        K        : Natural := 0;   --  non-rest element count
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
                              Front   : Natural := 0;  --  index before rest
                              Back    : Natural := 0;  --  count after rest
                              Has_Cmp : Boolean := False;

                              --  Element J's array index, given its position.
                              function Arr_Idx (Pos : Natural; After : Boolean;
                                                Back_Pos : Natural)
                                return Natural is
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
                                    AIdx : Natural;
                                 begin
                                    if El.Kind = SE_Rest then
                                       Seen_Rest := True;
                                    else
                                       if Seen_Rest then
                                          AIdx := Arr_Idx (0, True,
                                            (J - Rest_At) - 1);
                                       else
                                          AIdx := Front;
                                          Front := Front + 1;
                                       end if;
                                       declare
                                          Off : constant Natural :=
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
      else
         --  Scalar scrutinee (integer, or unit enum value): stash it in a
         --  frame slot (not the stack pointer, so an arm's `b` to the end
         --  needs no fix-up) and compare in a register per arm.
         declare
            Wide  : constant Boolean := Sizeof (Scrut_T) > 4;
            SR    : constant String := (if Wide then "x9" else "w9");
            CR    : constant String := (if Wide then "x10" else "w10");
            Slot  : constant Natural := ST.Next_Offset;
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
                     when Pat_Slice   =>
                        raise Program_Error with
                          "codegen: slice pattern on scalar scrutinee";
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
                        IO.Put_Line (F, "    b.lt    " & L_Next);
                        Lower_Imm (F, 10, Arm.Pat.Range_Hi, Wide);
                        IO.Put_Line (F, "    cmp     " & SR & ", " & CR);
                        IO.Put_Line (F, "    b."
                          & (if Arm.Pat.Range_Incl then "gt" else "ge")
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
