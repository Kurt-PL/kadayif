separate (Kurt.Codegen)
   procedure Note_Move
     (F : IO.File_Type; ST : in out Lower_State; E : Expr_Access) is
   begin
      if E /= null and then E.Kind = E_Path
        and then Natural (E.Segments.Length) = 1
        and then E.P_Is_Move
      then
         declare
            Idx : constant Natural :=
              Find_Binding (ST, SU.To_String (E.Segments.Last_Element));
         begin
            if Idx /= 0 then
               declare
                  FOff : constant Integer :=
                    Flag_Off_Of (ST, ST.Bindings.Element (Idx).Offset);
               begin
                  if FOff >= 0 then
                     IO.Put_Line (F, "    strb    wzr, [x29, #"
                                     & Img (FOff) & "]");
                  end if;
               end;
            end if;
         end;
      end if;
   end Note_Move;
