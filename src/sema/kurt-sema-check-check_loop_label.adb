separate (Kurt.Sema.Check)
   procedure Check_Loop_Label (Label : SU.Unbounded_String) is
   begin
      if SU.Length (Label) = 0 then
         return;
      end if;
      for I in Label_Stack.First_Index .. Label_Stack.Last_Index loop
         if SU.To_String (Label_Stack.Element (I))
              = SU.To_String (Label)
         then
            return;
         end if;
      end loop;
      Error ("`break`/`continue` names loop label ''" & SU.To_String (Label)
             & "' which is not in scope (spec 7.9)");
   end Check_Loop_Label;
