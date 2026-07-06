separate (Kurt.Sema.Check)
   procedure Check_Loop_Label (Label : SU.Unbounded_String) is
   begin
      if SU.Length (Label) = 0 then
         return;
      end if;
      --  §7.9 innermost-first: an inner label shadows an outer one of
      --  the same name, so the nearest match decides.
      for I in reverse Label_Stack.First_Index .. Label_Stack.Last_Index loop
         if SU.To_String (Label_Stack.Element (I).Name)
              = SU.To_String (Label)
         then
            if Label_Stack.Element (I).Is_Block then
               Error ("`break`/`continue` names ''" & SU.To_String (Label)
                      & "' which labels a block; `break`/`continue` shall "
                      & "name a labelled loop (spec 7.9)");
            end if;
            return;
         end if;
      end loop;
      Error ("`break`/`continue` names loop label ''" & SU.To_String (Label)
             & "' which is not in scope (spec 7.9)");
   end Check_Loop_Label;
