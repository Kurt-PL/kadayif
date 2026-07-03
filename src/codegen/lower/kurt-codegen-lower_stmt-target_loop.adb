separate (Kurt.Codegen.Lower_Stmt)
   function Target_Loop
     (ST : Lower_State; Label : SU.Unbounded_String) return Loop_Labels is
   begin
      if SU.Length (Label) = 0 then
         return ST.Loops.Last_Element;
      end if;
      for I in reverse ST.Loops.First_Index .. ST.Loops.Last_Index loop
         if SU.To_String (ST.Loops.Element (I).Name)
              = SU.To_String (Label)
         then
            return ST.Loops.Element (I);
         end if;
      end loop;
      raise Program_Error with
        "codegen: break/continue to unknown loop label '"
        & SU.To_String (Label) & "'";
   end Target_Loop;
