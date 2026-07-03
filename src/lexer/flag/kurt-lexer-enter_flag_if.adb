separate (Kurt.Lexer)
   procedure Enter_Flag_If (L : in out Lexer) is
      Cond      : Boolean := Read_Paren_Cond (L);
      Else_Seen : Boolean := False;
      Was_Else  : Boolean := False;   --  the branch about to be entered
   begin
      if Cur_Line_Ends_With_At (L) then    --  §10.8 line-branch chain
         Enter_Line_Chain (L, Cond);
         return;
      end if;
      loop
         if Cond then
            Skip_Line (L);   --  step past the directive line into the body
            --  Record the enclosing-chain context so the main token loop
            --  can validate the chain directives that follow this body.
            SU.Append (L.Chain_Stack, (if Was_Else then 'e' else 'i'));
            return;
         end if;
         declare
            D : constant Flag_Dir := Skip_Inactive_Branch (L);
         begin
            case D is
               when FD_Endif =>
                  Skip_Line (L);
                  return;
               when FD_Else =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "duplicate `@flag_else` in one chain (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Else_Seen := True;
                  Was_Else  := True;
                  Cond := True;
               when FD_Else_If =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "`@flag_else_if` after `@flag_else` (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Was_Else := False;
                  Cond := Read_Paren_Cond (L);
               when others =>
                  return;   --  unreachable
            end case;
         end;
      end loop;
   end Enter_Flag_If;
