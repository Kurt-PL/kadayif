separate (Kurt.Lexer)
   procedure Enter_Flag_If (L : in out Lexer) is
      Cond      : Boolean := Read_Paren_Cond (L);
      Else_Seen : Boolean := False;
      Was_Else  : Boolean := False;   --  the branch about to be entered
   begin
      if Cur_Line_Ends_With_At (L) then    --  §10.8 line-form first branch
         Enter_Line_Chain (L, Cond);
         return;
      end if;
      --  §10.8: a block-branch directive shall not share its line with
      --  any other source element.
      if Line_Has_More_Tokens (L) then
         raise Translation_Failure with
           "a block-form `@flag_if` directive shall not share its line "
           & "with other source text (§10.8) at line"
           & Positive'Image (L.Line);
      end if;
      --  The first branch is block-form; the chain requires a closing
      --  `@flag_endif`. Subsequent branches are each independently line-
      --  or block-form (§10.8 mixed chains).
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
            --  §10.8 mixed chain: this else/else-if branch may itself be
            --  line-form (`@flag_else body @`).
            if Line_Has_More_Tokens (L) then
               if not Cur_Line_Ends_With_At (L) then
                  raise Translation_Failure with
                    "a line-form `@flag` branch shall end with a lone `@` "
                    & "(§10.8) at line" & Positive'Image (L.Line);
               end if;
               if Cond then
                  --  Taken line-form branch of a chain that contains a
                  --  block branch: the body ends at the closing `@`, and
                  --  the chain's `@flag_endif` remains required
                  --  (Line_Has_Block).
                  L.Line_Close     := Find_Line_Close (L);
                  L.Line_Else_Seen := Else_Seen;
                  L.Line_Has_Block := True;
                  return;
               end if;
               Skip_Line (L);   --  inactive line-form branch: this line
            end if;
            --  Block-form branch: the loop top takes it (Cond) or the
            --  next Skip_Inactive_Branch scans past its body.
         end;
      end loop;
   end Enter_Flag_If;
