separate (Kurt.Lexer)
   procedure Skip_Line_Chain_Rest (L : in out Lexer) is
      Else_Seen : Boolean := L.Line_Else_Seen;
      Has_Block : Boolean := L.Line_Has_Block;
   begin
      L.Line_Has_Block := False;
      if Peek (L) = '@' then Advance (L); end if;
      Skip_Line (L);                       --  to and past the LF
      Outer : loop
         declare
            Save : constant Positive := L.Pos;
            D    : Flag_Dir := Peek_Line_Directive (L);
         begin
            Inner : loop
               case D is
                  when FD_None | FD_If =>
                     --  Chain ended; §10.8: a chain containing a block
                     --  branch requires the `@flag_endif` terminator.
                     if Has_Block then
                        raise Translation_Failure with
                          "missing `@flag_endif`: a `@flag` chain "
                          & "containing a block branch requires one "
                          & "(§10.8) at line" & Positive'Image (L.Line);
                     end if;
                     L.Pos := Save;        --  lex this line normally
                     return;
                  when FD_Endif =>
                     --  §10.8: `@flag_endif` shall not appear in an
                     --  all-line-branch chain, and is required otherwise.
                     if not Has_Block then
                        raise Translation_Failure with
                          "`@flag_endif` shall not appear in an "
                          & "all-line-branch chain (§10.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Skip_Line (L);
                     return;
                  when FD_Else | FD_Else_If =>
                     if Else_Seen then
                        raise Translation_Failure with
                          (if D = FD_Else
                           then "duplicate `@flag_else` in one chain"
                           else "`@flag_else_if` after `@flag_else`")
                          & " (§10.8) at line" & Positive'Image (L.Line);
                     end if;
                     if D = FD_Else then
                        Else_Seen := True;
                     else
                        declare
                           Ig : constant Boolean := Read_Paren_Cond (L);
                           pragma Unreferenced (Ig);
                        begin
                           null;
                        end;
                     end if;
                     if Line_Has_More_Tokens (L) then
                        --  §10.8 inactive line-form branch: this line.
                        if not Cur_Line_Ends_With_At (L) then
                           raise Translation_Failure with
                             "a line-form `@flag` branch shall end with a "
                             & "lone `@` (§10.8) at line"
                             & Positive'Image (L.Line);
                        end if;
                        Skip_Line (L);
                        exit Inner;        --  re-peek the next line
                     end if;
                     --  §10.8 mixed chain: an inactive block-form branch;
                     --  scan past its body to the chain's next directive.
                     Has_Block := True;
                     D := Skip_Inactive_Branch (L);
               end case;
            end loop Inner;
         end;
      end loop Outer;
   end Skip_Line_Chain_Rest;
