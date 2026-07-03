separate (Kurt.Lexer)
   procedure Skip_Line_Chain_Rest (L : in out Lexer) is
      Else_Seen : Boolean := L.Line_Else_Seen;
   begin
      if Peek (L) = '@' then Advance (L); end if;
      Skip_Line (L);                       --  to and past the LF
      loop
         declare
            Save : constant Positive := L.Pos;
            D    : constant Flag_Dir := Peek_Line_Directive (L);
         begin
            case D is
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
                     begin null; end;
                  end if;
                  if not Cur_Line_Ends_With_At (L) then
                     raise Translation_Failure with
                       "mixed line/block `@flag` chain is not supported "
                       & "in the bootstrap";
                  end if;
                  Skip_Line (L);           --  skip this inactive else branch
               when FD_Endif =>
                  --  §10.8: `@flag_endif` shall not appear in an
                  --  all-line-branch chain.
                  raise Translation_Failure with
                    "`@flag_endif` shall not appear in an all-line-branch "
                    & "chain (§10.8) at line" & Positive'Image (L.Line);
               when others =>
                  L.Pos := Save;           --  chain ended; lex this line
                  return;
            end case;
         end;
      end loop;
   end Skip_Line_Chain_Rest;
