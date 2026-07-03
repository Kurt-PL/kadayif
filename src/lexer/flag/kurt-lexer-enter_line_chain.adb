separate (Kurt.Lexer)
   procedure Enter_Line_Chain (L : in out Lexer; First_Cond : Boolean) is
      Cond      : Boolean := First_Cond;
      Else_Seen : Boolean := False;
   begin
      loop
         if Cond then
            L.Line_Close     := Find_Line_Close (L);
            L.Line_Else_Seen := Else_Seen;
            return;
         end if;
         Skip_Line (L);   --  skip this inactive line branch (body + `@` + LF)
         declare
            D : constant Flag_Dir := Peek_Line_Directive (L);
         begin
            case D is
               when FD_None =>
                  return;                  --  chain ended
               when FD_Endif =>
                  --  §10.8: `@flag_endif` shall not appear in an
                  --  all-line-branch chain.
                  raise Translation_Failure with
                    "`@flag_endif` shall not appear in an all-line-branch "
                    & "chain (§10.8) at line" & Positive'Image (L.Line);
               when FD_Else =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "duplicate `@flag_else` in one chain (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Else_Seen := True;
                  if not Cur_Line_Ends_With_At (L) then
                     raise Translation_Failure with
                       "mixed line/block `@flag` chain is not supported in "
                       & "the bootstrap (line `@flag_if` then block "
                       & "`@flag_else`)";
                  end if;
                  Cond := True;
               when FD_Else_If =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "`@flag_else_if` after `@flag_else` (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  declare
                     C2 : constant Boolean := Read_Paren_Cond (L);
                  begin
                     if not Cur_Line_Ends_With_At (L) then
                        raise Translation_Failure with
                          "mixed line/block `@flag` chain is not supported "
                          & "in the bootstrap";
                     end if;
                     Cond := C2;
                  end;
               when FD_If =>
                  return;                  --  a fresh chain; stop here
            end case;
         end;
      end loop;
   end Enter_Line_Chain;
