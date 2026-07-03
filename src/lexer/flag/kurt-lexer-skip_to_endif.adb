separate (Kurt.Lexer)
   procedure Skip_To_Endif (L : in out Lexer; Else_Seen : Boolean) is
      Depth : Natural := 0;
      Seen  : Boolean := Else_Seen;
   begin
      loop
         if At_End (L) then
            raise Translation_Failure with
              "unterminated `@flag_if` (missing `@flag_endif`)";
         end if;
         declare
            D : constant Flag_Dir := Peek_Line_Directive (L);
         begin
            case D is
               when FD_If => Depth := Depth + 1; Skip_Line (L);
               when FD_Endif =>
                  if Depth = 0 then
                     Skip_Line (L);
                     return;
                  end if;
                  Depth := Depth - 1; Skip_Line (L);
               when FD_Else | FD_Else_If =>
                  if Depth = 0 and then Seen then
                     raise Translation_Failure with
                       (if D = FD_Else
                        then "duplicate `@flag_else` in one chain"
                        else "`@flag_else_if` after `@flag_else`")
                       & " (§10.8) at line" & Positive'Image (L.Line);
                  end if;
                  if Depth = 0 and then D = FD_Else then
                     Seen := True;
                  end if;
                  Skip_Line (L);
               when others => Skip_Line (L);
            end case;
         end;
      end loop;
   end Skip_To_Endif;
