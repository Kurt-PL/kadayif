separate (Kurt.Lexer)
   function Skip_Inactive_Branch (L : in out Lexer) return Flag_Dir is
      Depth : Natural := 0;
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
               when FD_If =>
                  Depth := Depth + 1;
                  Skip_Line (L);
               when FD_Endif =>
                  if Depth = 0 then
                     return FD_Endif;
                  end if;
                  Depth := Depth - 1;
                  Skip_Line (L);
               when FD_Else | FD_Else_If =>
                  if Depth = 0 then
                     return D;
                  end if;
                  Skip_Line (L);   --  belongs to a nested chain
               when FD_None =>
                  Skip_Line (L);
            end case;
         end;
      end loop;
   end Skip_Inactive_Branch;
