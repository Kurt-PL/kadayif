separate (Kurt.Lexer)
   function Peek_Line_Directive (L : in out Lexer) return Flag_Dir is
      Save : constant Positive := L.Pos;
   begin
      while Peek (L) = ' ' or else Peek (L) = ASCII.HT loop
         Advance (L);
      end loop;
      if Peek (L) /= '@' then
         L.Pos := Save;
         return FD_None;
      end if;
      Advance (L);   --  '@'
      declare
         Start : constant Positive := L.Pos;
      begin
         while Is_Ident_Continue (Peek (L)) loop
            Advance (L);
         end loop;
         declare
            KW : constant String := SU.Slice (L.Src, Start, L.Pos - 1);
         begin
            if KW = "flag_if" then return FD_If;
            elsif KW = "flag_else_if" then return FD_Else_If;
            elsif KW = "flag_else" then return FD_Else;
            elsif KW = "flag_endif" then return FD_Endif;
            else
               L.Pos := Save;   --  not a chain directive
               return FD_None;
            end if;
         end;
      end;
   end Peek_Line_Directive;
