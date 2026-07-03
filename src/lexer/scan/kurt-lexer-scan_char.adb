separate (Kurt.Lexer)
   function Scan_Char (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      T          : Token;
      V          : Character;
   begin
      Advance (L);  --  consume opening '
      if At_End (L) then
         raise Translation_Failure
           with "unterminated character literal at line"
              & Positive'Image (Start_Line);
      end if;
      declare
         C : constant Character := Peek (L);
      begin
         if C = ''' then
            raise Translation_Failure
              with "empty character literal (§3.5.4) at line"
                 & Positive'Image (Start_Line);
         elsif C = L1.LF then
            raise Translation_Failure
              with "line ending in character literal (§3.5.4) at line"
                 & Positive'Image (Start_Line);
         elsif C = '\' then
            Advance (L);
            if At_End (L) then
               raise Translation_Failure
                 with "character literal ends with unfinished escape";
            end if;
            V := Scan_Escape (L);
         else
            V := C;
            Advance (L);
         end if;
      end;
      if At_End (L) or else Peek (L) /= ''' then
         raise Translation_Failure
           with "character literal shall contain exactly one character "
              & "(§3.5.4) at line" & Positive'Image (Start_Line);
      end if;
      Advance (L);  --  consume closing '
      T.Kind  := Tok_Char_Lit;
      T.Int_V := Long_Long_Integer (Character'Pos (V));
      T.Line  := Start_Line;
      T.Col   := Start_Col;
      return T;
   end Scan_Char;
