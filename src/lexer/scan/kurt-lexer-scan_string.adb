separate (Kurt.Lexer)
   function Scan_String (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Bytes      : SU.Unbounded_String;
      T          : Token;
   begin
      Advance (L);  --  consume opening "
      while not At_End (L) loop
         declare
            C : constant Character := Peek (L);
         begin
            if C = '"' then
               Advance (L);
               T.Kind      := Tok_String_Lit;
               T.Str_Bytes := Bytes;
               T.Line      := Start_Line;
               T.Col       := Start_Col;
               return T;
            elsif C = L1.LF then
               raise Translation_Failure
                 with "unescaped line ending in string literal (§3.4.5) at line"
                    & Positive'Image (L.Line);
            elsif C = '\' then
               Advance (L);
               if At_End (L) then
                  raise Translation_Failure
                    with "string ends with unfinished escape sequence";
               end if;
               SU.Append (Bytes, Scan_Escape (L));
            else
               SU.Append (Bytes, C);
               Advance (L);
            end if;
         end;
      end loop;
      raise Translation_Failure
        with "unterminated string literal starting at line"
           & Positive'Image (Start_Line);
   end Scan_String;
