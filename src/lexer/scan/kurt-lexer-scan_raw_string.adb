separate (Kurt.Lexer)
   function Scan_Raw_String (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Bytes      : SU.Unbounded_String;
      Hash_Count : Natural := 0;
   begin
      Advance (L); -- consume 'r'
      while Peek (L) = '#' loop
         Hash_Count := Hash_Count + 1;
         Advance (L);
      end loop;
      Advance (L); -- consume opening '"'

      while not At_End (L) loop
         declare
            C : constant Character := Peek (L);
         begin
            if C = '"' then
               declare
                  Match : Boolean := True;
               begin
                  for I in 1 .. Hash_Count loop
                     if Peek (L, I) /= '#' then
                        Match := False;
                        exit;
                     end if;
                  end loop;
                  if Match then
                     Advance (L); -- consume '"'
                     for I in 1 .. Hash_Count loop
                        Advance (L); -- consume '#'
                     end loop;
                     declare
                        T : Token;
                     begin
                        T.Kind      := Tok_String_Lit;
                        T.Str_Bytes := Bytes;
                        T.Line      := Start_Line;
                        T.Col       := Start_Col;
                        return T;
                     end;
                  end if;
               end;
            end if;
            SU.Append (Bytes, C);
            Advance (L);
         end;
      end loop;
      raise Translation_Failure
        with "unterminated raw string literal starting at line"
           & Positive'Image (Start_Line);
   end Scan_Raw_String;
