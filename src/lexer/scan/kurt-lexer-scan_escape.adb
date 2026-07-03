separate (Kurt.Lexer)
   function Scan_Escape (L : in out Lexer) return Character is
      Sel : constant Character := Peek (L);
   begin
      Advance (L);  --  consume the selector
      case Sel is
         when '0'  => return Character'Val (0);
         when 'a'  => return Character'Val (7);
         when 'b'  => return Character'Val (8);
         when 't'  => return L1.HT;
         when 'n'  => return L1.LF;
         when 'v'  => return Character'Val (11);
         when 'f'  => return Character'Val (12);
         when 'r'  => return L1.CR;
         when '\'  => return '\';
         when '''  => return ''';
         when '"'  => return '"';
         when 'x'  =>
            --  §3.5.7: exactly ceil(cellbits::exec / 4) hex digits; the
            --  value is a ui1 cell value and shall not exceed
            --  2**cellbits::exec - 1. Both the digit count and the bound
            --  derive from the single cellbits source in Kurt.
            declare
               V : Natural := 0;
            begin
               for I in 1 .. Kurt.Hex_Escape_Digits loop
                  declare
                     D : constant Integer := Digit_Value (Peek (L));
                  begin
                     if D not in 0 .. 15 then
                        raise Translation_Failure
                          with "\x requires exactly"
                             & Integer'Image (Kurt.Hex_Escape_Digits)
                             & " hexadecimal digits (§3.5.7) at line"
                             & Positive'Image (L.Line);
                     end if;
                     V := V * 16 + D;
                  end;
                  Advance (L);
               end loop;
               if V > 2 ** Kurt.Cell_Bits_Exec - 1 then
                  raise Translation_Failure
                    with "\x escape value exceeds 2**cellbits - 1 "
                       & "(§3.5.7) at line" & Positive'Image (L.Line);
               end if;
               return Character'Val (V);
            end;
         when others =>
            raise Translation_Failure
              with "unrecognised escape \" & Sel
                 & " (§3.5.7) at line" & Positive'Image (L.Line);
      end case;
   end Scan_Escape;
