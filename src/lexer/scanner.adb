with Ada.Strings.Unbounded;
with Diagnostics;

package body Scanner is

   use Tokens;

   function Is_Digit (C : Character) return Boolean is (C in '0' .. '9');

   function Is_Space (C : Character) return Boolean is
     (C in ' ' | ASCII.HT | ASCII.LF | ASCII.CR | ASCII.VT | ASCII.FF);

   function Run (S : Strip.Stripped) return Token_Vectors.Vector is
      Text   : String renames S.Text.all;
      Result : Token_Vectors.Vector;
      I      : Positive := Text'First;

      function At_I return Source_Map.Source_Pos is
        (Strip.Position (S, I));

      function Peek (K : Natural) return Character is
        (if I + K <= Text'Last then Text (I + K) else ASCII.NUL);

      procedure Push (Kind : Token_Kind; Last : Natural;
                      Raw : Boolean := False) is
      begin
         Result.Append (Token'(Kind, I, Last, Raw));
         I := Last + 1;
      end Push;

      function After_Dot return Boolean is
        (not Result.Is_Empty and then Result.Last_Element.Kind = P_Dot);

      --  J에서 digit { ['_'] digit } 를 읽고 다음 인덱스를 돌려준다.
      --  J에 숫자가 없으면 J 그대로.
      generic
         with function Valid (C : Character) return Boolean;
      function Scan_Digits (J : Positive) return Positive;

      function Scan_Digits (J : Positive) return Positive is
         K : Positive := J;
      begin
         if K > Text'Last or else not Valid (Text (K)) then
            return J;
         end if;
         K := K + 1;
         loop
            if K <= Text'Last and then Valid (Text (K)) then
               K := K + 1;
            elsif K < Text'Last and then Text (K) = '_'
              and then Valid (Text (K + 1))
            then
               K := K + 2;
            else
               return K;
            end if;
         end loop;
      end Scan_Digits;

      function Is_Bin (C : Character) return Boolean is (C in '0' | '1');
      function Is_Qat (C : Character) return Boolean is (C in '0' .. '3');
      function Is_Oct (C : Character) return Boolean is (C in '0' .. '7');

      function Dec_Digits is new Scan_Digits (Is_Digit);
      function Bin_Digits is new Scan_Digits (Is_Bin);
      function Qat_Digits is new Scan_Digits (Is_Qat);
      function Oct_Digits is new Scan_Digits (Is_Oct);
      function Hex_Digits is new Scan_Digits (Strip.Is_Hex);

      --  J의 지수부(e/E 또는 p/P, 부호, 숫자)를 읽는다. 없으면 J.
      function Exponent (J : Positive; Marks : String) return Positive is
         K : Positive := J;
      begin
         if K > Text'Last
           or else (Text (K) /= Marks (Marks'First)
                    and then Text (K) /= Marks (Marks'Last))
         then
            return J;
         end if;
         K := K + 1;
         if K <= Text'Last and then Text (K) in '+' | '-' then
            K := K + 1;
         end if;
         declare
            After : constant Positive := Dec_Digits (K);
         begin
            return (if After = K then J else After);
         end;
      end Exponent;

      --  radix 접두사가 붙은 정수 리터럴 하나(잔여값에도 쓰임).
      --  성립하지 않으면 J.
      function Radix_Int (J : Positive) return Positive is
      begin
         if J + 1 <= Text'Last and then Text (J) = '0' then
            case Text (J + 1) is
               when 'b' | 'B' =>
                  if Bin_Digits (J + 2) > J + 2 then
                     return Bin_Digits (J + 2);
                  end if;
               when 'q' | 'Q' =>
                  if Qat_Digits (J + 2) > J + 2 then
                     return Qat_Digits (J + 2);
                  end if;
               when 'o' | 'O' =>
                  if Oct_Digits (J + 2) > J + 2 then
                     return Oct_Digits (J + 2);
                  end if;
               when 'x' | 'X' =>
                  if Hex_Digits (J + 2) > J + 2 then
                     return Hex_Digits (J + 2);
                  end if;
               when others =>
                  null;
            end case;
         end if;
         return Dec_Digits (J);
      end Radix_Int;

      procedure Scan_Number is
         J : Positive;
      begin
         --  특수 리터럴 (§3.5.2)
         if I + 4 <= Text'Last and then Text (I .. I + 3) = "0nan"
           and then Text (I + 4) in 'q' | 's'
         then
            J := I + 5;
            if J <= Text'Last and then Text (J) = '''
              and then J < Text'Last and then Is_Digit (Text (J + 1))
            then
               J := Radix_Int (J + 1);
            end if;
            Push (T_Float, J - 1);
            return;
         elsif I + 3 <= Text'Last and then Text (I .. I + 3) = "0inf" then
            Push (T_Float, I + 3);
            return;
         end if;

         --  16진: 0x
         if Peek (1) in 'x' | 'X' and then Text (I) = '0'
           and then Strip.Is_Hex (Peek (2))
         then
            J := Hex_Digits (I + 2);
            if not After_Dot and then J < Text'Last and then Text (J) = '.'
              and then Strip.Is_Hex (Text (J + 1))
            then
               J := Exponent (Hex_Digits (J + 1), "pP");
               Push (T_Float, J - 1);
            elsif Exponent (J, "pP") > J then
               Push (T_Float, Exponent (J, "pP") - 1);
            else
               Push (T_Int, J - 1);
            end if;
            return;
         end if;

         J := Radix_Int (I);
         if J > Dec_Digits (I) then
            --  0b, 0q, 0o 리터럴
            Push (T_Int, J - 1);
            return;
         end if;

         --  10진
         if not After_Dot and then J < Text'Last and then Text (J) = '.'
           and then Is_Digit (Text (J + 1))
         then
            J := Exponent (Dec_Digits (J + 1), "eE");
            Push (T_Float, J - 1);
         elsif Exponent (J, "eE") > J then
            Push (T_Float, Exponent (J, "eE") - 1);
         else
            Push (T_Int, J - 1);
         end if;
      end Scan_Number;

      procedure Scan_Punct is
         Best      : Token_Kind := T_EOF;
         Best_Len  : Natural := 0;
      begin
         for K in Punct_Kind loop
            declare
               Sp : constant String := Spelling (K);
            begin
               if Sp'Length > Best_Len
                 and then I + Sp'Length - 1 <= Text'Last
                 and then Text (I .. I + Sp'Length - 1) = Sp
               then
                  Best := K;
                  Best_Len := Sp'Length;
               end if;
            end;
         end loop;
         if Best = T_EOF then
            Diagnostics.Error
              (At_I, "character not permitted here: '"
               & Text (I .. I + Strip.Char_Length (Text (I)) - 1) & "'");
            I := I + Strip.Char_Length (Text (I));
         else
            Push (Best, I + Best_Len - 1);
         end if;
      end Scan_Punct;

      procedure Scan_Hash is
         J : Positive := I + 1;
      begin
         if Peek (1) = '[' then
            --  annotation: #[ … ]#  (§4.17)
            J := I + 2;
            while J < Text'Last
              and then not (Text (J) = ']' and then Text (J + 1) = '#')
            loop
               J := J + 1;
            end loop;
            if J >= Text'Last then
               Diagnostics.Error (At_I, "unterminated annotation");
               I := Text'Last + 1;
            else
               Push (T_Annotation, J + 1);
            end if;
            return;
         end if;
         while J <= Text'Last and then Strip.Is_Ident_Char (Text (J)) loop
            J := J + 1;
         end loop;
         declare
            Kind : constant Token_Kind := Directive (Text (I + 1 .. J - 1));
         begin
            if Kind = T_EOF then
               Diagnostics.Error
                 (At_I, "unknown directive '" & Text (I .. J - 1) & "'");
               I := J;
            else
               Push (Kind, J - 1);
            end if;
         end;
      end Scan_Hash;

      procedure Scan_Ident is
         J : Positive := I;
      begin
         while J <= Text'Last and then Strip.Is_Ident_Char (Text (J)) loop
            J := J + 1;
         end loop;
         Push (Keyword (Text (I .. J - 1)), J - 1);
      end Scan_Ident;

      function Is_Raw_Opening return Boolean is
         J : Positive := I + 1;
      begin
         while J <= Text'Last and then Text (J) = '#' loop
            J := J + 1;
         end loop;
         return J <= Text'Last and then Text (J) = '"';
      end Is_Raw_Opening;

      procedure Scan_Delimited (Kind : Token_Kind) is
         J      : Positive := I;
         Hashes : Natural := 0;
      begin
         if Kind = T_Raw_String then
            J := J + 1;
            while Text (J) = '#' loop
               Hashes := Hashes + 1;
               J := J + 1;
            end loop;
         end if;
         J := J + 1;
         loop
            if J > Text'Last then
               --  strip 단계가 이미 진단했다
               I := Text'Last + 1;
               return;
            elsif Kind = T_String and then Text (J) = '\' then
               J := J + 2;
            elsif Text (J) = '"'
              and then J + Hashes <= Text'Last
              and then Text (J + 1 .. J + Hashes) = [1 .. Hashes => '#']
            then
               Push (Kind, J + Hashes);
               return;
            else
               J := J + 1;
            end if;
         end loop;
      end Scan_Delimited;

   begin
      while I <= Text'Last loop
         declare
            C : constant Character := Text (I);
         begin
            if Is_Space (C) then
               I := I + 1;
            elsif C = '"' then
               Scan_Delimited (T_String);
            elsif C = 'r' and then Is_Raw_Opening then
               Scan_Delimited (T_Raw_String);
            elsif C = ''' and then Strip.Char_Literal_End (Text, I) > 0 then
               Push (T_Char, Strip.Char_Literal_End (Text, I));
            elsif C = 'i' and then Peek (1) = '#'
              and then Strip.Is_Ident_Start (Peek (2))
            then
               declare
                  J : Positive := I + 2;
               begin
                  while J <= Text'Last
                    and then Strip.Is_Ident_Char (Text (J))
                  loop
                     J := J + 1;
                  end loop;
                  Push (T_Ident, J - 1, Raw => True);
               end;
            elsif Strip.Is_Ident_Start (C) then
               Scan_Ident;
            elsif Is_Digit (C) then
               Scan_Number;
            elsif C = '#' then
               Scan_Hash;
            else
               Scan_Punct;
            end if;
         end;
      end loop;
      Result.Append (Token'(T_EOF, Text'Last + 1, Text'Last, False));
      return Result;
   end Run;

   function Literal_Content (S : Strip.Stripped; T : Tokens.Token)
                             return String
   is
      use Ada.Strings.Unbounded;
      Text  : String renames S.Text.all;
      Out_S : Unbounded_String;
      First : Positive := T.First + 1;
      Last  : Natural := T.Last - 1;
      J     : Positive;
   begin
      if T.Kind = T_Raw_String then
         First := T.First + 1;
         while Text (First) = '#' loop
            First := First + 1;
         end loop;
         First := First + 1;
         Last := T.Last - (First - T.First - 1);
         return Text (First .. Last);
      end if;

      J := First;
      while J <= Last loop
         if Text (J) = '\' then
            case Text (J + 1) is
               when '0' => Append (Out_S, ASCII.NUL);
               when 'a' => Append (Out_S, ASCII.BEL);
               when 'b' => Append (Out_S, ASCII.BS);
               when 't' => Append (Out_S, ASCII.HT);
               when 'n' => Append (Out_S, ASCII.LF);
               when 'v' => Append (Out_S, ASCII.VT);
               when 'f' => Append (Out_S, ASCII.FF);
               when 'r' => Append (Out_S, ASCII.CR);
               when '\' | ''' | '"' => Append (Out_S, Text (J + 1));
               when 'x' =>
                  if J + 1 + Strip.Hex_Escape_Digits <= Last
                    and then (for all D in 1 .. Strip.Hex_Escape_Digits =>
                                Strip.Is_Hex (Text (J + 1 + D)))
                  then
                     Append
                       (Out_S,
                        Character'Val
                          (Integer'Value
                             ("16#" & Text (J + 2 .. J + 1
                                + Strip.Hex_Escape_Digits) & "#")));
                     J := J + Strip.Hex_Escape_Digits;
                  else
                     Diagnostics.Error
                       (Strip.Position (S, J),
                        "'\x' escape needs"
                        & Strip.Hex_Escape_Digits'Image
                        & " hexadecimal digits");
                  end if;
               when others =>
                  Diagnostics.Error
                    (Strip.Position (S, J), "unknown escape sequence");
            end case;
            J := J + 2;
         else
            Append (Out_S, Text (J));
            J := J + 1;
         end if;
      end loop;
      return To_String (Out_S);
   end Literal_Content;

end Scanner;
