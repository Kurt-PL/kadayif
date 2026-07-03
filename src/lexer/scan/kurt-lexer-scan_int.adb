separate (Kurt.Lexer)
   function Scan_Int (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Buf        : SU.Unbounded_String;
      V          : Long_Long_Integer := 0;
      Base       : Long_Long_Integer := 10;
      T          : Token;
   begin
      --  §3.5.2 special floating-point literal `0nan` / `0inf`, with an
      --  optional float suffix fused on (bare — no separator). `0nan` is a
      --  NaN with sign bit 0 and all-zero payload (the quiet-NaN pattern);
      --  `0inf` is positive infinity. Negative forms are unary negation.
      if Peek (L) = '0'
        and then ((Peek (L, 1) = 'n' and then Peek (L, 2) = 'a'
                     and then Peek (L, 3) = 'n')
                  or else (Peek (L, 1) = 'i' and then Peek (L, 2) = 'n'
                             and then Peek (L, 3) = 'f'))
      then
         declare
            Is_Nan : constant Boolean := Peek (L, 1) = 'n';
            Suf    : SU.Unbounded_String;
         begin
            Advance (L); Advance (L); Advance (L); Advance (L);
            while Is_Ident_Continue (Peek (L)) loop
               SU.Append (Suf, Peek (L));
               Advance (L);
            end loop;
            if SU.Length (Suf) > 0
              and then not Is_Float_Suffix (SU.To_String (Suf))
            then
               raise Translation_Failure with
                 "invalid float suffix '" & SU.To_String (Suf)
                 & "' (§3.5.2) at line" & Positive'Image (Start_Line);
            end if;
            T.Kind          := Tok_Float_Lit;
            T.Float_Special := (if Is_Nan then 1 else 2);
            T.Int_Suffix    := Suf;
            T.Line          := Start_Line;
            T.Col           := Start_Col;
            return T;
         end;
      end if;

      --  Radix prefix.
      if Peek (L) = '0'
        and then (Peek (L, 1) = 'x' or else Peek (L, 1) = 'o'
                  or else Peek (L, 1) = 'b' or else Peek (L, 1) = 'q')
      then
         case Peek (L, 1) is
            when 'x' => Base := 16;
            when 'o' => Base := 8;
            when 'b' => Base := 2;
            when 'q' => Base := 4;
            when others => null;
         end case;
         SU.Append (Buf, Peek (L));      --  '0'
         SU.Append (Buf, Peek (L, 1));   --  radix letter
         Advance (L); Advance (L);
      end if;

      --  Digits with optional `_` separators. §3.5.8: a separator shall
      --  appear only between two digits — never leading, trailing,
      --  adjacent to the radix prefix / suffix, or doubled.
      declare
         Seen_Digit : Boolean := False;
      begin
         loop
            exit when At_End (L);
            declare
               C : constant Character := Peek (L);
            begin
               if C = '_' then
                  declare
                     ND : constant Integer := Digit_Value (Peek (L, 1));
                  begin
                     if not Seen_Digit
                       or else ND < 0
                       or else Long_Long_Integer (ND) >= Base
                     then
                        raise Translation_Failure with
                          "misplaced digit separator '_' (§3.5.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                  end;
                  Advance (L);
               else
                  declare
                     D : constant Integer := Digit_Value (C);
                  begin
                     exit when D < 0 or else Long_Long_Integer (D) >= Base;
                     --  §3.5.1 reject an out-of-range literal with a clean
                     --  diagnostic instead of an internal overflow.
                     if V > (Long_Long_Integer'Last - Long_Long_Integer (D))
                              / Base
                     then
                        raise Translation_Failure with
                          "integer literal is too large to represent (§3.5.1)"
                          & " at line" & Positive'Image (L.Line);
                     end if;
                     V := V * Base + Long_Long_Integer (D);
                     SU.Append (Buf, C);
                     Seen_Digit := True;
                     Advance (L);
                  end;
               end if;
            end;
         end loop;
      end;

      --  §3.4.2 floating-point literal: a base-10 literal becomes a float
      --  when a fractional part (`.`digit) or an exponent (`e`/`E`) follows.
      if Base = 10 then
         declare
            Is_Float : Boolean := False;
         begin
            --  Fractional part: `.` then at least one digit.
            if not At_End (L) and then Peek (L) = '.'
              and then Digit_Value (Peek (L, 1)) in 0 .. 9
            then
               Is_Float := True;
               SU.Append (Buf, '.');
               Advance (L);
               while not At_End (L) loop
                  if Peek (L) = '_' then
                     --  §3.5.8: only between two digits.
                     if Digit_Value (Peek (L, 1)) not in 0 .. 9 then
                        raise Translation_Failure with
                          "misplaced digit separator '_' (§3.5.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Advance (L);
                  elsif Digit_Value (Peek (L)) in 0 .. 9 then
                     SU.Append (Buf, Peek (L));
                     Advance (L);
                  else
                     exit;
                  end if;
               end loop;
            end if;
            --  Exponent part: `e`/`E` then optional sign then digit(s).
            if not At_End (L) and then (Peek (L) = 'e' or else Peek (L) = 'E')
              and then (Digit_Value (Peek (L, 1)) in 0 .. 9
                        or else ((Peek (L, 1) = '+' or else Peek (L, 1) = '-')
                                 and then Digit_Value (Peek (L, 2)) in 0 .. 9))
            then
               Is_Float := True;
               if SU.Index (Buf, ".") = 0 then
                  SU.Append (Buf, ".0");   --  Ada 'Value needs a point
               end if;
               SU.Append (Buf, 'E');
               Advance (L);
               if Peek (L) = '+' or else Peek (L) = '-' then
                  SU.Append (Buf, Peek (L));
                  Advance (L);
               end if;
               while not At_End (L) loop
                  if Peek (L) = '_' then
                     --  §3.5.8: only between two digits.
                     if Digit_Value (Peek (L, 1)) not in 0 .. 9 then
                        raise Translation_Failure with
                          "misplaced digit separator '_' (§3.5.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Advance (L);
                  elsif Digit_Value (Peek (L)) in 0 .. 9 then
                     SU.Append (Buf, Peek (L));
                     Advance (L);
                  else
                     exit;
                  end if;
               end loop;
            end if;

            if Is_Float then
               --  Optional float type suffix (fe.../f16/bf16/f32/...).
               if not At_End (L)
                 and then (Peek (L) = 'f' or else Peek (L) = 'b')
               then
                  declare
                     Suf : SU.Unbounded_String;
                  begin
                     while not At_End (L)
                       and then Is_Ident_Continue (Peek (L))
                     loop
                        SU.Append (Suf, Peek (L));
                        Advance (L);
                     end loop;
                     if Is_Float_Suffix (SU.To_String (Suf)) then
                        T.Int_Suffix := Suf;
                     else
                        raise Translation_Failure
                          with "invalid floating-point suffix '"
                             & SU.To_String (Suf) & "' (§3.5.2) at line"
                             & Positive'Image (Start_Line);
                     end if;
                  end;
               end if;
               T.Kind    := Tok_Float_Lit;
               T.Lexeme  := Buf;
               T.Float_V := Long_Float'Value (SU.To_String (Buf));
               T.Line    := Start_Line;
               T.Col     := Start_Col;
               return T;
            end if;
         end;
      end if;

      --  §3.5.2 hexadecimal floating-point literal: `0x` hex digits with a
      --  fractional part (`.` hex digits) and/or a binary exponent
      --  (`p`/`P` decimal). Without either it stays an integer (the `fe...`
      --  of a would-be suffix are hex digits, per §3.5.2).
      if Base = 16 then
         declare
            Is_Float : Boolean := False;
            Mant     : Long_Float := Long_Float (V);   --  integer part
            Frac_W   : Long_Float := 1.0 / 16.0;       --  next frac weight
            Exp      : Integer := 0;
            Exp_Neg  : Boolean := False;
         begin
            --  Fractional part: `.` then at least one hex digit.
            if not At_End (L) and then Peek (L) = '.'
              and then Digit_Value (Peek (L, 1)) in 0 .. 15
            then
               Is_Float := True;
               Advance (L);   --  consume '.'
               loop
                  exit when At_End (L);
                  if Peek (L) = '_' then
                     if Digit_Value (Peek (L, 1)) not in 0 .. 15 then
                        raise Translation_Failure with
                          "misplaced digit separator '_' (§3.5.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Advance (L);
                  elsif Digit_Value (Peek (L)) in 0 .. 15 then
                     Mant := Mant
                       + Long_Float (Digit_Value (Peek (L))) * Frac_W;
                     Frac_W := Frac_W / 16.0;
                     Advance (L);
                  else
                     exit;
                  end if;
               end loop;
            end if;
            --  Binary exponent: `p`/`P` then optional sign then decimal.
            if not At_End (L)
              and then (Peek (L) = 'p' or else Peek (L) = 'P')
              and then (Digit_Value (Peek (L, 1)) in 0 .. 9
                        or else ((Peek (L, 1) = '+' or else Peek (L, 1) = '-')
                                 and then Digit_Value (Peek (L, 2)) in 0 .. 9))
            then
               Is_Float := True;
               Advance (L);   --  consume 'p'/'P'
               if Peek (L) = '+' or else Peek (L) = '-' then
                  Exp_Neg := Peek (L) = '-';
                  Advance (L);
               end if;
               loop
                  exit when At_End (L);
                  if Peek (L) = '_' then
                     if Digit_Value (Peek (L, 1)) not in 0 .. 9 then
                        raise Translation_Failure with
                          "misplaced digit separator '_' (§3.5.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Advance (L);
                  elsif Digit_Value (Peek (L)) in 0 .. 9 then
                     Exp := Exp * 10 + Digit_Value (Peek (L));
                     Advance (L);
                  else
                     exit;
                  end if;
               end loop;
               if Exp_Neg then
                  Exp := -Exp;
               end if;
            end if;

            if Is_Float then
               --  §3.5.2: value = significand × 2**(binary exponent).
               if not At_End (L)
                 and then (Peek (L) = 'f' or else Peek (L) = 'b')
               then
                  declare
                     Suf : SU.Unbounded_String;
                  begin
                     while not At_End (L)
                       and then Is_Ident_Continue (Peek (L))
                     loop
                        SU.Append (Suf, Peek (L));
                        Advance (L);
                     end loop;
                     if Is_Float_Suffix (SU.To_String (Suf)) then
                        T.Int_Suffix := Suf;
                     else
                        raise Translation_Failure
                          with "invalid floating-point suffix '"
                             & SU.To_String (Suf) & "' (§3.5.2) at line"
                             & Positive'Image (Start_Line);
                     end if;
                  end;
               end if;
               T.Kind    := Tok_Float_Lit;
               T.Lexeme  := Buf;
               T.Float_V := Mant * (2.0 ** Exp);
               T.Line    := Start_Line;
               T.Col     := Start_Col;
               return T;
            end if;
         end;
      end if;

      --  Optional integer type suffix (begins with 'u' or 's').
      if not At_End (L)
        and then (Peek (L) = 'u' or else Peek (L) = 's')
      then
         declare
            Suf : SU.Unbounded_String;
         begin
            while not At_End (L) and then Is_Ident_Continue (Peek (L)) loop
               SU.Append (Suf, Peek (L));
               Advance (L);
            end loop;
            if Is_Int_Suffix (SU.To_String (Suf)) then
               T.Int_Suffix := Suf;
            else
               raise Translation_Failure
                 with "invalid integer suffix '" & SU.To_String (Suf)
                    & "' at line" & Positive'Image (Start_Line);
            end if;
         end;
      end if;

      T.Kind   := Tok_Int_Lit;
      T.Lexeme := Buf;
      T.Int_V  := V;
      T.Line   := Start_Line;
      T.Col    := Start_Col;
      return T;
   end Scan_Int;
