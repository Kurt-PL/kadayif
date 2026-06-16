with Ada.Characters.Handling;
with Ada.Characters.Latin_1;

package body Kurt.Lexer is

   package CH renames Ada.Characters.Handling;
   package L1 renames Ada.Characters.Latin_1;

   ------------------------------------------------------------------
   --  Internal helpers
   ------------------------------------------------------------------

   function At_End (L : Lexer) return Boolean is
      (L.Pos > SU.Length (L.Src));

   function Peek (L : Lexer; Ahead : Natural := 0) return Character is
   begin
      if L.Pos + Ahead > SU.Length (L.Src) then
         return L1.NUL;
      end if;
      return SU.Element (L.Src, L.Pos + Ahead);
   end Peek;

   procedure Advance (L : in out Lexer) is
      C : Character;
   begin
      if At_End (L) then
         return;
      end if;
      C := SU.Element (L.Src, L.Pos);
      L.Pos := L.Pos + 1;
      if C = L1.LF then
         L.Line := L.Line + 1;
         L.Col  := 1;
      else
         L.Col  := L.Col + 1;
      end if;
   end Advance;

   function Is_Ident_Start (C : Character) return Boolean is
     (CH.Is_Letter (C) or else C = '_');

   function Is_Ident_Continue (C : Character) return Boolean is
     (CH.Is_Alphanumeric (C) or else C = '_');

   ------------------------------------------------------------------
   --  Trivia: whitespace and §3.5 comments.
   ------------------------------------------------------------------

   procedure Skip_Trivia (L : in out Lexer) is
   begin
      while not At_End (L) loop
         declare
            C : constant Character := Peek (L);
         begin
            if C = ' ' or else C = L1.HT or else C = L1.LF
              or else C = L1.CR or else C = L1.VT or else C = L1.FF
            then
               Advance (L);
            elsif C = '/' and then Peek (L, 1) = '/' then
               while not At_End (L) and then Peek (L) /= L1.LF loop
                  Advance (L);
               end loop;
            elsif C = '/' and then Peek (L, 1) = '*' then
               declare
                  Depth : Natural := 1;
               begin
                  Advance (L);
                  Advance (L);
                  loop
                     if At_End (L) then
                        raise Translation_Failure
                          with "unterminated block comment (§3.5)";
                     end if;
                     if Peek (L) = '/' and then Peek (L, 1) = '*' then
                        Advance (L); Advance (L);
                        Depth := Depth + 1;
                     elsif Peek (L) = '*' and then Peek (L, 1) = '/' then
                        Advance (L); Advance (L);
                        Depth := Depth - 1;
                        exit when Depth = 0;
                     else
                        Advance (L);
                     end if;
                  end loop;
               end;
            else
               exit;
            end if;
         end;
      end loop;
   end Skip_Trivia;

   ------------------------------------------------------------------
   --  Identifier / keyword (§3.3).
   ------------------------------------------------------------------

   function Scan_Ident (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Buf        : SU.Unbounded_String;
      T          : Token;
   begin
      while not At_End (L) and then Is_Ident_Continue (Peek (L)) loop
         SU.Append (Buf, Peek (L));
         Advance (L);
      end loop;

      T.Lexeme := Buf;
      T.Line   := Start_Line;
      T.Col    := Start_Col;

      declare
         S : constant String := SU.To_String (Buf);
      begin
         if    S = "fn"       then T.Kind := Kw_Fn;
         elsif S = "return"   then T.Kind := Kw_Return;
         elsif S = "as"       then T.Kind := Kw_As;
         elsif S = "pub"      then T.Kind := Kw_Pub;
         elsif S = "extern"   then T.Kind := Kw_Extern;
         elsif S = "variadic" then T.Kind := Kw_Variadic;
         elsif S = "airside"  then T.Kind := Kw_Airside;
         elsif S = "let"      then T.Kind := Kw_Let;
         elsif S = "mut"      then T.Kind := Kw_Mut;
         elsif S = "if"       then T.Kind := Kw_If;
         elsif S = "then"     then T.Kind := Kw_Then;
         elsif S = "else"     then T.Kind := Kw_Else;
         elsif S = "while"    then T.Kind := Kw_While;
         elsif S = "loop"     then T.Kind := Kw_Loop;
         elsif S = "break"    then T.Kind := Kw_Break;
         elsif S = "continue" then T.Kind := Kw_Continue;
         elsif S = "express"  then T.Kind := Kw_Express;
         elsif S = "uninit"   then T.Kind := Kw_Uninit;
         elsif S = "struct"   then T.Kind := Kw_Struct;
         elsif S = "enum"     then T.Kind := Kw_Enum;
         elsif S = "match"    then T.Kind := Kw_Match;
         elsif S = "impl"     then T.Kind := Kw_Impl;
         elsif S = "trait"    then T.Kind := Kw_Trait;
         elsif S = "dyn"      then T.Kind := Kw_Dyn;
         elsif S = "const"    then T.Kind := Kw_Const;
         elsif S = "with"     then T.Kind := Kw_With;
         elsif S = "true"     then T.Kind := Kw_True;
         elsif S = "false"    then T.Kind := Kw_False;
         elsif S = "cellbits" then T.Kind := Kw_Cellbits;
         else                       T.Kind := Tok_Ident;
         end if;
      end;
      return T;
   end Scan_Ident;

   ------------------------------------------------------------------
   --  Integer literal (§3.4.1): decimal / 0x / 0o / 0b / 0q, optional
   --  `_` digit separators (§3.4.8), optional integer type suffix.
   --  Floating-point literals are not yet handled.
   ------------------------------------------------------------------

   function Digit_Value (C : Character) return Integer is
   begin
      case C is
         when '0' .. '9' => return Character'Pos (C) - Character'Pos ('0');
         when 'a' .. 'f' => return Character'Pos (C) - Character'Pos ('a') + 10;
         when 'A' .. 'F' => return Character'Pos (C) - Character'Pos ('A') + 10;
         when others     => return -1;
      end case;
   end Digit_Value;

   function Is_Int_Suffix (S : String) return Boolean is
   begin
      return S = "ui1" or else S = "ui2" or else S = "ui4"
          or else S = "ui8" or else S = "ui16" or else S = "ui32"
          or else S = "si1" or else S = "si2" or else S = "si4"
          or else S = "si8" or else S = "si16" or else S = "si32"
          or else S = "uaddr" or else S = "saddr";
   end Is_Int_Suffix;

   function Scan_Int (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Buf        : SU.Unbounded_String;
      V          : Long_Long_Integer := 0;
      Base       : Long_Long_Integer := 10;
      T          : Token;
   begin
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
               --  Optional float type suffix (fe…/f16/bf16/f32/…).
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
                     T.Int_Suffix := Suf;
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

   ------------------------------------------------------------------
   --  String literal (§3.4.5, §3.4.7).
   --  Bootstrap escapes: \0 \n \t \r \\ \"
   --  Per §3.4.5, an unescaped newline within a string literal is a TF.
   --  Each character is mapped 1:1 to a cell (CELL_BITS=8 assumed for the
   --  host target; the broader mapping rule in §3.4.5 is deferred).
   ------------------------------------------------------------------

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
               case Peek (L) is
                  when '0'  => SU.Append (Bytes, Character'Val (0));
                  when 'a'  => SU.Append (Bytes, Character'Val (7));
                  when 'b'  => SU.Append (Bytes, Character'Val (8));
                  when 't'  => SU.Append (Bytes, L1.HT);
                  when 'n'  => SU.Append (Bytes, L1.LF);
                  when 'v'  => SU.Append (Bytes, Character'Val (11));
                  when 'f'  => SU.Append (Bytes, Character'Val (12));
                  when 'r'  => SU.Append (Bytes, L1.CR);
                  when '\'  => SU.Append (Bytes, '\');
                  when '''  => SU.Append (Bytes, ''');
                  when '"'  => SU.Append (Bytes, '"');
                  when 'x'  =>
                     --  §3.5.7: `\xHH` — exactly ceil(cellbits/4) = 2
                     --  hex digits on this target. Consume 'x' and the
                     --  first digit here; the shared Advance below
                     --  consumes the second.
                     Advance (L);
                     declare
                        H1 : constant Integer := Digit_Value (Peek (L));
                        H2 : constant Integer := Digit_Value (Peek (L, 1));
                     begin
                        if H1 not in 0 .. 15 or else H2 not in 0 .. 15 then
                           raise Translation_Failure
                             with "\x requires exactly 2 hexadecimal "
                                & "digits (§3.5.7) at line"
                                & Positive'Image (L.Line);
                        end if;
                        SU.Append (Bytes, Character'Val (16 * H1 + H2));
                     end;
                     Advance (L);
                  when others =>
                     raise Translation_Failure
                       with "unrecognised escape \" & Peek (L)
                          & " (§3.5.7) at line"
                          & Positive'Image (L.Line);
               end case;
               Advance (L);
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

   ------------------------------------------------------------------
   --  Character literal (§3.5.4): exactly one source character or one
   --  escape sequence between single quotes; the value is one cell
   --  (type ui1). Escapes mirror the string-literal set plus \'.
   ------------------------------------------------------------------

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
            case Peek (L) is
               when '0'  => V := Character'Val (0);
               when 'a'  => V := Character'Val (7);
               when 'b'  => V := Character'Val (8);
               when 't'  => V := L1.HT;
               when 'n'  => V := L1.LF;
               when 'v'  => V := Character'Val (11);
               when 'f'  => V := Character'Val (12);
               when 'r'  => V := L1.CR;
               when '\'  => V := '\';
               when '''  => V := ''';
               when '"'  => V := '"';
               when 'x'  =>
                  --  §3.5.7: `\xHH`. Consume 'x' and the first digit
                  --  here; the shared Advance below takes the second.
                  Advance (L);
                  declare
                     H1 : constant Integer := Digit_Value (Peek (L));
                     H2 : constant Integer := Digit_Value (Peek (L, 1));
                  begin
                     if H1 not in 0 .. 15 or else H2 not in 0 .. 15 then
                        raise Translation_Failure
                          with "\x requires exactly 2 hexadecimal "
                             & "digits (§3.5.7) at line"
                             & Positive'Image (L.Line);
                     end if;
                     V := Character'Val (16 * H1 + H2);
                  end;
                  Advance (L);
               when others =>
                  raise Translation_Failure
                    with "unrecognised escape \" & Peek (L)
                       & " (§3.5.7) at line" & Positive'Image (L.Line);
            end case;
            Advance (L);
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

   ------------------------------------------------------------------
   --  Public API
   ------------------------------------------------------------------

   procedure Init (L : out Lexer; Source : String) is
   begin
      L.Src  := SU.To_Unbounded_String (Source);
      L.Pos  := 1;
      L.Line := 1;
      L.Col  := 1;
   end Init;

   function Next_Token (L : in out Lexer) return Token is
   begin
      Skip_Trivia (L);

      if At_End (L) then
         return (Kind => Tok_EOF, Line => L.Line, Col => L.Col, others => <>);
      end if;

      declare
         C   : constant Character := Peek (L);
         Tok : Token;
      begin
         Tok.Line := L.Line;
         Tok.Col  := L.Col;

         if Is_Ident_Start (C) then
            --  §3.5.6 raw string literal (e.g. r"..." or r#..."#)
            if C = 'r' then
               declare
                  Idx : Natural := 1;
                  Is_Raw_String : Boolean := False;
               begin
                  if Peek (L, 1) = '"' then
                     Is_Raw_String := True;
                  elsif Peek (L, 1) = '#' then
                     while Peek (L, Idx) = '#' loop
                        Idx := Idx + 1;
                     end loop;
                     if Peek (L, Idx) = '"' then
                        Is_Raw_String := True;
                     end if;
                  end if;

                  if Is_Raw_String then
                     return Scan_Raw_String (L);
                  end if;
               end;
            end if;

            --  §3.4.2 raw identifier `i#foo`: a single token denoting
            --  the identifier `foo`, bypassing keyword classification.
            if C = 'i' and then Peek (L, 1) = '#'
              and then Is_Ident_Start (Peek (L, 2))
            then
               Advance (L);   --  'i'
               Advance (L);   --  '#'
               declare
                  T : Token := Scan_Ident (L);
               begin
                  T.Kind := Tok_Ident;
                  return T;
               end;
            end if;
            return Scan_Ident (L);
         elsif CH.Is_Digit (C) then
            return Scan_Int (L);
         elsif C = '"' then
            return Scan_String (L);
         elsif C = ''' then
            --  §7.9: disambiguate a label `'name` from a character literal
            --  `'c'`. It is a label when an identifier follows the quote and
            --  is not closed by another quote (a char literal always is).
            if Is_Ident_Start (Peek (L, 1)) then
               declare
                  K : Positive := 2;
               begin
                  while Is_Ident_Continue (Peek (L, K)) loop
                     K := K + 1;
                  end loop;
                  if Peek (L, K) /= ''' then
                     Advance (L);                  --  consume the quote
                     declare
                        T : Token := Scan_Ident (L);
                     begin
                        T.Kind := Tok_Label;       --  name retained in Lexeme
                        return T;
                     end;
                  end if;
               end;
            end if;
            return Scan_Char (L);
         end if;

         case C is
            when '(' => Tok.Kind := Punct_LParen; Advance (L);
            when ')' => Tok.Kind := Punct_RParen; Advance (L);
            when '{' => Tok.Kind := Punct_LBrace; Advance (L);
            when '}' => Tok.Kind := Punct_RBrace; Advance (L);
            when '[' => Tok.Kind := Punct_LBracket; Advance (L);
            when ']' =>
               if Peek (L, 1) = '@' then           --  §5.16 annotation close
                  Tok.Kind := Dir_At_RBracket;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Punct_RBracket; Advance (L);
               end if;
            when ';' => Tok.Kind := Punct_Semi;   Advance (L);
            when ',' => Tok.Kind := Punct_Comma;  Advance (L);
            when '.' =>
               if Peek (L, 1) = '.' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_DotDotEq;        --  ..=  (§4.8)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '.' then
                  Tok.Kind := Op_DotDot;          --  ..   (§4.8)
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Punct_Dot; Advance (L);
               end if;
            when '&' =>
               if Peek (L, 1) = '&' then
                  Tok.Kind := Op_AmpAmp; Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_AmpEq; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Amp; Advance (L);
               end if;
            when '$' => Tok.Kind := Op_Dollar;    Advance (L);
            when '*' =>
               if Peek (L, 1) = '|' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_StarBarEq;       --  *|=  (§3.6, §6.7.2)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_StarEq; Advance (L); Advance (L);
               elsif Peek (L, 1) = '|' then
                  Tok.Kind := Op_StarBar; Advance (L); Advance (L);
               elsif Peek (L, 1) = '@' then
                  Tok.Kind := Op_StarAt; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Star; Advance (L);
               end if;
            when '/' =>
               if Peek (L, 1) = '|' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_SlashBarEq;      --  /|=  (§3.6, §6.7.2)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_SlashEq; Advance (L); Advance (L);
               elsif Peek (L, 1) = '|' then
                  Tok.Kind := Op_SlashBar; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Slash; Advance (L);
               end if;
            when '%' =>
               if Peek (L, 1) = '=' then
                  Tok.Kind := Op_PercentEq; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Percent; Advance (L);
               end if;
            when '|' =>
               if Peek (L, 1) = '|' then
                  Tok.Kind := Op_BarBar; Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_BarEq; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Bar; Advance (L);
               end if;
            when '^' =>
               if Peek (L, 1) = '=' then
                  Tok.Kind := Op_CaretEq; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Caret; Advance (L);
               end if;
            when '?' => Tok.Kind := Op_Question;  Advance (L);
            when '+' =>
               if Peek (L, 1) = '|' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_PlusBarEq;       --  +|=  (§3.6, §6.7.2)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_PlusEq; Advance (L); Advance (L);
               elsif Peek (L, 1) = '|' then
                  Tok.Kind := Op_PlusBar; Advance (L); Advance (L);
               elsif Peek (L, 1) = '@' then
                  Tok.Kind := Op_PlusAt; Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Plus; Advance (L);
               end if;
            when ':' =>
               if Peek (L, 1) = ':' then
                  Tok.Kind := Punct_ColonColon;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Punct_Colon;
                  Advance (L);
               end if;
            when '=' =>
               if Peek (L, 1) = '=' then
                  Tok.Kind := Op_EqEq;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Punct_Eq;
                  Advance (L);
               end if;
            when '!' =>
               if Peek (L, 1) = '=' then
                  Tok.Kind := Op_BangEq;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Bang;      --  bitwise NOT / polarity
                  Advance (L);
               end if;
            when '<' =>
               if Peek (L, 1) = '=' then
                  Tok.Kind := Op_Le;
                  Advance (L); Advance (L);
               elsif Peek (L, 1) = '-' then
                  Tok.Kind := Punct_LArrow;
                  Advance (L); Advance (L);
               elsif Peek (L, 1) = '<' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_ShlEq;
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '<' then
                  Tok.Kind := Op_Shl;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Lt;
                  Advance (L);
               end if;
            when '>' =>
               if Peek (L, 1) = '.' and then Peek (L, 2) = '<' then
                  Tok.Kind := Op_EqCas;            --  >.<  (§8.7)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '!' and then Peek (L, 2) = '<' then
                  Tok.Kind := Op_NeCas;            --  >!<  (§8.7)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_Ge;
                  Advance (L); Advance (L);
               elsif Peek (L, 1) = '>' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_ShrEq;
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '>' then
                  Tok.Kind := Op_Shr;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Gt;
                  Advance (L);
               end if;
            when '-' =>
               if Peek (L, 1) = '>' then
                  Tok.Kind := Punct_Arrow;
                  Advance (L); Advance (L);
               elsif Peek (L, 1) = '|' and then Peek (L, 2) = '=' then
                  Tok.Kind := Op_MinusBarEq;      --  -|=  (§3.6, §6.7.2)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
                  Tok.Kind := Op_MinusEq;
                  Advance (L); Advance (L);
               elsif Peek (L, 1) = '|' then
                  Tok.Kind := Op_MinusBar;
                  Advance (L); Advance (L);
               else
                  Tok.Kind := Op_Minus;
                  Advance (L);
               end if;
            when '#' =>
               --  §3.6: `#wild#` is a single indivisible token.
               if Peek (L, 1) = 'w' and then Peek (L, 2) = 'i'
                 and then Peek (L, 3) = 'l' and then Peek (L, 4) = 'd'
                 and then Peek (L, 5) = '#'
               then
                  Tok.Kind := Tok_Hash_Wild;
                  for K in 1 .. 6 loop
                     Advance (L);
                  end loop;
               else
                  raise Translation_Failure
                    with "unexpected '#' at line"
                       & Positive'Image (L.Line)
                       & " (only '#wild#' is recognised by the bootstrap)";
               end if;
            when '@' =>
               Advance (L);
               --  §5.16 annotation open `@[`.
               if Peek (L) = '[' then
                  Advance (L);
                  Tok.Kind := Dir_At_LBracket;
                  return Tok;
               end if;
               if not Is_Ident_Start (Peek (L)) then
                  raise Translation_Failure
                    with "expected identifier after '@' at line"
                       & Positive'Image (Tok.Line);
               end if;
               declare
                  Name_Tok : constant Token  := Scan_Ident (L);
                  S        : constant String := SU.To_String (Name_Tok.Lexeme);
               begin
                  if S = "dyn" then
                     Tok.Kind   := Dir_At_Dyn;
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "guard" then
                     Tok.Kind   := Dir_At_Guard;     --  §8.5.3
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "volatile" then
                     Tok.Kind   := Dir_At_Volatile;  --  §8.5.3
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "size" then
                     Tok.Kind   := Dir_At_Size;      --  §6.12
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "align" then
                     Tok.Kind   := Dir_At_Align;     --  §6.12
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "offset" then
                     Tok.Kind   := Dir_At_Offset;    --  §6.12
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "inline" then
                     Tok.Kind   := Dir_At_Inline;    --  §5.14
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "no_inline" then
                     Tok.Kind   := Dir_At_No_Inline; --  §5.14
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "symbol" then
                     Tok.Kind   := Dir_At_Symbol;    --  §5.15
                     Tok.Lexeme := Name_Tok.Lexeme;
                  else
                     raise Translation_Failure
                       with "unknown @-directive '@" & S
                          & "' at line" & Positive'Image (Tok.Line)
                          & " (bootstrap supports @dyn/@guard/@volatile"
                          & "/@size/@align/@offset/@inline/@no_inline"
                          & "/@symbol)";
                  end if;
               end;
            when others =>
               raise Translation_Failure
                 with "unexpected character '" & C
                    & "' at line"  & Positive'Image (L.Line)
                    & ", col"      & Positive'Image (L.Col);
         end case;

         return Tok;
      end;
   end Next_Token;

end Kurt.Lexer;
