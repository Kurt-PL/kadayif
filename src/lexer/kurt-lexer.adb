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
         elsif S = "never"    then T.Kind := Kw_Never;
         elsif S = "xlatime"  then T.Kind := Kw_Xlatime;
         elsif S = "asm"        then T.Kind := Kw_Asm;
         elsif S = "atomic"     then T.Kind := Kw_Atomic;
         elsif S = "contract"   then T.Kind := Kw_Contract;
         elsif S = "destruct"   then T.Kind := Kw_Destruct;
         elsif S = "guard"      then T.Kind := Kw_Guard;
         elsif S = "integer"    then T.Kind := Kw_Integer;
         elsif S = "module"     then T.Kind := Kw_Module;
         elsif S = "numeric"    then T.Kind := Kw_Numeric;
         elsif S = "primitive"  then T.Kind := Kw_Primitive;
         elsif S = "self"       then T.Kind := Kw_Self;
         elsif S = "selftype"     then T.Kind := Kw_Selftype;
         elsif S = "srcroot"    then T.Kind := Kw_Srcroot;
         elsif S = "static"     then T.Kind := Kw_Static;
         elsif S = "super"      then T.Kind := Kw_Super;
         elsif S = "type"       then T.Kind := Kw_Type;
         elsif S = "undestruct" then T.Kind := Kw_Undestruct;
         elsif S = "use"        then T.Kind := Kw_Use;
         elsif S = "volatile"   then T.Kind := Kw_Volatile;
         elsif S = "xfer"       then T.Kind := Kw_Xfer;
         else                       T.Kind := Tok_Ident;
         end if;

         --  §3.7 `as!` is a single token (maximal munch): the `!` must
         --  follow `as` with no intervening whitespace.
         if T.Kind = Kw_As and then not At_End (L) and then Peek (L) = '!'
         then
            Advance (L);
            T.Kind := Kw_As_Bang;
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

   --  §3.5.2: a floating-point type suffix is one of the six `feEmM`
   --  forms or one of their aliases (f16/bf16/f32/f64/f128/f256).
   function Is_Float_Suffix (S : String) return Boolean is
   begin
      return S = "fe5m10" or else S = "fe8m7" or else S = "fe8m23"
          or else S = "fe11m52" or else S = "fe15m112"
          or else S = "fe19m236"
          or else S = "f16" or else S = "bf16" or else S = "f32"
          or else S = "f64" or else S = "f128" or else S = "f256";
   end Is_Float_Suffix;

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

   ------------------------------------------------------------------
   --  §3.5.7 escape sequence. On entry the cursor is at the escape
   --  selector character (the one after `\`); on return it is just past
   --  the whole escape. Returns the resolved cell value. Shared by the
   --  string- and character-literal scanners.
   ------------------------------------------------------------------

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

   ------------------------------------------------------------------
   --  String literal (§3.5.5, §3.5.7).
   --  Per §3.5.5, an unescaped line ending within a string literal is a
   --  TF. Each character is mapped 1:1 to a cell (the C >= W partition
   --  of §3.5.5, with character width equal to cellbits on this target;
   --  the C < W partitioning is deferred).
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

   ------------------------------------------------------------------
   --  §10.7-8 conditional translation (flags).
   ------------------------------------------------------------------

   function Flag_Set (L : Lexer; Name : String) return Boolean is
     (SU.Index (L.Flags, " " & Name & " ") /= 0);

   procedure Define_Flag (L : in out Lexer; Name : String) is
   begin
      if not Flag_Set (L, Name) then
         SU.Append (L.Flags, Name & " ");
      end if;
   end Define_Flag;

   procedure Unset_Flag (L : in out Lexer; Name : String) is
      Idx : constant Natural := SU.Index (L.Flags, " " & Name & " ");
   begin
      if Idx /= 0 then
         --  Drop "Name " keeping the leading space as the next delimiter.
         SU.Replace_Slice
           (L.Flags, Idx + 1, Idx + Name'Length, "");
      end if;
   end Unset_Flag;

   --  Evaluate a §10.8 flag expression held in S (the text between the
   --  parentheses): identifier | '!' e | e '&&' e | e '||' e | '(' e ')'.
   function Eval_Flag_Expr (L : Lexer; S : String) return Boolean is
      P : Natural := S'First;

      procedure Skip_Ws is
      begin
         while P <= S'Last and then (S (P) = ' ' or else S (P) = ASCII.HT)
         loop
            P := P + 1;
         end loop;
      end Skip_Ws;

      function Parse_Or return Boolean;

      function Parse_Atom return Boolean is
         R : Boolean;
      begin
         Skip_Ws;
         if P <= S'Last and then S (P) = '!' then
            P := P + 1;
            return not Parse_Atom;
         elsif P <= S'Last and then S (P) = '(' then
            P := P + 1;
            R := Parse_Or;
            Skip_Ws;
            if P <= S'Last and then S (P) = ')' then
               P := P + 1;
            end if;
            return R;
         else
            declare
               Start : constant Natural := P;
            begin
               while P <= S'Last
                 and then (Is_Ident_Continue (S (P)))
               loop
                  P := P + 1;
               end loop;
               if P = Start then
                  return False;   --  malformed; treat as false
               end if;
               return Flag_Set (L, S (Start .. P - 1));
            end;
         end if;
      end Parse_Atom;

      function Parse_And return Boolean is
         R : Boolean := Parse_Atom;
      begin
         loop
            Skip_Ws;
            if P + 1 <= S'Last and then S (P) = '&' and then S (P + 1) = '&'
            then
               P := P + 2;
               R := Parse_Atom and then R;   --  evaluate both (no short-circuit side effects)
            else
               exit;
            end if;
         end loop;
         return R;
      end Parse_And;

      function Parse_Or return Boolean is
         R : Boolean := Parse_And;
      begin
         loop
            Skip_Ws;
            if P + 1 <= S'Last and then S (P) = '|' and then S (P + 1) = '|'
            then
               P := P + 2;
               R := Parse_And or else R;
            else
               exit;
            end if;
         end loop;
         return R;
      end Parse_Or;
   begin
      return Parse_Or;
   end Eval_Flag_Expr;

   --  Flag-chain directive kinds recognised at the start of a line.
   type Flag_Dir is (FD_None, FD_If, FD_Else_If, FD_Else, FD_Endif);

   --  Classify the line beginning at L.Pos: if its first non-whitespace
   --  token is a `@flag_*` chain directive, return its kind and leave L.Pos
   --  just after the directive keyword (so a following `(expr)` can be read).
   --  Otherwise return FD_None with L.Pos unchanged.
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

   --  Advance L.Pos past the rest of the current line (including the LF).
   procedure Skip_Line (L : in out Lexer) is
   begin
      while not At_End (L) and then Peek (L) /= ASCII.LF loop
         Advance (L);
      end loop;
      if not At_End (L) then
         Advance (L);   --  consume the LF
      end if;
   end Skip_Line;

   --  Read a `(expr)` at L.Pos and evaluate it; L.Pos ends after the ')'.
   function Read_Paren_Cond (L : in out Lexer) return Boolean is
   begin
      while Peek (L) = ' ' or else Peek (L) = ASCII.HT loop
         Advance (L);
      end loop;
      if Peek (L) /= '(' then
         raise Translation_Failure with
           "`@flag_if`/`@flag_else_if` requires `(expr)` at line"
           & Positive'Image (L.Line);
      end if;
      Advance (L);   --  '('
      declare
         Start : constant Positive := L.Pos;
         Depth : Natural := 1;
      begin
         while not At_End (L) and then Depth > 0 loop
            if Peek (L) = '(' then Depth := Depth + 1;
            elsif Peek (L) = ')' then Depth := Depth - 1;
            end if;
            exit when Depth = 0;
            Advance (L);
         end loop;
         declare
            Expr : constant String := SU.Slice (L.Src, Start, L.Pos - 1);
         begin
            if Peek (L) = ')' then Advance (L); end if;
            return Eval_Flag_Expr (L, Expr);
         end;
      end;
   end Read_Paren_Cond;

   --  Skip a non-taken branch body from L.Pos to the next depth-0 chain
   --  directive (handling nested `@flag_if…@flag_endif`). On return L.Pos is
   --  just after that directive's keyword; the kind is returned.
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

   --  From inside a taken branch that just ended (an `@flag_else`/`else_if`
   --  was reached), skip everything to this chain's matching `@flag_endif`,
   --  consuming that endif line. `Else_Seen` carries whether the chain has
   --  already passed its `@flag_else`, so §10.8's duplicate-else and
   --  else-if-after-else constraints hold across the skipped remainder.
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

   --  Read a `(identifier)` at L.Pos (used by `@flag`/`@unflag`).
   function Read_Paren_Ident (L : in out Lexer) return String is
   begin
      while Peek (L) = ' ' or else Peek (L) = ASCII.HT loop
         Advance (L);
      end loop;
      if Peek (L) /= '(' then
         raise Translation_Failure with
           "`@flag`/`@unflag` requires `(name)` at line"
           & Positive'Image (L.Line);
      end if;
      Advance (L);   --  '('
      while Peek (L) = ' ' or else Peek (L) = ASCII.HT loop
         Advance (L);
      end loop;
      declare
         Start : constant Positive := L.Pos;
      begin
         while Is_Ident_Continue (Peek (L)) loop
            Advance (L);
         end loop;
         declare
            Nm : constant String := SU.Slice (L.Src, Start, L.Pos - 1);
         begin
            while Peek (L) = ' ' or else Peek (L) = ASCII.HT loop
               Advance (L);
            end loop;
            if Peek (L) = ')' then Advance (L); end if;
            return Nm;
         end;
      end;
   end Read_Paren_Ident;

   --  §10.8 line branch: is `@` the final non-whitespace character on the
   --  current line (from L.Pos onward)? That marks a `… @` line branch.
   function Cur_Line_Ends_With_At (L : Lexer) return Boolean is
      P        : Natural := L.Pos;
      Last_NWS : Natural := 0;
      Len      : constant Natural := SU.Length (L.Src);
   begin
      while P <= Len and then SU.Element (L.Src, P) /= ASCII.LF loop
         if SU.Element (L.Src, P) /= ' '
           and then SU.Element (L.Src, P) /= ASCII.HT
         then
            Last_NWS := P;
         end if;
         P := P + 1;
      end loop;
      return Last_NWS /= 0 and then SU.Element (L.Src, Last_NWS) = '@';
   end Cur_Line_Ends_With_At;

   --  Source position of that closing `@` (precondition: the line ends with
   --  one, per Cur_Line_Ends_With_At).
   function Find_Line_Close (L : Lexer) return Positive is
      P        : Natural := L.Pos;
      Last_NWS : Natural := L.Pos;
      Len      : constant Natural := SU.Length (L.Src);
   begin
      while P <= Len and then SU.Element (L.Src, P) /= ASCII.LF loop
         if SU.Element (L.Src, P) /= ' '
           and then SU.Element (L.Src, P) /= ASCII.HT
         then
            Last_NWS := P;
         end if;
         P := P + 1;
      end loop;
      return Last_NWS;
   end Find_Line_Close;

   --  §10.8 an all-line-branch `@flag_if` chain. `First_Cond` is the already
   --  evaluated condition of the first branch; L.Pos sits just after its
   --  `(expr)`. On return either L.Line_Close marks the taken branch's closing
   --  `@` (and L.Pos is at the branch body), or the whole chain was skipped.
   procedure Enter_Line_Chain (L : in out Lexer; First_Cond : Boolean) is
      Cond      : Boolean := First_Cond;
      Else_Seen : Boolean := False;
   begin
      loop
         if Cond then
            L.Line_Close     := Find_Line_Close (L);
            L.Line_Else_Seen := Else_Seen;
            return;
         end if;
         Skip_Line (L);   --  skip this inactive line branch (body + `@` + LF)
         declare
            D : constant Flag_Dir := Peek_Line_Directive (L);
         begin
            case D is
               when FD_None =>
                  return;                  --  chain ended
               when FD_Endif =>
                  --  §10.8: `@flag_endif` shall not appear in an
                  --  all-line-branch chain.
                  raise Translation_Failure with
                    "`@flag_endif` shall not appear in an all-line-branch "
                    & "chain (§10.8) at line" & Positive'Image (L.Line);
               when FD_Else =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "duplicate `@flag_else` in one chain (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Else_Seen := True;
                  if not Cur_Line_Ends_With_At (L) then
                     raise Translation_Failure with
                       "mixed line/block `@flag` chain is not supported in "
                       & "the bootstrap (line `@flag_if` then block "
                       & "`@flag_else`)";
                  end if;
                  Cond := True;
               when FD_Else_If =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "`@flag_else_if` after `@flag_else` (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  declare
                     C2 : constant Boolean := Read_Paren_Cond (L);
                  begin
                     if not Cur_Line_Ends_With_At (L) then
                        raise Translation_Failure with
                          "mixed line/block `@flag` chain is not supported "
                          & "in the bootstrap";
                     end if;
                     Cond := C2;
                  end;
               when FD_If =>
                  return;                  --  a fresh chain; stop here
            end case;
         end;
      end loop;
   end Enter_Line_Chain;

   --  After a taken line branch's body, consume its closing `@` and skip any
   --  remaining (inactive) line branches of the chain.
   procedure Skip_Line_Chain_Rest (L : in out Lexer) is
      Else_Seen : Boolean := L.Line_Else_Seen;
   begin
      if Peek (L) = '@' then Advance (L); end if;
      Skip_Line (L);                       --  to and past the LF
      loop
         declare
            Save : constant Positive := L.Pos;
            D    : constant Flag_Dir := Peek_Line_Directive (L);
         begin
            case D is
               when FD_Else | FD_Else_If =>
                  if Else_Seen then
                     raise Translation_Failure with
                       (if D = FD_Else
                        then "duplicate `@flag_else` in one chain"
                        else "`@flag_else_if` after `@flag_else`")
                       & " (§10.8) at line" & Positive'Image (L.Line);
                  end if;
                  if D = FD_Else then
                     Else_Seen := True;
                  else
                     declare
                        Ig : constant Boolean := Read_Paren_Cond (L);
                        pragma Unreferenced (Ig);
                     begin null; end;
                  end if;
                  if not Cur_Line_Ends_With_At (L) then
                     raise Translation_Failure with
                       "mixed line/block `@flag` chain is not supported "
                       & "in the bootstrap";
                  end if;
                  Skip_Line (L);           --  skip this inactive else branch
               when FD_Endif =>
                  --  §10.8: `@flag_endif` shall not appear in an
                  --  all-line-branch chain.
                  raise Translation_Failure with
                    "`@flag_endif` shall not appear in an all-line-branch "
                    & "chain (§10.8) at line" & Positive'Image (L.Line);
               when others =>
                  L.Pos := Save;           --  chain ended; lex this line
                  return;
            end case;
         end;
      end loop;
   end Skip_Line_Chain_Rest;

   --  Handle a `@flag_if` chain at L.Pos (just after the keyword). On return
   --  L.Pos sits at the start of the taken branch's body, or past the whole
   --  chain if no branch is taken.
   procedure Enter_Flag_If (L : in out Lexer) is
      Cond      : Boolean := Read_Paren_Cond (L);
      Else_Seen : Boolean := False;
      Was_Else  : Boolean := False;   --  the branch about to be entered
   begin
      if Cur_Line_Ends_With_At (L) then    --  §10.8 line-branch chain
         Enter_Line_Chain (L, Cond);
         return;
      end if;
      loop
         if Cond then
            Skip_Line (L);   --  step past the directive line into the body
            --  Record the enclosing-chain context so the main token loop
            --  can validate the chain directives that follow this body.
            SU.Append (L.Chain_Stack, (if Was_Else then 'e' else 'i'));
            return;
         end if;
         declare
            D : constant Flag_Dir := Skip_Inactive_Branch (L);
         begin
            case D is
               when FD_Endif =>
                  Skip_Line (L);
                  return;
               when FD_Else =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "duplicate `@flag_else` in one chain (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Else_Seen := True;
                  Was_Else  := True;
                  Cond := True;
               when FD_Else_If =>
                  if Else_Seen then
                     raise Translation_Failure with
                       "`@flag_else_if` after `@flag_else` (§10.8) at line"
                       & Positive'Image (L.Line);
                  end if;
                  Was_Else := False;
                  Cond := Read_Paren_Cond (L);
               when others =>
                  return;   --  unreachable
            end case;
         end;
      end loop;
   end Enter_Flag_If;

   function Next_Token (L : in out Lexer) return Token is
   begin
      Skip_Trivia (L);

      --  §10.8 the active line branch's body has ended at its closing `@`;
      --  consume it and skip the remaining branches of the chain.
      if L.Line_Close /= 0 and then L.Pos >= L.Line_Close then
         L.Line_Close := 0;
         Skip_Line_Chain_Rest (L);
         return Next_Token (L);
      end if;

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
            declare
               T : Token := Scan_Ident (L);
            begin
               --  §6.11 `asm { … }`: capture the brace body verbatim. `asm`
               --  followed (on the same line) by `{` opens a raw block; any
               --  other `asm` stays the bare keyword (usable only where the
               --  grammar names it, e.g. a top-level asm declaration).
               if T.Kind = Kw_Asm then
                  declare
                     Save_Pos : constant Positive := L.Pos;
                     Save_Col : constant Positive := L.Col;
                  begin
                     while Peek (L) = ' ' or else Peek (L) = L1.HT loop
                        Advance (L);
                     end loop;
                     if Peek (L) = '{' then
                        Advance (L);   --  consume '{'
                        declare
                           Depth : Natural := 1;
                           Buf   : SU.Unbounded_String;
                        begin
                           while not At_End (L) and then Depth > 0 loop
                              if Peek (L) = '{' then
                                 Depth := Depth + 1;
                              elsif Peek (L) = '}' then
                                 Depth := Depth - 1;
                                 exit when Depth = 0;
                              end if;
                              SU.Append (Buf, Peek (L));
                              Advance (L);
                           end loop;
                           if Peek (L) = '}' then
                              Advance (L);
                           end if;
                           T.Kind   := Tok_Asm;
                           T.Lexeme := Buf;
                        end;
                     else
                        L.Pos := Save_Pos;   --  not an asm block
                        L.Col := Save_Col;
                     end if;
                  end;
               end if;
               return T;
            end;
         elsif CH.Is_Digit (C) then
            return Scan_Int (L);
         elsif C = '"' then
            return Scan_String (L);
         elsif C = ''' then
            --  §7.9 / §6.11: disambiguate a label / asm positional operand
            --  (`'name`, `'0`) from a character literal `'c'`. It is a label
            --  when an identifier or digit follows the quote and is not closed
            --  by another quote (a char literal always is).
            if Is_Ident_Start (Peek (L, 1))
              or else Peek (L, 1) in '0' .. '9'
            then
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
               if Peek (L, 1) = '.' and then Peek (L, 2) = '.' then
                  Tok.Kind := Op_Ellipsis;        --  ...  (§7.4.2)
                  Advance (L); Advance (L); Advance (L);
               elsif Peek (L, 1) = '.' and then Peek (L, 2) = '=' then
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
               if Peek (L, 1) = '/' then
                  --  §3.6: `*/` outside a block comment is a translation
                  --  failure (Skip_Trivia consumes well-formed comments
                  --  before tokenization, so a `*/` reaching here is stray).
                  raise Translation_Failure
                    with "'*/' outside a block comment (§3.6) at line"
                       & Positive'Image (L.Line);
               elsif Peek (L, 1) = '|' and then Peek (L, 2) = '=' then
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
                  --  §5.10 standalone `#` (binding pattern `name # sub`).
                  Tok.Kind := Tok_Hash;
                  Advance (L);
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
                  elsif S = "add" then
                     Tok.Kind   := Dir_At_Add;       --  §10.2
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "path" then
                     Tok.Kind   := Dir_At_Path;      --  §10.5
                     Tok.Lexeme := Name_Tok.Lexeme;
                  elsif S = "trap" then
                     Tok.Kind   := Dir_At_Trap;      --  §7.10
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
                  elsif S = "name" then
                     Tok.Kind   := Dir_At_Name;      --  §6.12.2
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
                  elsif S = "flag" then               --  §10.7
                     Define_Flag (L, Read_Paren_Ident (L));
                     return Next_Token (L);
                  elsif S = "unflag" then             --  §10.7
                     Unset_Flag (L, Read_Paren_Ident (L));
                     return Next_Token (L);
                  elsif S = "flag_if" then            --  §10.8
                     Enter_Flag_If (L);
                     return Next_Token (L);
                  elsif S = "flag_endif" then
                     --  Active branch reached its chain end. §10.8: the
                     --  directive must close an enclosing block chain.
                     if SU.Length (L.Chain_Stack) = 0 then
                        raise Translation_Failure with
                          "unmatched `@flag_endif` without a preceding "
                          & "`@flag_if` (§10.8) at line"
                          & Positive'Image (Tok.Line);
                     end if;
                     SU.Head (L.Chain_Stack, SU.Length (L.Chain_Stack) - 1);
                     Skip_Line (L);
                     return Next_Token (L);
                  elsif S = "flag_else" or else S = "flag_else_if" then
                     --  Active branch ended; the rest of the chain is
                     --  skipped. §10.8: reject an unmatched directive, and a
                     --  duplicate `@flag_else` (or `@flag_else_if` after
                     --  `@flag_else`) when the taken branch WAS the else.
                     if SU.Length (L.Chain_Stack) = 0 then
                        raise Translation_Failure with
                          "unmatched `@" & S & "` without a preceding "
                          & "`@flag_if` (§10.8) at line"
                          & Positive'Image (Tok.Line);
                     end if;
                     declare
                        Top : constant Character :=
                          SU.Element (L.Chain_Stack,
                                      SU.Length (L.Chain_Stack));
                     begin
                        if Top = 'e' then
                           raise Translation_Failure with
                             (if S = "flag_else"
                              then "duplicate `@flag_else` in one chain"
                              else "`@flag_else_if` after `@flag_else`")
                             & " (§10.8) at line"
                             & Positive'Image (Tok.Line);
                        end if;
                        SU.Head (L.Chain_Stack,
                                 SU.Length (L.Chain_Stack) - 1);
                        Skip_To_Endif (L, Else_Seen => S = "flag_else");
                     end;
                     return Next_Token (L);
                  else
                     raise Translation_Failure
                       with "unknown @-directive '@" & S
                          & "' at line" & Positive'Image (Tok.Line)
                          & " (bootstrap supports @dyn/@trap/@guard/@volatile"
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
