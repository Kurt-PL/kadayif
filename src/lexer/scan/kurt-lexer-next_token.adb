separate (Kurt.Lexer)
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

         --  §3.4: an identifier-start character here may be a plain ASCII
         --  byte or the lead byte of a multi-byte UTF-8 letter (Unicode
         --  Kurt supports non-ASCII identifiers; §3.1 malformed sequences
         --  are rejected by Ident_Start_Len itself).
         if Ident_Start_Len (L) > 0 then
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
            --  `foo` follows the same §3.4 identifier-start rule as any
            --  other identifier, so a Unicode letter is admissible here
            --  too (e.g. `i#변수`).
            if C = 'i' and then Peek (L, 1) = '#'
              and then Ident_Start_Len (L, 2) > 0
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
               if Peek (L, 1) = '^' then
                  --  §7.2.2 `^^` contract XOR (distinct from bitwise `^`).
                  Tok.Kind := Op_CaretCaret; Advance (L); Advance (L);
               elsif Peek (L, 1) = '=' then
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
               --  A byte >= 16#80# here is a Unicode code point that is
               --  well-formed UTF-8 but not admissible outside an
               --  identifier/string/comment/char-literal (§3.1): report
               --  its decoded value rather than splicing its raw bytes
               --  into the message, which would garble a multibyte
               --  sequence. Decode_UTF8 itself raises citing §3.1 if the
               --  sequence is malformed.
               if Character'Pos (C) >= 16#80# then
                  declare
                     D : constant UTF8_Char := Decode_UTF8 (L);
                  begin
                     raise Translation_Failure
                       with "unexpected character U+"
                          & Hex_Image (Wide_Wide_Character'Pos (D.CP))
                          & " at line" & Positive'Image (L.Line)
                          & ", col"    & Positive'Image (L.Col);
                  end;
               end if;
               raise Translation_Failure
                 with "unexpected character '" & C
                    & "' at line"  & Positive'Image (L.Line)
                    & ", col"      & Positive'Image (L.Col);
         end case;

         return Tok;
      end;
   end Next_Token;
