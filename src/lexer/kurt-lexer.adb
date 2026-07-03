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

   function Scan_Ident (L : in out Lexer) return Token is separate;

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

   function Scan_Int (L : in out Lexer) return Token is separate;

   ------------------------------------------------------------------
   --  §3.5.7 escape sequence. On entry the cursor is at the escape
   --  selector character (the one after `\`); on return it is just past
   --  the whole escape. Returns the resolved cell value. Shared by the
   --  string- and character-literal scanners.
   ------------------------------------------------------------------

   function Scan_Escape (L : in out Lexer) return Character is separate;

   ------------------------------------------------------------------
   --  String literal (§3.5.5, §3.5.7).
   --  Per §3.5.5, an unescaped line ending within a string literal is a
   --  TF. Each character is mapped 1:1 to a cell (the C >= W partition
   --  of §3.5.5, with character width equal to cellbits on this target;
   --  the C < W partitioning is deferred).
   ------------------------------------------------------------------

   function Scan_String (L : in out Lexer) return Token is separate;

   function Scan_Raw_String (L : in out Lexer) return Token is separate;

   ------------------------------------------------------------------
   --  Character literal (§3.5.4): exactly one source character or one
   --  escape sequence between single quotes; the value is one cell
   --  (type ui1). Escapes mirror the string-literal set plus \'.
   ------------------------------------------------------------------

   function Scan_Char (L : in out Lexer) return Token is separate;

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
   function Eval_Flag_Expr (L : Lexer; S : String) return Boolean is separate;

   --  Flag-chain directive kinds recognised at the start of a line.
   type Flag_Dir is (FD_None, FD_If, FD_Else_If, FD_Else, FD_Endif);

   --  Classify the line beginning at L.Pos: if its first non-whitespace
   --  token is a `@flag_*` chain directive, return its kind and leave L.Pos
   --  just after the directive keyword (so a following `(expr)` can be read).
   --  Otherwise return FD_None with L.Pos unchanged.
   function Peek_Line_Directive (L : in out Lexer) return Flag_Dir is separate;

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
   function Skip_Inactive_Branch (L : in out Lexer) return Flag_Dir is separate;

   --  From inside a taken branch that just ended (an `@flag_else`/`else_if`
   --  was reached), skip everything to this chain's matching `@flag_endif`,
   --  consuming that endif line. `Else_Seen` carries whether the chain has
   --  already passed its `@flag_else`, so §10.8's duplicate-else and
   --  else-if-after-else constraints hold across the skipped remainder.
   procedure Skip_To_Endif (L : in out Lexer; Else_Seen : Boolean) is separate;

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
   procedure Enter_Line_Chain (L : in out Lexer; First_Cond : Boolean) is separate;

   --  After a taken line branch's body, consume its closing `@` and skip any
   --  remaining (inactive) line branches of the chain.
   procedure Skip_Line_Chain_Rest (L : in out Lexer) is separate;

   --  Handle a `@flag_if` chain at L.Pos (just after the keyword). On return
   --  L.Pos sits at the start of the taken branch's body, or past the whole
   --  chain if no branch is taken.
   procedure Enter_Flag_If (L : in out Lexer) is separate;

   function Next_Token (L : in out Lexer) return Token is separate;

end Kurt.Lexer;
