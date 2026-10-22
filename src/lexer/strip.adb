with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Diagnostics;

package body Strip is

   use Ada.Strings.Unbounded;

   package Offset_Vectors is new Ada.Containers.Vectors (Positive, Positive);

   function Position
     (S : Stripped; Index : Positive) return Source_Map.Source_Pos
   is
   begin
      if Index > S.Origin'Last then
         return (S.Source, S.Origin (S.Origin'Last) + 1);
      end if;
      return (S.Source, S.Origin (Index));
   end Position;

   function Char_Length (C : Character) return Positive is
      B : constant Natural := Character'Pos (C);
   begin
      if B < 16#C0# then
         return 1;
      elsif B < 16#E0# then
         return 2;
      elsif B < 16#F0# then
         return 3;
      else
         return 4;
      end if;
   end Char_Length;

   function Char_Literal_End (S : String; I : Positive) return Natural is
      J : Positive := I + 1;
   begin
      if J > S'Last then
         return 0;
      end if;
      if S (J) = '\' then
         if J + 1 > S'Last then
            return 0;
         elsif S (J + 1) = 'x' then
            for D in 1 .. Hex_Escape_Digits loop
               if J + 1 + D > S'Last or else not Is_Hex (S (J + 1 + D)) then
                  return 0;
               end if;
            end loop;
            J := J + 2 + Hex_Escape_Digits;
         elsif S (J + 1) in '0' | 'a' | 'b' | 't' | 'n' | 'v' | 'f' | 'r'
                          | '\' | ''' | '"'
         then
            J := J + 2;
         else
            return 0;
         end if;
      elsif S (J) in ''' | ASCII.LF | ASCII.CR then
         return 0;
      else
         J := J + Char_Length (S (J));
      end if;
      if J <= S'Last and then S (J) = ''' then
         return J;
      end if;
      return 0;
   end Char_Literal_End;

   function Run (Id : Source_Map.Source_Id) return Stripped is
      Raw : constant Source_Map.Text_Access := Source_Map.Text (Id);

      --  줄 끝 인식 단계: 마지막이 줄 끝이 아니면 하나 덧붙인다 (§3.2)
      Needs_Newline : constant Boolean :=
        Raw'Length = 0 or else Raw (Raw'Last) /= ASCII.LF;
      Src : constant String :=
        Raw.all & (if Needs_Newline then [1 => ASCII.LF] else "");

      Out_Text : Unbounded_String;
      Out_Map  : Offset_Vectors.Vector;
      I        : Positive := Src'First;

      function At_Pos (K : Positive) return Source_Map.Source_Pos is
        ((Id, Natural'Min (K, Raw'Length + 1)));

      procedure Emit (C : Character; From : Positive) is
      begin
         Append (Out_Text, C);
         Out_Map.Append (Natural'Min (From, Raw'Length + 1));
      end Emit;

      procedure Emit_Through (Last : Natural) is
      begin
         while I <= Last loop
            Emit (Src (I), I);
            I := I + 1;
         end loop;
      end Emit_Through;

      function Peek (K : Natural) return Character is
        (if I + K <= Src'Last then Src (I + K) else ASCII.NUL);

      function Prev_Is_Ident return Boolean is
        (Length (Out_Text) > 0
         and then Is_Ident_Char (Element (Out_Text, Length (Out_Text))));

      --  '#' 다음 단어
      function Directive_Word return String is
         J : Natural := I + 1;
      begin
         while J <= Src'Last and then Is_Ident_Char (Src (J)) loop
            J := J + 1;
         end loop;
         return Src (I + 1 .. J - 1);
      end Directive_Word;

      procedure Scan_String is
         Start : constant Positive := I;
      begin
         Emit_Through (I);
         loop
            if I > Src'Last then
               Diagnostics.Error
                 (At_Pos (Start), "unterminated string literal");
               return;
            end if;
            if Src (I) = '\' and then I < Src'Last then
               Emit_Through (I + 1);
            elsif Src (I) = '"' then
               Emit_Through (I);
               return;
            else
               Emit_Through (I);
            end if;
         end loop;
      end Scan_String;

      procedure Scan_Raw_String is
         Start  : constant Positive := I;
         Hashes : Natural := 0;
      begin
         Emit_Through (I);  --  r
         while Src (I) = '#' loop
            Hashes := Hashes + 1;
            Emit_Through (I);
         end loop;
         Emit_Through (I);  --  "
         loop
            if I > Src'Last then
               Diagnostics.Error
                 (At_Pos (Start), "unterminated raw string literal");
               return;
            end if;
            if Src (I) = '"'
              and then I + Hashes <= Src'Last
              and then Src (I + 1 .. I + Hashes) = [1 .. Hashes => '#']
            then
               Emit_Through (I + Hashes);
               return;
            end if;
            Emit_Through (I);
         end loop;
      end Scan_Raw_String;

      procedure Scan_Block_Comment is
         Start : constant Positive := I;
         Depth : Natural := 1;
      begin
         I := I + 2;
         while Depth > 0 loop
            if I > Src'Last then
               Diagnostics.Error
                 (At_Pos (Start), "unterminated block comment");
               return;
            end if;
            if Src (I) = '/' and then Peek (1) = '*' then
               Depth := Depth + 1;
               I := I + 2;
            elsif Src (I) = '*' and then Peek (1) = '/' then
               Depth := Depth - 1;
               I := I + 2;
            else
               I := I + 1;
            end if;
         end loop;
         Emit (' ', Start);
      end Scan_Block_Comment;

      function Is_Raw_String_Opening return Boolean is
         J : Positive := I + 1;
      begin
         if Prev_Is_Ident then
            return False;
         end if;
         while J <= Src'Last and then Src (J) = '#' loop
            J := J + 1;
         end loop;
         return J <= Src'Last and then Src (J) = '"';
      end Is_Raw_String_Opening;

   begin
      while I <= Src'Last loop
         declare
            C : constant Character := Src (I);
         begin
            if C = '"' then
               Scan_String;
            elsif C = 'r' and then Is_Raw_String_Opening then
               Scan_Raw_String;
            elsif C = ''' and then Char_Literal_End (Src, I) > 0 then
               Emit_Through (Char_Literal_End (Src, I));
            elsif C = 'i' and then Peek (1) = '#'
              and then Is_Ident_Start (Peek (2))
              and then not Prev_Is_Ident
            then
               --  raw identifier: '#'가 지시어로 읽히지 않게 통째로 넘긴다
               Emit_Through (I + 1);
               while I <= Src'Last and then Is_Ident_Char (Src (I)) loop
                  Emit_Through (I);
               end loop;
            elsif C = '/' and then Peek (1) = '/' then
               Emit (' ', I);
               while Src (I) /= ASCII.LF loop
                  I := I + 1;
               end loop;
            elsif C = '/' and then Peek (1) = '*' then
               Scan_Block_Comment;
            elsif C = '*' and then Peek (1) = '/' then
               Diagnostics.Error
                 (At_Pos (I), "'*/' outside a block comment");
               Emit_Through (I + 1);
            elsif C = '#'
              and then Directive_Word in "flag" | "unflag" | "flag_if"
                | "flag_else_if" | "flag_else" | "flag_endif"
            then
               Diagnostics.Unimplemented
                 (At_Pos (I),
                  "flag declarations and conditional translation"
                  & " (§10.8, §10.9)");
               Emit (' ', I);
               I := I + 1 + Directive_Word'Length;
            else
               Emit_Through (I);
            end if;
         end;
      end loop;

      declare
         Origin : Origin_Array (1 .. Natural (Out_Map.Length));
      begin
         for K in Origin'Range loop
            Origin (K) := Out_Map (K);
         end loop;
         return
           (Source => Id,
            Text   => new String'(To_String (Out_Text)),
            Origin => new Origin_Array'(Origin));
      end;
   end Run;

end Strip;
