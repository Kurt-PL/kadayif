separate (Kurt.Lexer)
   function Scan_Ident (L : in out Lexer) return Token is
      Start_Line : constant Positive := L.Line;
      Start_Col  : constant Positive := L.Col;
      Buf        : SU.Unbounded_String;
      T          : Token;
   begin
      --  §3.4: an identifier is a maximal run of continue characters, each
      --  either a single ASCII byte or a multi-byte UTF-8 encoding of a
      --  Unicode letter/digit code point (Ident_Continue_Len, §3.1). The
      --  stored name is the raw byte sequence -- identity and
      --  case-sensitivity are untouched, only the character-set test
      --  changed.
      loop
         declare
            Len : constant Natural := Ident_Continue_Len (L);
         begin
            exit when Len = 0;
            for K in 0 .. Len - 1 loop
               SU.Append (Buf, Peek (L, K));
            end loop;
            for K in 1 .. Len loop
               Advance (L);
            end loop;
         end;
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
