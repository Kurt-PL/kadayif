separate (Kurt.Parser)
   procedure Parse_Fn_Header
     (C             : in out Cursor;
      Allow_Unnamed : Boolean;
      H             : out Fn_Header)
   is
   begin
      --  §5.14/§5.15: `@inline` / `@no_inline` / `@symbol "name"` precede
      --  the rest of the header (before `pub`/`airside`). The inlining
      --  directives are mutually exclusive.
      while C.Cur.Kind = Dir_At_Inline
            or else C.Cur.Kind = Dir_At_No_Inline
            or else C.Cur.Kind = Dir_At_Symbol
      loop
         if C.Cur.Kind = Dir_At_Inline then
            H.Is_Inline := True;
            Advance (C);
         elsif C.Cur.Kind = Dir_At_No_Inline then
            H.Is_No_Inline := True;
            Advance (C);
         else
            Advance (C);   --  past @symbol
            if C.Cur.Kind /= Tok_String_Lit then
               raise Syntax_Error with
                 "`@symbol` requires a string literal (spec 5.15) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            H.Symbol_Name := C.Cur.Str_Bytes;
            Advance (C);
         end if;
      end loop;
      if H.Is_Inline and then H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline` and `@no_inline` shall not both appear on the same "
           & "subroutine (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;

      --  §5.1 header order: [pub] [extern[(iface)]] — independent
      --  modifiers; `pub extern fn` is legal.
      if C.Cur.Kind = Kw_Pub then
         H.Is_Pub := True;
         Advance (C);
      end if;
      if C.Cur.Kind = Kw_Extern then
         H.Is_Extern := True;
         Advance (C);
      end if;

      if C.Cur.Kind = Kw_Variadic then
         Advance (C);
         H.Is_Variadic := True;
         --  §5.1.3: the declaration form requires the binding clause
         --  `variadic(name: T)`; the bare keyword is the prototype form
         --  (subroutine_proto_header, e.g. inside @dyn).
         if C.Cur.Kind = Punct_LParen then
            Advance (C);
            H.Variadic_Name := Take_Ident (C, "variadic binding name");
            Expect (C, Punct_Colon, "':'");
            H.Variadic_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif not Allow_Unnamed then
            raise Syntax_Error with
              "a variadic subroutine definition requires "
              & "'variadic(name: type)' (spec 5.1.3) at line"
              & Positive'Image (C.Cur.Line);
         end if;
      end if;

      if C.Cur.Kind = Kw_Airside then
         H.Is_Airside := True;
         Advance (C);
      end if;

      Expect (C, Kw_Fn, "'fn'");
      H.Name := Take_Ident (C, "function name");
      Parse_Opt_Generic_Params_Bounded (C, H.Generic_Params);
      Parse_Param_List (C, H.Params, Allow_Unnamed);

      if C.Cur.Kind = Punct_Arrow then
         Advance (C);
         if C.Cur.Kind = Kw_Never then
            --  §4.10/§7.11: `-> never`. No value type; the body diverges.
            Advance (C);
            H.Is_Never    := True;
            H.Return_Type := null;
         else
            H.Return_Type := Parse_Type (C);
         end if;
      else
         H.Return_Type := null;
      end if;

      --  §8.4.3 optional `with lifetime` ordering clause on the subroutine.
      if At_Lifetime_Clause (C) then
         Parse_Lifetime_Clause (C);
      end if;
   end Parse_Fn_Header;
