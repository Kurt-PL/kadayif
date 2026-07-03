separate (Kurt.Parser)
   function Parse_Dyn_Decl (C : in out Cursor) return Dyn_Decl is
      D : Dyn_Decl;
   begin
      Expect (C, Dir_At_Dyn, "'@dyn'");
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      --  §10.4 optional bound form `[prefix::]"path"`. The path identifies the
      --  opaque code; resolution/symbol-presence checking against the host
      --  linker is deferred, so the path is recorded but not yet verified.
      if C.Cur.Kind = Tok_Ident
        and then Peek_Tok (C).Kind = Punct_ColonColon
      then
         Advance (C);   --  prefix
         Advance (C);   --  ::
      end if;
      if C.Cur.Kind = Tok_String_Lit then
         D.Bound_Path := C.Cur.Str_Bytes;
         Advance (C);
      end if;
      Expect (C, Kw_As, "'as'");
      D.Alias := Take_Ident (C, "alias name for @dyn block");

      Expect (C, Punct_LBrace, "'{'");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         if C.Cur.Kind = Kw_Fn
           or else C.Cur.Kind = Kw_Pub
           or else C.Cur.Kind = Kw_Extern
           or else C.Cur.Kind = Kw_Variadic
           or else C.Cur.Kind = Dir_At_Symbol   --  §5.15 on a dyn item
         then
            D.Items.Append (Parse_Fn_Proto (C));
         else
            raise Syntax_Error with
              "expected fn prototype inside @dyn block, got "
              & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}'");
      return D;
   end Parse_Dyn_Decl;
