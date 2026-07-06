separate (Kurt.Parser)
   procedure Parse_Payload_Binds (C : in out Cursor; P : in out Pattern) is
   begin
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            --  §5.10.2 `...` at the end of the field list: the fields not
            --  mentioned are ignored. It shall be the last entry.
            if C.Cur.Kind = Op_Ellipsis then
               P.Has_Rest := True;
               Advance (C);
               exit;
            end if;
            --  §7.4 item(a): a slot written as a full nested pattern
            --  (`res::Yes { v }` or a nested struct pattern `pt { x, y }`)
            --  rather than a plain `name` / `name = field`. Distinguished
            --  by what follows the leading identifier -- a plain binding
            --  or rename is never itself followed by `::` or `{`.
            if C.Cur.Kind = Tok_Ident
              and then (Peek_Tok (C).Kind = Punct_ColonColon
                        or else Peek_Tok (C).Kind = Punct_LBrace)
            then
               P.Bindings.Append (SU.Null_Unbounded_String);
               P.Bind_Fields.Append (SU.Null_Unbounded_String);
               while Natural (P.Sub_Pats.Length) < Natural (P.Bindings.Length) - 1
               loop
                  P.Sub_Pats.Append (null);
               end loop;
               P.Sub_Pats.Append
                 (new Pattern'(Parse_Match_Pattern (C)));
            else
               declare
                  N1 : constant SU.Unbounded_String :=
                    Take_Ident (C, "payload binding");
               begin
                  if C.Cur.Kind = Punct_Eq then
                     --  §5.10.2 long form `binding = field`: the leading
                     --  side is the binding name, the following side the
                     --  field name.
                     Advance (C);   --  '='
                     P.Bindings.Append (N1);
                     P.Bind_Fields.Append (Take_Ident (C, "field name"));
                  else
                     P.Bind_Fields.Append (SU.Null_Unbounded_String);
                     P.Bindings.Append (N1);
                  end if;
                  while Natural (P.Sub_Pats.Length)
                          < Natural (P.Bindings.Length)
                  loop
                     P.Sub_Pats.Append (null);
                  end loop;
               end;
            end if;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");
   end Parse_Payload_Binds;
