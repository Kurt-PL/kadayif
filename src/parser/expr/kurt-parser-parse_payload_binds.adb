separate (Kurt.Parser)
   procedure Parse_Payload_Binds (C : in out Cursor; P : in out Pattern) is
   begin
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               N1 : constant SU.Unbounded_String :=
                 Take_Ident (C, "payload binding");
            begin
               if C.Cur.Kind = Punct_Eq then
                  --  §5.10.2 long form `binding = field`: the leading side is
                  --  the binding name, the following side the field name.
                  Advance (C);   --  '='
                  P.Bindings.Append (N1);
                  P.Bind_Fields.Append (Take_Ident (C, "field name"));
               else
                  P.Bind_Fields.Append (SU.Null_Unbounded_String);
                  P.Bindings.Append (N1);
               end if;
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");
   end Parse_Payload_Binds;
