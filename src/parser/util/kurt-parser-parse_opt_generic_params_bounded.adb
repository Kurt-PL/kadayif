separate (Kurt.Parser)
   procedure Parse_Opt_Generic_Params_Bounded
     (C : in out Cursor; Params : out Generic_Param_Vectors.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            --  §5.9 lifetime parameter `'name`: a compile-time discipline
            --  with no representation, so it is parsed and ignored (the
            --  bootstrap's borrow analysis does not consume it).
            if C.Cur.Kind = Tok_Label then
               Advance (C);
            else
               declare
                  P : Generic_Param;
               begin
                  P.Name := Take_Ident (C, "generic parameter");
                  if C.Cur.Kind = Punct_Colon then
                     Advance (C);
                     loop
                        --  §9.8: built-in bound names are keywords
                        --  (`numeric`, `integer`, `primitive`, `contract`,
                        --  `destruct`, `variadic`); trait bounds are
                        --  ordinary identifiers.
                        P.Bounds.Append (Take_Word (C, "bound name"));
                        exit when C.Cur.Kind /= Op_Plus;
                        Advance (C);
                     end loop;
                  end if;
                  --  §5.9 `generic_item = identifier [':' bound]
                  --  [lifetime_param]`: a single item may carry a bound
                  --  AND a trailing lifetime, e.g. `.<T: Display 'a>`.
                  --  Lifetimes are erased later; discard it here just as
                  --  the standalone-lifetime-item branch above does.
                  if C.Cur.Kind = Tok_Label then
                     Advance (C);
                  end if;
                  Params.Append (P);
               end;
            end if;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params_Bounded;
