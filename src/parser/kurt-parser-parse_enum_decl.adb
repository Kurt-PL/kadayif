separate (Kurt.Parser)
   function Parse_Enum_Decl (C : in out Cursor) return Enum_Decl is
      D    : Enum_Decl;
      Next : Long_Long_Integer := 0;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Enum, "'enum'");
      D.Name := Take_Ident (C, "enum name");
      Parse_Opt_Generic_Params (C, D.Generic_Params);
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               V : Enum_Variant;
            begin
               V.Name := Take_Ident (C, "variant name");
               --  Optional payload (§5.6):
               --     struct variant: `{ ident: type, ... }`  (named fields)
               --     tuple  variant: `{ [pub|mut|airside]* type, ... }`
               --                                          (positional)
               --  Disambiguated by the first non-modifier token sequence:
               --  `ident ':'` -> struct, otherwise -> tuple.
               if C.Cur.Kind = Punct_LBrace then
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     --  Skip leading modifiers to peek the first payload
                     --  token (modifiers themselves are not stored in the
                     --  bootstrap field model).
                     while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                        Advance (C);
                     end loop;
                     declare
                        Is_Struct_Variant : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Colon;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              Fld : Struct_Field;
                           begin
                              if Is_Struct_Variant then
                                 if C.Cur.Kind = Op_Question then
                                    Fld.Name := SU.To_Unbounded_String ("?");
                                    Advance (C);
                                 else
                                    Fld.Name := Take_Ident (C, "payload field name");
                                 end if;
                                 Expect (C, Punct_Colon, "':'");
                                 Fld.Ty := Parse_Type (C);
                              else
                                 --  Synthetic positional name "0", "1", ...
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    Fld.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Fld.Ty := Parse_Type (C);
                                 Idx := Idx + 1;
                              end if;
                              V.Payload.Append (Fld);
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                           while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside
                           loop
                              Advance (C);
                           end loop;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
               end if;
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  if C.Cur.Kind = Tok_Hash_Wild then
                     --  `= #wild#` or `= #wild#(V)`: this variant covers
                     --  all otherwise-unlisted discriminant values, with
                     --  optional canonical value V (§4.5, §5.6).
                     Advance (C);
                     V.Is_Wild := True;
                     if C.Cur.Kind = Punct_LParen then
                        Advance (C);
                        declare
                           Neg : Boolean := False;
                        begin
                           if C.Cur.Kind = Op_Minus then
                              Neg := True;
                              Advance (C);
                           end if;
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer in #wild#(...), got "
                                & Image (C.Cur)
                                & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                           V.Value :=
                             (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                        end;
                        V.Wild_Canon := True;
                        Advance (C);
                        Expect (C, Punct_RParen, "')'");
                     else
                        --  bare `= #wild#`: discriminant via occupied-set pass.
                        V.Auto_Disc := True;
                     end if;
                  elsif C.Cur.Kind = Tok_Int_Lit
                    or else C.Cur.Kind = Op_Minus
                  then
                     --  §4.11.3: a negative explicit value selects a
                     --  signed discriminant type.
                     declare
                        Neg : Boolean := False;
                     begin
                        if C.Cur.Kind = Op_Minus then
                           Neg := True;
                           Advance (C);
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer after '-' in "
                                & "discriminant value, got "
                                & Image (C.Cur) & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                        end if;
                        Next := (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                     end;
                     Advance (C);
                     V.Value := Next;          --  explicit value
                  else
                     raise Syntax_Error with
                       "expected discriminant value after '=', got "
                       & Image (C.Cur)
                       & " at line" & Positive'Image (C.Cur.Line);
                  end if;
               else
                  V.Auto_Disc := True;         --  no `=`: occupied-set pass
               end if;
               D.Variants.Append (V);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");

      --  §5.7 automatic discriminant assignment (occupied-set algorithm):
      --  S = all explicit values + `#wild#(V)` canonical values; counter c=0;
      --  each variant lacking an explicit value (incl. bare `#wild#`) takes the
      --  smallest value >= c not in S, which is then added to S and c bumped.
      declare
         function In_S (Val : Long_Long_Integer) return Boolean is
         begin
            for I in D.Variants.First_Index .. D.Variants.Last_Index loop
               if not D.Variants.Element (I).Auto_Disc
                 and then D.Variants.Element (I).Value = Val
               then
                  return True;     --  explicit or already-assigned / canonical
               end if;
            end loop;
            return False;
         end In_S;
         Cc : Long_Long_Integer := 0;
      begin
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            if D.Variants.Element (I).Auto_Disc then
               while In_S (Cc) loop Cc := Cc + 1; end loop;
               declare
                  V : Enum_Variant := D.Variants.Element (I);
               begin
                  V.Value := Cc;
                  V.Auto_Disc := False;   --  now part of S for later variants
                  D.Variants.Replace_Element (I, V);
               end;
               Cc := Cc + 1;
            end if;
         end loop;
      end;

      --  Optional `with` clause (§5.10).
      --     `with contract`                       — bare contract clause
      --     `with { item, item, ... }`              — with-block (§4.5, §5.10)
      --  Items recognised by the bootstrap: `contract [-> type]`, `discrim
      --  (type)`. Other items (repr, align, ...) are parsed-and-discarded.
      if C.Cur.Kind = Kw_With then
       declare
         Is_Braced : Boolean := False;
       begin
         Advance (C);
         if C.Cur.Kind = Punct_LBrace then
            Is_Braced := True;
            Advance (C);
            loop
               exit when C.Cur.Kind = Punct_RBrace;
               if Kurt.Lexer.Is_Word (C.Cur.Kind) then
                  declare
                     Item : constant String := SU.To_String (C.Cur.Lexeme);
                  begin
                     Advance (C);
                     if Item = "contract" then
                        D.Is_Contract := True;
                        --  Optional `-> inverted_pair_type` (§7.2). The
                        --  inverted pair is parsed and discarded; `!verdict`
                        --  is not yet activated.
                        if C.Cur.Kind = Punct_Arrow then
                           Advance (C);
                           declare
                              Ignore : constant Type_Access := Parse_Type (C);
                              pragma Unreferenced (Ignore);
                           begin null; end;
                        end if;
                     elsif Item = "discrim" then
                        --  §4.11.3: `with discrim(T)` fixes the
                        --  discriminant type (validated by sema).
                        Expect (C, Punct_LParen, "'('");
                        D.Discrim_Ty := Parse_Type (C);
                        Expect (C, Punct_RParen, "')'");
                     elsif Item = "destruct" then
                        --  §8.11 `with destruct [block]`.
                        D.Has_Destruct := True;
                        if C.Cur.Kind = Punct_LBrace then
                           Parse_Block_Stmts (C, D.Destruct_Block);
                        end if;
                     elsif Item = "concurrent" then
                        --  §8.10 context-safety markers.
                        Parse_Concurrent_Items
                          (C, D.Conc_Transfer, D.Conc_No_Transfer,
                           D.Conc_Reference, D.Conc_No_Reference);
                     else
                        --  Unrecognised with-item: skip balanced tokens up
                        --  to the next ',' or '}'. The bootstrap does not
                        --  semantically use repr/align/lifetime/...
                        declare
                           Depth : Natural := 0;
                        begin
                           while not (Depth = 0
                                      and then (C.Cur.Kind = Punct_Comma
                                                or else C.Cur.Kind
                                                       = Punct_RBrace))
                           loop
                              if C.Cur.Kind in Punct_LParen
                                | Punct_LBrace
                              then
                                 Depth := Depth + 1;
                              elsif C.Cur.Kind in Punct_RParen
                                | Punct_RBrace
                              then
                                 Depth := Depth - 1;
                              end if;
                              Advance (C);
                           end loop;
                        end;
                     end if;
                  end;
               else
                  raise Syntax_Error with
                    "expected with-item word, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               exit when C.Cur.Kind /= Punct_Comma;
               Advance (C);
            end loop;
            Expect (C, Punct_RBrace, "'}'");
         elsif C.Cur.Kind = Kw_Contract then
            D.Is_Contract := True;
            Advance (C);
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "discrim"
         then
            --  Bare form `with discrim(T)` (§4.11.3 example form).
            Advance (C);
            Expect (C, Punct_LParen, "'('");
            D.Discrim_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif C.Cur.Kind = Kw_Destruct then
            --  §8.11 bare `with destruct [block]`.
            Advance (C);
            D.Has_Destruct := True;
            if C.Cur.Kind = Punct_LBrace then
               Parse_Block_Stmts (C, D.Destruct_Block);
               Is_Braced := True;   --  the block terminates it; no ';'
            end if;
         else
            raise Syntax_Error with
              "expected 'contract' or '{' after 'with', got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
         --  §5.7 / §5.11: `with_single` requires a terminating ';';
         --  `with_braced` is terminated by its closing brace.
         if not Is_Braced then
            Expect (C, Punct_Semi,
              "';' after single-item `with` clause (spec 5.11)");
         end if;
       end;
      end if;
      return D;
   end Parse_Enum_Decl;
