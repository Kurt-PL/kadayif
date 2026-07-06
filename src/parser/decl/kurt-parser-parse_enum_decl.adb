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
      --  §5.9: enum generics accept inline bounds and a trailing lifetime,
      --  same as fn/impl (`enum box.<T: Display> { ... }`).
      Parse_Opt_Generic_Params_Bounded (C, D.Generic_Params);
      Check_Unique_Generic_Names
        (SU.To_String (D.Name), D.Generic_Params);
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
                     --  §5.5.1/§5.7: payload-field modifiers are parsed and
                     --  retained on the field (the spec defines their
                     --  combination for struct fields; it is silent on
                     --  enum payload fields specifically, so the bootstrap
                     --  carries the same three flags through uniformly and
                     --  enforces `airside` — see Kurt.Sema.Check).
                     declare
                        procedure Skip_Mods
                          (Is_Pub, Is_Mut, Is_Airside : out Boolean)
                        is
                        begin
                           Is_Pub := False;
                           Is_Mut := False;
                           Is_Airside := False;
                           while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside
                           loop
                              case C.Cur.Kind is
                                 when Kw_Pub     => Is_Pub     := True;
                                 when Kw_Mut     => Is_Mut     := True;
                                 when Kw_Airside => Is_Airside := True;
                                 when others     => null;
                              end case;
                              Advance (C);
                           end loop;
                        end Skip_Mods;
                        Fld_Pub, Fld_Mut, Fld_Airside : Boolean;
                     begin
                        Skip_Mods (Fld_Pub, Fld_Mut, Fld_Airside);
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
                              Fld.Is_Pub     := Fld_Pub;
                              Fld.Is_Mut     := Fld_Mut;
                              Fld.Is_Airside := Fld_Airside;
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
                           Skip_Mods (Fld_Pub, Fld_Mut, Fld_Airside);
                        end loop;
                     end;
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
                     D.Any_Explicit := True;   --  §4.11.2: no void discriminant
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
               --  §7.2 `!contract`: the inverted-polarity form. `!` is not
               --  itself a "word" token, so it is peeled off here before
               --  the with-item-word dispatch below.
               if C.Cur.Kind = Op_Bang
                 and then Peek_Tok (C).Kind = Kw_Contract
               then
                  if D.Is_Contract then
                     raise Syntax_Error with
                       "an enum shall declare `contract` or `!contract` "
                       & "at most once, not both (spec 7.2) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  Advance (C);   --  '!'
                  Advance (C);   --  'contract'
                  D.Is_Contract   := True;
                  D.Contract_Inv  := True;
                  if C.Cur.Kind = Punct_Arrow then
                     Advance (C);
                     D.Inv_Type := Parse_Type (C);
                  end if;
               elsif Kurt.Lexer.Is_Word (C.Cur.Kind) then
                  declare
                     Item : constant String := SU.To_String (C.Cur.Lexeme);
                  begin
                     Advance (C);
                     if Item = "contract" then
                        if D.Is_Contract then
                           raise Syntax_Error with
                             "an enum shall declare `contract` or "
                             & "`!contract` at most once, not both "
                             & "(spec 7.2) at line"
                             & Positive'Image (C.Cur.Line);
                        end if;
                        D.Is_Contract := True;
                        --  §7.2 optional `-> inverted_pair_type`; the
                        --  symmetry constraint is enforced in Validate_Enums.
                        if C.Cur.Kind = Punct_Arrow then
                           Advance (C);
                           D.Inv_Type := Parse_Type (C);
                        end if;
                     elsif Item = "discrim" then
                        --  §4.11.3: `with discrim(T)` fixes the
                        --  discriminant type (validated by sema). At most
                        --  one `discrim(...)` per declaration (spec 4.11).
                        if D.Discrim_Ty /= null then
                           raise Syntax_Error with
                             "duplicate `discrim(...)` with-item "
                             & "(spec 4.11) at line"
                             & Positive'Image (C.Cur.Line);
                        end if;
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
                     elsif Item = "repr" then
                        --  §4.11/§4.11.3: on an enum, `repr` governs the
                        --  payload region's layout. At most one per decl.
                        if D.Repr_Packed then
                           raise Syntax_Error with
                             "duplicate `repr(...)` with-item (spec 4.11) "
                             & "at line" & Positive'Image (C.Cur.Line);
                        end if;
                        Expect (C, Punct_LParen, "'('");
                        declare
                           Arg : constant String :=
                             SU.To_String (Take_Ident (C, "repr argument"));
                        begin
                           if Arg = "packed" then
                              D.Repr_Packed := True;
                           elsif Arg = "native" then
                              null;   --  §10.9.2: default layout, no effect.
                           else
                              raise Syntax_Error with
                                "unknown `repr(" & Arg & ")` - expected "
                                & "`packed` or `native` (spec 4.11.4) at "
                                & "line" & Positive'Image (C.Cur.Line);
                           end if;
                        end;
                        Expect (C, Punct_RParen, "')'");
                     elsif Item = "lifetime" then
                        --  §8.4.3 `with lifetime` — retained on
                        --  D.Lifetime_Chains to govern variant payload
                        --  field destruction order (see Kurt.Codegen.
                        --  Emit_Field_Drops). Lifetimes themselves are
                        --  still erased (no run-time representation).
                        Parse_Lifetime_Body (C, D.Lifetime_Chains);
                     elsif Item = "align" then
                        --  §4.11.4 `with align(N)` is a legitimate enum
                        --  with-item that the bootstrap does not model
                        --  semantically. Parse-and-discard a balanced
                        --  item body.
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
                     else
                        --  §5.11: a `with` keyword shall appear only on
                        --  the declaration kinds for which it is defined;
                        --  `variadic` is struct-only, and any other word
                        --  is not a with-keyword at all. Neither is legal
                        --  on an enum.
                        raise Syntax_Error with
                          "with-item `" & Item & "` shall not appear on "
                          & "an enum declaration (spec 5.11) at line"
                          & Positive'Image (C.Cur.Line);
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
            --  §7.2 bare `with contract -> inv_type`.
            if C.Cur.Kind = Punct_Arrow then
               Advance (C);
               D.Inv_Type := Parse_Type (C);
            end if;
         elsif C.Cur.Kind = Op_Bang and then Peek_Tok (C).Kind = Kw_Contract
         then
            --  §7.2 bare `with !contract [-> inv_type]`.
            Advance (C);   --  '!'
            Advance (C);   --  'contract'
            D.Is_Contract  := True;
            D.Contract_Inv := True;
            if C.Cur.Kind = Punct_Arrow then
               Advance (C);
               D.Inv_Type := Parse_Type (C);
            end if;
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "discrim"
         then
            --  Bare form `with discrim(T)` (§4.11.3 example form).
            Advance (C);
            Expect (C, Punct_LParen, "'('");
            D.Discrim_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "repr"
         then
            --  Bare form `with repr(packed);` (§4.11 example form).
            Advance (C);
            Expect (C, Punct_LParen, "'('");
            declare
               Arg : constant String :=
                 SU.To_String (Take_Ident (C, "repr argument"));
            begin
               if Arg = "packed" then
                  D.Repr_Packed := True;
               elsif Arg = "native" then
                  null;
               else
                  raise Syntax_Error with
                    "unknown `repr(" & Arg & ")` - expected `packed` or "
                    & "`native` (spec 4.11.4) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
            end;
            Expect (C, Punct_RParen, "')'");
         elsif C.Cur.Kind = Kw_Destruct then
            --  §8.11/§5.11 bare `with destruct [block]`. This is the
            --  with_single form; per §5.11 the form itself never includes
            --  its own terminator, even when the item's body is a `{...}`
            --  block — the enclosing declaration's grammar (here, a
            --  trailing ';') always follows. Do NOT set Is_Braced here.
            Advance (C);
            D.Has_Destruct := True;
            if C.Cur.Kind = Punct_LBrace then
               Parse_Block_Stmts (C, D.Destruct_Block);
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
