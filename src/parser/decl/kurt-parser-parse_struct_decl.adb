separate (Kurt.Parser)
   function Parse_Struct_Decl (C : in out Cursor) return Struct_Decl is
      D        : Struct_Decl;
      Has_Body : Boolean := True;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Struct, "'struct'");
      D.Name := Take_Ident (C, "struct name");
      --  §5.9: struct generics accept inline bounds and a trailing
      --  lifetime, same as fn/impl (`struct box.<T: Display> { ... }`).
      Parse_Opt_Generic_Params_Bounded (C, D.Generic_Params);
      Check_Unique_Generic_Names
        (SU.To_String (D.Name), D.Generic_Params);
      --  §5.5 a struct declaration is either a composite form `{ … }` or,
      --  when the body is absent, a unit struct (`struct s;` / `struct s
      --  with …;`) with zero fields. `Has_Body` gates the trailing `;`.
      Has_Body := C.Cur.Kind = Punct_LBrace;
      if Has_Body then
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               Fld : Struct_Field;
            begin
               --  §5.5.1 field modifiers — recorded on the field.
               while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                  case C.Cur.Kind is
                     when Kw_Pub     => Fld.Is_Pub     := True;
                     when Kw_Mut     => Fld.Is_Mut     := True;
                     when Kw_Airside => Fld.Is_Airside := True;
                     when others     => null;
                  end case;
                  Advance (C);
               end loop;
                if C.Cur.Kind = Op_Question then
                   Fld.Name := SU.To_Unbounded_String ("?");
                   Advance (C);
                else
                   Fld.Name := Take_Ident (C, "field name");
                end if;
               Expect (C, Punct_Colon, "':'");
               Fld.Ty := Parse_Type (C);
               --  §5.5.3 optional default-value expression.
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  Fld.Default := Parse_Expr (C);
               end if;
               D.Fields.Append (Fld);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");
      end if;   --  Has_Body

      --  Optional `with` clause (§5.11). Recognised items: `repr(packed)`
      --  (§4.11.4) and `align(N)` (§4.11.5) — bare or inside a with-block;
      --  unrecognised items are skipped (balanced) like the enum parser.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         declare
            --  §4.11: at most one `repr(...)` and one `align(...)` per
            --  declaration.
            Seen_Repr  : Boolean := False;
            Seen_Align : Boolean := False;
            procedure Parse_Struct_With_Item is
               Item : constant String := SU.To_String (C.Cur.Lexeme);
            begin
               --  §5.11: with-item words include keywords (`destruct`,
               --  `contract`) and contextual words (`repr`, `align`, ...).
               if not Kurt.Lexer.Is_Word (C.Cur.Kind) then
                  raise Syntax_Error with
                    "expected with-item word, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);
               if Item = "repr" then
                  if Seen_Repr then
                     raise Syntax_Error with
                       "duplicate `repr(...)` with-item (spec 4.11) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  Seen_Repr := True;
                  Expect (C, Punct_LParen, "'('");
                  declare
                     Arg : constant String :=
                       SU.To_String (Take_Ident (C, "repr argument"));
                  begin
                     if Arg = "packed" then
                        D.Repr_Packed := True;
                     elsif Arg = "native" then
                        --  §10.9.2: `repr(native)` is the default layout /
                        --  invocation interface — in a single-unit bootstrap
                        --  it coincides with the default KSA, so no effect.
                        null;
                     else
                        raise Syntax_Error with
                          "unknown `repr(" & Arg & ")` - expected `packed` "
                          & "or `native` (spec 4.11.4) at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                  end;
                  Expect (C, Punct_RParen, "')'");
               elsif Item = "align" then
                  if Seen_Align then
                     raise Syntax_Error with
                       "duplicate `align(...)` with-item (spec 4.11) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  Seen_Align := True;
                  Expect (C, Punct_LParen, "'('");
                  if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
                     raise Syntax_Error with
                       "expected positive integer in align(N) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  D.Align_N := Cell_Count (C.Cur.Int_V);
                  Advance (C);
                  Expect (C, Punct_RParen, "')'");
               elsif Item = "discrim" then
                  --  §4.11: `discrim(...)` selects an enum's discriminant
                  --  representation type; it shall not appear on a struct.
                  raise Syntax_Error with
                    "`discrim(...)` shall not appear on a struct "
                    & "declaration (spec 4.11) at line"
                    & Positive'Image (C.Cur.Line);
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
               elsif Item = "lifetime" then
                  --  §8.4.3 `with lifetime` — retained on D.Lifetime_Chains
                  --  to govern field destruction order (see
                  --  Kurt.Sema/Kurt.Codegen.Emit_Field_Drops). The
                  --  lifetimes themselves are still erased (no run-time
                  --  representation).
                  Parse_Lifetime_Body (C, D.Lifetime_Chains);
               elsif Item = "variadic" then
                  --  §4.11.5 `with variadic` is a legitimate struct
                  --  with-item that the bootstrap does not model
                  --  semantically (a variadic state struct is treated
                  --  like any other struct). Parse-and-discard a balanced
                  --  item body.
                  declare
                     Depth : Natural := 0;
                  begin
                     while not (Depth = 0
                                and then (C.Cur.Kind = Punct_Comma
                                          or else C.Cur.Kind
                                                 = Punct_RBrace
                                          or else C.Cur.Kind
                                                 = Punct_Semi
                                          or else C.Cur.Kind = Tok_EOF))
                     loop
                        if C.Cur.Kind in Punct_LParen | Punct_LBrace then
                           Depth := Depth + 1;
                        elsif C.Cur.Kind in Punct_RParen | Punct_RBrace
                        then
                           Depth := Depth - 1;
                        end if;
                        Advance (C);
                     end loop;
                  end;
               else
                  --  §5.11: a `with` keyword shall appear only on the
                  --  declaration kinds for which it is defined; `contract`
                  --  and `discrim` are enum-only, and any other word is not
                  --  a with-keyword at all. Neither is legal on a struct.
                  raise Syntax_Error with
                    "with-item `" & Item & "` shall not appear on a "
                    & "struct declaration (spec 5.11) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
            end Parse_Struct_With_Item;
         begin
            if C.Cur.Kind = Punct_LBrace then
               --  with_braced (§5.11): the closing brace terminates the
               --  clause; no trailing ';'.
               Advance (C);
               loop
                  exit when C.Cur.Kind = Punct_RBrace;
                  Parse_Struct_With_Item;
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
               end loop;
               Expect (C, Punct_RBrace, "'}'");
            else
               --  with_single (§5.11): a terminating ';' is required
               --  (§5.6: `composite_form, with_single, ';'`).
               Parse_Struct_With_Item;
               Expect (C, Punct_Semi,
                 "';' after single-item `with` clause (spec 5.11)");
            end if;
         end;
      elsif not Has_Body then
         --  §5.5 a unit struct with no `with` clause: `struct s;`.
         Expect (C, Punct_Semi, "';' after unit struct declaration (spec 5.5)");
      end if;
      return D;
   end Parse_Struct_Decl;
