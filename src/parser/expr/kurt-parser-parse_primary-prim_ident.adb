separate (Kurt.Parser.Parse_Primary)
   function Prim_Ident return Expr_Access is
   begin
            --  §9.2 / §10.6: the keywords admissible as a path head are
            --  `self` (method receiver), `super`, and `srcroot` (module
            --  paths); every other keyword in an identifier position
            --  fails below.
            --  §10.6: `super` shall not appear at source-unit top level,
            --  outside any enclosing `module { ... }`.
            if C.Cur.Kind = Kw_Super and then C.Module_Depth = 0 then
               raise Syntax_Error with
                 "`super` is not valid at source-unit top level, outside "
                 & "any `module` (spec 10.6) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E := new Expr_Node (Kind => E_Path);
            E.Segments.Append (C.Cur.Lexeme);
            Advance (C);
            while C.Cur.Kind = Punct_ColonColon loop
               Advance (C);
               --  §6.1.5 wild construction `Enum::#wild#`: a value of the
               --  enum's implicit `#wild#` (for enums without a declared one).
               if C.Cur.Kind = Tok_Hash_Wild then
                  Advance (C);
                  declare
                     W : constant Expr_Access :=
                       new Expr_Node (Kind => E_Variant_New);
                  begin
                     W.VN_Enum    := E.Segments.First_Element;
                     W.VN_Variant := SU.To_Unbounded_String ("#wild#");
                     return W;
                  end;
               end if;
               --  §10.6 `super::super::name` — chained enclosing-module
               --  references.
               if C.Cur.Kind /= Tok_Ident
                 and then C.Cur.Kind /= Kw_Super
               then
                  raise Syntax_Error with
                    "expected identifier after '::', got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               E.Segments.Append (C.Cur.Lexeme);
               Advance (C);
            end loop;
            --  Explicit generic arguments `path.< T, ... >` (§5.9.2). On a
            --  callee path they drive monomorphisation (Kurt.Mono); on a
            --  literal path (`Box.<si4> { ... }`) the concrete type comes
            --  from context, so the captured args are simply unused.
            if C.Cur.Kind = Punct_Dot
              and then Peek_Tok (C).Kind = Op_Lt
            then
               Advance (C);   --  '.'
               Advance (C);   --  '<'
               Split_Shr_If_Present (C);
               if C.Cur.Kind /= Op_Gt then
                  loop
                     E.P_Type_Args.Append (Parse_Type (C));
                     exit when C.Cur.Kind /= Punct_Comma;
                     Advance (C);
                     Split_Shr_If_Present (C);
                     exit when C.Cur.Kind = Op_Gt;
                  end loop;
               end if;
               Expect (C, Op_Gt, "'>' to close generic arguments");
            end if;
            --  §6.12.2 name intrinsic `T@name`: a translation-time string
            --  (`&[ui1]`) of the type's name. Desugared to a string literal.
            if C.Cur.Kind = Dir_At_Name then
               if Natural (E.Segments.Length) /= 1
                 or else not E.P_Type_Args.Is_Empty
               then
                  raise Syntax_Error with
                    "`@name` operand shall be a plain named type (bootstrap) "
                    & "at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);   --  consume @name
               declare
                  S : constant Expr_Access :=
                    new Expr_Node (Kind => E_String_Lit);
               begin
                  S.Str_Bytes := E.Segments.First_Element;
                  return S;
               end;
            end if;
            --  §6.12 type intrinsic: the parsed path names a *type* when
            --  followed by `@size` / `@align` / `@offset(field)`.
            --  Bootstrap subset: a single-segment named type.
            if C.Cur.Kind in Dir_At_Size | Dir_At_Align | Dir_At_Offset
            then
               if Natural (E.Segments.Length) /= 1
                 or else not E.P_Type_Args.Is_Empty
               then
                  raise Syntax_Error with
                    "type intrinsic operand shall be a plain named type "
                    & "(bootstrap) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               declare
                  TI : constant Expr_Access :=
                    new Expr_Node (Kind => E_Type_Intrinsic);
               begin
                  TI.TI_Ty := new AST_Type'
                    (Kind => T_Named,
                     Name => E.Segments.First_Element,
                     Args => Type_Vectors.Empty_Vector);
                  --  §5.8: an alias name is replaced by its underlying type
                  --  at every use site — including as intrinsic operand.
                  for I in C.Aliases.First_Index ..
                           C.Aliases.Last_Index
                  loop
                     if C.Aliases.Element (I).Params.Is_Empty
                       and then SU."=" (C.Aliases.Element (I).Name,
                                        TI.TI_Ty.Name)
                     then
                        TI.TI_Ty := C.Aliases.Element (I).Target;
                        exit;
                     end if;
                  end loop;
                  case C.Cur.Kind is
                     when Dir_At_Size  => TI.TI_Op := TI_Size;
                     when Dir_At_Align => TI.TI_Op := TI_Align;
                     when others       => TI.TI_Op := TI_Offset;
                  end case;
                  Advance (C);
                  if TI.TI_Op = TI_Offset then
                     Expect (C, Punct_LParen, "'('");
                     TI.TI_Field := Take_Ident (C, "field name");
                     Expect (C, Punct_RParen, "')'");
                  end if;
                  return TI;
               end;
            end if;
            if C.Cur.Kind = Punct_LBrace
              and then not C.No_Struct_Lit
              and then Natural (E.Segments.Length) in 1 .. 2
            then
               declare
                  --  §10.3: `alias::Type { ... }` (alias a known `@add ...
                  --  as alias;` name in this file) is a namespace-qualified
                  --  struct literal, not `Enum::Variant { ... }` — stored as
                  --  a compound `SL_Name` ("alias::Type"), mirroring how
                  --  qualified type names are stored, and mangled later by
                  --  Resolve_Aliases.
                  Is_Add_Alias : constant Boolean :=
                    Natural (E.Segments.Length) = 2
                    and then (for some A of C.Add_Aliases =>
                                SU."=" (A, E.Segments.First_Element));
                  Two  : constant Boolean :=
                    Natural (E.Segments.Length) = 2
                    and then not Is_Add_Alias;
                  Lit  : constant Expr_Access :=
                    (if Two then new Expr_Node (Kind => E_Variant_New)
                            else new Expr_Node (Kind => E_Struct_Lit));
               begin
                  if Two then
                     Lit.VN_Enum    := E.Segments.First_Element;
                     Lit.VN_Variant := E.Segments.Last_Element;
                  elsif Is_Add_Alias then
                     Lit.SL_Name := SU.To_Unbounded_String
                       (SU.To_String (E.Segments.First_Element) & "::"
                        & SU.To_String (E.Segments.Last_Element));
                  else
                     Lit.SL_Name := E.Segments.Last_Element;
                  end if;
                  Advance (C);  --  consume '{'
                  if C.Cur.Kind /= Punct_RBrace then
                     --  §6.1.5 positional vs named: a leading `ident '='`
                     --  starts a named initialiser; anything else is
                     --  positional. Named form is allowed for both struct
                     --  literals and (struct-)variant construction. The
                     --  positional form is meaningful only for tuple
                     --  variants — but using it for a struct literal will
                     --  surface as a field-not-found error in sema.
                     declare
                        Named : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Eq;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              FI : Field_Init;
                           begin
                              if Named then
                                 FI.Name := Take_Ident (C, "field name");
                                 Expect (C, Punct_Eq, "'='");
                              else
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    FI.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Idx := Idx + 1;
                              end if;
                              FI.Val := Parse_Expr (C);
                              if Two then
                                 Lit.VN_Fields.Append (FI);
                              else
                                 Lit.SL_Fields.Append (FI);
                              end if;
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
                  return Lit;
               end;
            end if;
            return E;

   end Prim_Ident;
