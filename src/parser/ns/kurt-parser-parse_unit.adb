separate (Kurt.Parser)
   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit
   is
      C : Cursor := (Lex => Lex'Unchecked_Access, others => <>);
      U : Translation_Unit;
      --  §10.6 `module name { … }` — a real namespace: when a module body
      --  closes, every declaration it appended (a slice of U's vectors,
      --  tracked by the entry Snapshot) is renamed `name$item` and every
      --  internal reference is rewritten to match (Apply_Namespace); the
      --  mangled module prefix then doubles as its own access alias
      --  (`name::item` → `name$item` via Resolve_Aliases). One stack
      --  entry per open module, innermost last.
      type Module_Frame is record
         Name     : SU.Unbounded_String;
         Snap     : Rename_From;
         MN_Start : Natural;   --  U.Module_Names length at open
         --  §10.6 `pub module` -- whether THIS module's own namespace
         --  identifier is visible to importers of the source unit (item-
         --  level `pub` inside the body is independent and unaffected).
         Is_Pub   : Boolean := False;
      end record;
      package Module_Stacks is new Ada.Containers.Vectors
        (Index_Type => Positive, Element_Type => Module_Frame);
      Modules : Module_Stacks.Vector;

      --  Close the innermost open module: namespace its declaration slice
      --  and register/refresh the module-alias prefixes.
      procedure Close_Module is
         Fr    : constant Module_Frame := Modules.Last_Element;
         Nm    : constant String := SU.To_String (Fr.Name);
         Extra : Path_Segments.Vector;
      begin
         Modules.Delete_Last;
         C.Module_Depth := C.Module_Depth - 1;
         --  Heads of the sub-modules closed inside this body — their
         --  mangled declarations (`b$f`) must pick up this prefix too.
         for I in Fr.MN_Start + 1 .. Natural (U.Module_Names.Length) loop
            declare
               M      : constant String :=
                 SU.To_String (U.Module_Names.Element (I));
               Dollar : constant Natural := Ada.Strings.Fixed.Index (M, "$");
               Head   : constant String :=
                 (if Dollar = 0 then M else M (M'First .. Dollar - 1));
               Dup    : Boolean := False;
            begin
               for E of Extra loop
                  if SU.To_String (E) = Head then
                     Dup := True;
                  end if;
               end loop;
               if not Dup then
                  Extra.Append (SU.To_Unbounded_String (Head));
               end if;
            end;
         end loop;
         Apply_Namespace
           (U, Nm, From => Fr.Snap, Extra_Names => Extra,
            Super_Word => "super");
         --  Sub-module prefixes gain this module's prefix; then this
         --  module itself becomes an alias. Nested Module_Pubs entries
         --  keep their own flag unchanged -- only the NAME gains a prefix
         --  segment; pub-ness is per-module, not inherited from a parent.
         for I in Fr.MN_Start + 1 .. Natural (U.Module_Names.Length) loop
            U.Module_Names.Replace_Element
              (I, SU.To_Unbounded_String
                    (Nm & "$" & SU.To_String (U.Module_Names.Element (I))));
         end loop;
         U.Module_Names.Append (Fr.Name);
         U.Module_Pubs.Append (Fr.Is_Pub);
      end Close_Module;

      --  Open a module: record its frame (after `module name {` is read).
      --  The name also joins the cursor's namespace-alias set so a
      --  composite literal `name::Type { ... }` parses as a qualified
      --  struct literal rather than `Enum::Variant { ... }`.
      procedure Open_Module
        (Nm : SU.Unbounded_String; Pub : Boolean := False) is
      begin
         Modules.Append
           ((Name     => Nm,
             Snap     => Snapshot (U),
             MN_Start => Natural (U.Module_Names.Length),
             Is_Pub   => Pub));
         C.Add_Aliases.Append (Nm);
         C.Module_Depth := C.Module_Depth + 1;
      end Open_Module;

      --  §5.12.2 `use_path = path | path::'{' use_item, ... '}'`,
      --  `use_item = identifier | use_path` -- parsed recursively: Prefix
      --  is the path accumulated so far. A plain trailing identifier (no
      --  further `::`) terminates the path and registers it (U.Use_Names/
      --  Use_Paths); a `::` continues the chain, either into a further
      --  single identifier or into a braced group, each entry of which is
      --  itself a (possibly further-nested) use_path sharing this prefix.
      --  Resolution against the alias/module/`pub` machinery, and the
      --  actual name-substitution rewrite, happen later in
      --  Kurt.Parser.Resolve_Aliases (this pass only records the syntax).
      procedure Parse_Use_Path (Prefix : Path_Segments.Vector) is
         --  §10.6 `module_path` permits a leading `super`/`srcroot` on a
         --  `use` path declared inside a `module` body; resolving one
         --  against the enclosing module's (not-yet-mangled, not-yet-
         --  known-prefix) scope is not modelled by this bootstrap's
         --  single deferred resolution pass (Kurt.Parser.Resolve_Aliases)
         --  -- rejected here, at parse time, with a clear diagnostic
         --  rather than left to fail later as a confusing "does not
         --  resolve" error. A top-level `use` (this bootstrap's normal
         --  case, and the one in the spec's own §5.12.2 examples) is
         --  unaffected.
         Seg  : SU.Unbounded_String;
         Full : Path_Segments.Vector := Prefix;
      begin
         if Prefix.Is_Empty
           and then (C.Cur.Kind = Kw_Super or else C.Cur.Kind = Kw_Srcroot)
         then
            raise Syntax_Error with
              "a `use` path headed by '" & SU.To_String (C.Cur.Lexeme)
              & "' is not supported by this bootstrap (spec 5.12.2/10.6) "
              & "at line" & Positive'Image (C.Cur.Line);
         end if;
         Seg := Take_Ident (C, "use path segment");
         Full.Append (Seg);
         if C.Cur.Kind = Punct_ColonColon then
            Advance (C);
            if C.Cur.Kind = Punct_LBrace then
               Advance (C);
               loop
                  Parse_Use_Path (Full);
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;
               end loop;
               Expect (C, Punct_RBrace, "'}' to close `use` group "
                       & "(spec 5.12.2)");
            else
               Parse_Use_Path (Full);
            end if;
         else
            U.Use_Names.Append (Seg);
            U.Use_Paths.Append (Full);
         end if;
      end Parse_Use_Path;
   begin
      Advance (C);
      while C.Cur.Kind /= Tok_EOF loop
         --  §5.16: skip any `@[ ... ]@` annotations preceding a declaration.
         --  Their content is opaque and unrecognised ones are ignored.
         while C.Cur.Kind = Dir_At_LBracket loop
            Advance (C);
            while C.Cur.Kind /= Dir_At_RBracket loop
               if C.Cur.Kind = Tok_EOF then
                  raise Syntax_Error with
                    "unbalanced `@[` annotation (missing `]@`, spec 5.16)";
               end if;
               Advance (C);
            end loop;
            Advance (C);   --  past `]@`
         end loop;
         exit when C.Cur.Kind = Tok_EOF;
         case C.Cur.Kind is
            when Kw_Fn | Kw_Extern | Kw_Variadic | Kw_Airside
               | Dir_At_Inline | Dir_At_No_Inline   --  §5.14
               | Dir_At_Symbol =>                    --  §5.15
               U.Fns.Append (Parse_Fn_Decl (C));
            when Kw_Pub =>
               --  `pub` heads a subroutine, trait, struct, enum, const, or
               --  static. §10.3: `pub` governs whether the declaration is
               --  reachable through a `@add`-ing unit's namespace.
               if Peek_Tok (C).Kind = Kw_Trait then
                  Parse_Trait_Decl (C, U.Traits);
               elsif Peek_Tok (C).Kind = Kw_Struct then
                  U.Structs.Append (Parse_Struct_Decl (C));
               elsif Peek_Tok (C).Kind = Kw_Enum then
                  U.Enums.Append (Parse_Enum_Decl (C));
               elsif Peek_Tok (C).Kind = Kw_Const then
                  Advance (C);
                  declare
                     CD : Const_Decl := Parse_Const_Decl (C);
                  begin
                     CD.Is_Pub := True;
                     U.Consts.Append (CD);
                  end;
               elsif Peek_Tok (C).Kind = Kw_Module then
                  --  §10.6 `pub module name { … }`.
                  Advance (C);   --  `pub`
                  Advance (C);   --  `module`
                  declare
                     Nm : constant SU.Unbounded_String :=
                       Take_Ident (C, "module name");
                  begin
                     Expect (C, Punct_LBrace, "'{' to open module body");
                     Open_Module (Nm, Pub => True);
                  end;
               elsif Peek_Tok (C).Kind = Kw_Static then
                  Advance (C);
                  declare
                     SD : Static_Decl := Parse_Static_Decl (C);
                  begin
                     SD.Is_Pub := True;
                     U.Statics.Append (SD);
                  end;
               else
                  U.Fns.Append (Parse_Fn_Decl (C));
               end if;
            when Kw_Const =>
               U.Consts.Append (Parse_Const_Decl (C));
            when Dir_At_Dyn =>
               U.Dyns.Append (Parse_Dyn_Decl (C));
            when Dir_At_Add =>
               --  §10.3 `@add [pub] [prefix::]( path_form | block_form )`:
               --    path_form  = "path" as ident ;
               --    block_form = { "a" as x, "b" as y [,] }
               --  the `as ident` namespace name is mandatory and is how each
               --  import's `pub` declarations are accessed (`ident::item`).
               --  A block simply groups several path entries under one
               --  prefix — no semantic distinction. §10.3 `@add pub`: the
               --  namespace identifier itself is re-exported to importers
               --  of this source unit (Kurt.Parser.Resolve_Aliases /
               --  main-translate.adb's Load implement the propagation).
               Advance (C);
               declare
                  Prefix     : SU.Unbounded_String;
                  Add_Is_Pub : Boolean := False;

                  --  Parse one `"path" as ident` entry (prefix pre-read).
                  procedure Parse_Entry is
                  begin
                     if C.Cur.Kind /= Tok_String_Lit then
                        raise Syntax_Error with
                          "`@add` requires a string path at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                     U.Adds.Append (C.Cur.Str_Bytes);
                     U.Add_Prefixes.Append (Prefix);
                     Advance (C);
                     Expect (C, Kw_As, "`as` in @add (spec 10.3)");
                     declare
                        Ns : constant SU.Unbounded_String :=
                          Take_Ident (C, "@add namespace name");
                     begin
                        U.Add_Names.Append (Ns);
                        U.Add_Pubs.Append (Add_Is_Pub);
                        C.Add_Aliases.Append (Ns);
                     end;
                  end Parse_Entry;
               begin
                  if C.Cur.Kind = Kw_Pub then
                     Add_Is_Pub := True;
                     Advance (C);
                  end if;
                  if C.Cur.Kind = Tok_Ident
                    and then Peek_Tok (C).Kind = Punct_ColonColon
                  then
                     Prefix := C.Cur.Lexeme;
                     Advance (C);   --  prefix
                     Advance (C);   --  ::
                  end if;
                  if C.Cur.Kind = Punct_LBrace then
                     --  §10.3 block form.
                     Advance (C);
                     loop
                        Parse_Entry;
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RBrace;
                     end loop;
                     Expect (C, Punct_RBrace, "'}' to close @add block");
                     if C.Cur.Kind = Punct_Semi then
                        Advance (C);
                     end if;
                  else
                     --  §10.3 path form.
                     Parse_Entry;
                     Expect (C, Punct_Semi, "';' after @add");
                  end if;
               end;
            when Dir_At_Path =>
               --  §10.5 `@path "base" as name;` — named search-path prefix.
               Advance (C);
               if C.Cur.Kind /= Tok_String_Lit then
                  raise Syntax_Error with
                    "`@path` requires a string base at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               declare
                  Base : constant SU.Unbounded_String := C.Cur.Str_Bytes;
                  Line : constant Positive := C.Cur.Line;
               begin
                  Advance (C);
                  Expect (C, Kw_As, "'as' in @path");
                  declare
                     Nm : constant SU.Unbounded_String :=
                       Take_Ident (C, "@path prefix name");
                  begin
                     --  §10.5: duplicate declarations of the same prefix
                     --  name within one source unit are a translation
                     --  failure (the cross-unit identical-base allowance is
                     --  enforced by the driver).
                     for P in U.Path_Names.First_Index ..
                              U.Path_Names.Last_Index loop
                        if SU."=" (U.Path_Names.Element (P), Nm) then
                           raise Syntax_Error with
                             "duplicate `@path` prefix '"
                             & SU.To_String (Nm)
                             & "' (§10.5) at line" & Positive'Image (Line);
                        end if;
                     end loop;
                     U.Path_Names.Append (Nm);
                     U.Path_Bases.Append (Base);
                  end;
               end;
               if C.Cur.Kind = Punct_Semi then
                  Advance (C);
               end if;
            when Dir_At_Trap =>
               --  §7.10.1 `@trap { ... }` handler. At most one per
               --  translation unit.
               if U.Has_Trap_Handler then
                  raise Syntax_Error with
                    "multiple @trap handlers in one translation unit "
                    & "(§7.10.1) at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);
               U.Has_Trap_Handler := True;
               Parse_Block_Stmts (C, U.Trap_Handler);
            when Tok_Asm =>
               --  §5.13 top-level inline assembly — emitted verbatim into the
               --  text section. Operand-less only (bootstrap).
               U.Top_Asm.Append (C.Cur.Lexeme);
               Advance (C);
               if C.Cur.Kind = Punct_Semi then
                  Advance (C);
               end if;
            when Kw_Struct =>
               U.Structs.Append (Parse_Struct_Decl (C));
            when Kw_Enum =>
               U.Enums.Append (Parse_Enum_Decl (C));
            when Kw_Impl =>
               Parse_Impl_Decl
                 (C, U.Fns, U.Trait_Impls, U.Gen_Methods, U.Traits);
            when Kw_Trait =>
               Parse_Trait_Decl (C, U.Traits);
            when Punct_RBrace =>
               --  §10.6 closing brace of a `module` body: namespace the
               --  slice of declarations the body appended.
               if Modules.Is_Empty then
                  raise Syntax_Error with
                    "unexpected '}' at top level at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Close_Module;
               Advance (C);
            when Kw_Static =>
               --  §5.4 `static [mut] NAME: T = expr ;`.
               U.Statics.Append (Parse_Static_Decl (C));
            when Kw_Module =>
               --  §10.6 `module name { … }` — a namespace: the body's
               --  declarations are renamed `name$item` when it closes.
               Advance (C);   --  `module`
               declare
                  Nm : constant SU.Unbounded_String :=
                    Take_Ident (C, "module name");
               begin
                  Expect (C, Punct_LBrace, "'{' to open module body");
                  Open_Module (Nm);
               end;
            when Kw_Use =>
               --  §5.12.2 `use path::name;` — unqualified name
               --  introduction. Parsed here (recursively, to cover the
               --  braced multi-import and nested-group forms); resolved
               --  against the alias/module/`pub` machinery, and the
               --  actual substitution applied, by Kurt.Parser.
               --  Resolve_Aliases once this whole source unit is known.
               Advance (C);
               Parse_Use_Path (Path_Segments.Empty_Vector);
               Expect (C, Punct_Semi, "';' after `use` (spec 5.12.2)");
            when Kw_Type =>
               --  §5.8 `type NAME = type ;` — alias declaration. The
               --  substitution happens at later use sites (Parse_Type),
               --  so nothing is recorded in the translation unit.
               Advance (C);
               declare
                  A : Alias_Entry;

                  --  Whether the type tree T mentions a `T_Named` with the
                  --  given name anywhere (in itself or a component).
                  function Mentions (T : Type_Access; Nm : String)
                    return Boolean is
                  begin
                     if T = null then
                        return False;
                     end if;
                     case T.Kind is
                        when T_Named =>
                           if SU.To_String (T.Name) = Nm then
                              return True;
                           end if;
                           for I in T.Args.First_Index .. T.Args.Last_Index
                           loop
                              if Mentions (T.Args.Element (I), Nm) then
                                 return True;
                              end if;
                           end loop;
                           return False;
                        when T_Ref =>
                           return Mentions (T.Target, Nm);
                        when T_Array =>
                           return Mentions (T.Elem, Nm);
                        when T_Tuple =>
                           for I in T.Elems.First_Index .. T.Elems.Last_Index
                           loop
                              if Mentions (T.Elems.Element (I), Nm) then
                                 return True;
                              end if;
                           end loop;
                           return False;
                        when T_Fn =>
                           for I in T.Fn_Params.First_Index
                                    .. T.Fn_Params.Last_Index loop
                              if Mentions (T.Fn_Params.Element (I), Nm) then
                                 return True;
                              end if;
                           end loop;
                           return Mentions (T.Fn_Ret, Nm);
                        when T_Dyn =>
                           return False;
                     end case;
                  end Mentions;
               begin
                  A.Name := Take_Ident (C, "alias name after 'type'");
                  --  §5.8 generic alias `type Name.<T, U> = ...`.
                  if C.Cur.Kind = Punct_Dot
                    and then Peek_Tok (C).Kind = Op_Lt
                  then
                     Advance (C);   --  '.'
                     Advance (C);   --  '<'
                     loop
                        A.Params.Append
                          (Take_Ident (C, "alias type parameter"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                     end loop;
                     Expect (C, Op_Gt, "'>' to close alias parameters");
                  end if;
                  Expect (C, Punct_Eq, "'=' in type alias");
                  A.Target := Parse_Type (C);
                  Expect (C, Punct_Semi, "';' after type alias");
                  --  §5.8 a directly or mutually recursive alias shall not
                  --  appear. Because Parse_Type already substituted any
                  --  earlier alias into A.Target, a mutual cycle surfaces here
                  --  as the alias name mentioning itself.
                  if Mentions (A.Target, SU.To_String (A.Name)) then
                     raise Syntax_Error with
                       "type alias '" & SU.To_String (A.Name)
                       & "' is directly or mutually recursive (spec 5.8)";
                  end if;
                  --  §5.8 every declared type parameter shall appear in the
                  --  aliased type.
                  for I in A.Params.First_Index .. A.Params.Last_Index loop
                     if not Mentions
                              (A.Target, SU.To_String (A.Params.Element (I)))
                     then
                        raise Syntax_Error with
                          "type parameter '"
                          & SU.To_String (A.Params.Element (I))
                          & "' does not appear in the aliased type of '"
                          & SU.To_String (A.Name) & "' (spec 5.8)";
                     end if;
                  end loop;
                  --  §5.17 a declared name shall not be redeclared in the
                  --  same scope: reject a second `type` alias with the
                  --  same name (and a clash with an existing struct/enum
                  --  name, cheaply checked here too).
                  for I in C.Aliases.First_Index .. C.Aliases.Last_Index loop
                     if SU."=" (C.Aliases.Element (I).Name, A.Name) then
                        raise Syntax_Error with
                          "type alias '" & SU.To_String (A.Name)
                          & "' is already declared (spec 5.17)";
                     end if;
                  end loop;
                  for I in U.Structs.First_Index .. U.Structs.Last_Index loop
                     if SU."=" (U.Structs.Element (I).Name, A.Name) then
                        raise Syntax_Error with
                          "type alias '" & SU.To_String (A.Name)
                          & "' clashes with a struct of the same name "
                          & "(spec 5.17)";
                     end if;
                  end loop;
                  for I in U.Enums.First_Index .. U.Enums.Last_Index loop
                     if SU."=" (U.Enums.Element (I).Name, A.Name) then
                        raise Syntax_Error with
                          "type alias '" & SU.To_String (A.Name)
                          & "' clashes with an enum of the same name "
                          & "(spec 5.17)";
                     end if;
                  end loop;
                  C.Aliases.Append (A);
               end;
            when others =>
               raise Syntax_Error with
                 "expected top-level declaration, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
         end case;
      end loop;
      if not Modules.Is_Empty then
         raise Syntax_Error with
           "unterminated `module` (missing '}', spec 10.6)";
      end if;
      return U;
   end Parse_Unit;
