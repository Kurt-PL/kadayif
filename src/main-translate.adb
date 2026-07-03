separate (Main)
   procedure Translate
     (In_Path  : String;
      Out_Path : String;
      Emit     : Boolean;
      Flags    : String;
      Errors   : out Natural)
   is
      Unit    : Kurt.Parser.Translation_Unit;
      Visited : Unbounded_String;   --  space-bracketed canonical paths

      --  §10.3 the crate-wide namespace tables. Kurt has no crate/package
      --  federation — every `@add`-ed source unit lives in ONE flat
      --  compilation, so both tables are simply global: each canonical file
      --  is assigned one mangling prefix (implementation-defined; derived
      --  from its file name here) the first time it is loaded, and every
      --  `@add ... as name;` site anywhere in the graph registers `name` as
      --  an alias for that prefix. A name reused for a different target is
      --  permitted (not a TF — the spec does not constrain cross-file alias
      --  uniqueness); the first registration for that name wins.
      Canon_Paths    : Kurt.Parser.Path_Segments.Vector;
      Canon_Prefixes : Kurt.Parser.Path_Segments.Vector;
      Alias_Names    : Kurt.Parser.Path_Segments.Vector;
      Alias_Prefixes : Kurt.Parser.Path_Segments.Vector;
      --  §10.5 `@path` prefixes seen across ALL source units: the same
      --  prefix name re-declared in another unit shall carry an identical
      --  base path; a mismatch is a translation failure.
      Seen_Path_Names : Kurt.Parser.Path_Segments.Vector;
      Seen_Path_Bases : Kurt.Parser.Path_Segments.Vector;

      --  Lex (seeding command-line flags) and parse one source file.
      function Parse_One (Path : String)
        return Kurt.Parser.Translation_Unit
      is
         Source : constant String := Read_File (Path);
         Lex    : Kurt.Lexer.Lexer;
         Start  : Natural := Flags'First;
      begin
         Kurt.Lexer.Init (Lex, Source);
         --  §10.7 external (command-line) flags apply to every source unit.
         for I in Flags'Range loop
            if Flags (I) = ' ' then
               if I > Start then
                  Kurt.Lexer.Define_Flag (Lex, Flags (Start .. I - 1));
               end if;
               Start := I + 1;
            end if;
         end loop;
         if Flags'Last >= Start then
            Kurt.Lexer.Define_Flag (Lex, Flags (Start .. Flags'Last));
         end if;
         return Kurt.Parser.Parse_Unit (Lex);
      end Parse_One;

      --  Derive a mangling prefix from Canon's file name: strip directory
      --  and extension, replace any non-identifier byte with '_', and
      --  disambiguate against an already-assigned prefix by appending a
      --  running number (two files named the same in different directories
      --  are unlikely but not prohibited).
      function Compute_Prefix (Canon : String) return String is
         Raw : constant String := Dir.Base_Name (Canon);
         Buf : String (Raw'Range) := Raw;
      begin
         for I in Buf'Range loop
            if not (Buf (I) in 'a' .. 'z' or else Buf (I) in 'A' .. 'Z'
                    or else Buf (I) in '0' .. '9' or else Buf (I) = '_')
            then
               Buf (I) := '_';
            end if;
         end loop;
         declare
            Base : constant String :=
              (if Buf'Length = 0 or else Buf (Buf'First) in '0' .. '9'
               then "u" & Buf else Buf);
            Candidate : Unbounded_String := To_Unbounded_String (Base);
            N         : Natural := 1;
         begin
            loop
               declare
                  Clash : Boolean := False;
               begin
                  for I in Canon_Prefixes.First_Index ..
                           Canon_Prefixes.Last_Index loop
                     if Kurt.Parser.SU."="
                          (Canon_Prefixes.Element (I), Candidate)
                     then
                        Clash := True;
                        exit;
                     end if;
                  end loop;
                  exit when not Clash;
               end;
               N := N + 1;
               Candidate := To_Unbounded_String (Base & Natural'Image (N));
            end loop;
            return To_String (Candidate);
         end;
      end Compute_Prefix;

      function Prefix_For_Canon (Canon : String) return String is
      begin
         for I in Canon_Paths.First_Index .. Canon_Paths.Last_Index loop
            if Kurt.Parser.SU."="
                 (Canon_Paths.Element (I), To_Unbounded_String (Canon))
            then
               return To_String (Canon_Prefixes.Element (I));
            end if;
         end loop;
         raise Program_Error with "internal: no prefix registered for "
           & Canon;
      end Prefix_For_Canon;

      --  §10.2 parse Path, recursively pull in its `@add` imports (resolved
      --  relative to Path's directory, deduplicated by canonical name),
      --  namespace-mangle each import under its chosen alias (§10.3), and
      --  merge every unit's declarations into Unit. `Is_Root` marks the
      --  top-level file being translated directly: unlike an `@add`-ed
      --  unit, its own declarations are never namespace-mangled (there is
      --  no `as name;` site for it — it IS the crate).
      procedure Load (Path : String; Is_Root : Boolean := False) is
         Canon : constant String := Dir.Full_Name (Path);
         U     : Kurt.Parser.Translation_Unit;
      begin
         if Index (Visited, " " & Canon & " ") /= 0 then
            return;   --  already parsed and merged
         end if;
         Append (Visited, Canon & " ");
         declare
            Prefix : constant String := Compute_Prefix (Canon);
         begin
            Canon_Paths.Append (To_Unbounded_String (Canon));
            Canon_Prefixes.Append (To_Unbounded_String (Prefix));
            U := Parse_One (Path);
            --  §10.5 cross-unit `@path` consistency: the same prefix name
            --  declared in more than one source unit shall have identical
            --  base paths.
            for I in U.Path_Names.First_Index .. U.Path_Names.Last_Index loop
               declare
                  Found : Boolean := False;
               begin
                  for S in Seen_Path_Names.First_Index ..
                           Seen_Path_Names.Last_Index loop
                     if Seen_Path_Names.Element (S) = U.Path_Names.Element (I)
                     then
                        Found := True;
                        if Seen_Path_Bases.Element (S)
                             /= U.Path_Bases.Element (I)
                        then
                           Put_E ("kadayif: `@path` prefix '"
                                  & To_String (U.Path_Names.Element (I))
                                  & "' re-declared with a different base "
                                  & "path (spec 10.5) in " & Path);
                           Errors := Errors + 1;
                        end if;
                     end if;
                  end loop;
                  if not Found then
                     Seen_Path_Names.Append (U.Path_Names.Element (I));
                     Seen_Path_Bases.Append (U.Path_Bases.Element (I));
                  end if;
               end;
            end loop;
            declare
               Base : constant String := Dir.Containing_Directory (Canon);
            begin
               for I in U.Adds.First_Index .. U.Adds.Last_Index loop
                  declare
                     Rel : constant String := To_String (U.Adds.Element (I));
                     Pfx : constant String :=
                       To_String (U.Add_Prefixes.Element (I));

                     --  §10.5 resolution base: a `prefix::` selects the
                     --  matching `@path` base; otherwise the importing
                     --  file's directory.
                     function Resolve_Base return String is
                     begin
                        if Pfx /= "" then
                           for P in U.Path_Names.First_Index ..
                                    U.Path_Names.Last_Index loop
                              if To_String (U.Path_Names.Element (P)) = Pfx
                              then
                                 return To_String (U.Path_Bases.Element (P));
                              end if;
                           end loop;
                           Put_E ("kadayif: unknown @path prefix '" & Pfx
                                  & "' (from " & Path & ")");
                           Errors := Errors + 1;
                           return Base;
                        end if;
                        return Base;
                     end Resolve_Base;

                     RB  : constant String := Resolve_Base;
                     Sub : constant String :=
                       (if Rel'Length > 0 and then Rel (Rel'First) = '/'
                        then Rel
                        elsif RB'Length > 0 and then RB (RB'First) = '/'
                        then RB & "/" & Rel
                        else Base & "/" & RB & "/" & Rel);
                  begin
                     if not Dir.Exists (Sub) then
                        Put_E ("kadayif: @add file not found: " & Rel
                               & " (from " & Path & ")");
                        Errors := Errors + 1;
                     else
                        Load (Sub);
                        --  §10.3 register this @add site's `as name;` as an
                        --  alias for the target's canonical prefix.
                        Alias_Names.Append (U.Add_Names.Element (I));
                        Alias_Prefixes.Append
                          (To_Unbounded_String
                             (Prefix_For_Canon (Dir.Full_Name (Sub))));
                     end if;
                  end;
               end loop;
            end;
            if not Is_Root then
               --  §10.3/§10.6 whole-file namespace pass. Module-mangled
               --  declarations (`a$b$f`) are reached through their module
               --  heads (Extra_Names); a leading `srcroot` names this
               --  file's own root and is resolved here.
               declare
                  Heads : Kurt.Parser.Path_Segments.Vector;
               begin
                  for M of U.Module_Names loop
                     declare
                        S      : constant String := To_String (M);
                        Dollar : Natural := 0;
                        Dup    : Boolean := False;
                     begin
                        for I in S'Range loop
                           if S (I) = '$' then
                              Dollar := I;
                              exit;
                           end if;
                        end loop;
                        declare
                           H : constant String :=
                             (if Dollar = 0 then S
                              else S (S'First .. Dollar - 1));
                        begin
                           for E of Heads loop
                              if To_String (E) = H then
                                 Dup := True;
                              end if;
                           end loop;
                           if not Dup then
                              Heads.Append (To_Unbounded_String (H));
                           end if;
                        end;
                     end;
                  end loop;
                  Kurt.Parser.Apply_Namespace
                    (U, Prefix, Extra_Names => Heads,
                     Super_Word => "srcroot");
               end;
               --  The file prefix folds into every module alias.
               for I in U.Module_Names.First_Index ..
                        U.Module_Names.Last_Index loop
                  U.Module_Names.Replace_Element
                    (I, To_Unbounded_String
                          (Prefix & "$"
                           & To_String (U.Module_Names.Element (I))));
               end loop;
            end if;
            --  §10.6 every module prefix is its own namespace alias
            --  (`a::b::item` collapses stepwise to `a$b$item`).
            for M of U.Module_Names loop
               Alias_Names.Append (M);
               Alias_Prefixes.Append (M);
            end loop;
            Kurt.Parser.Merge_Unit (Unit, U);
         end;
      end Load;
   begin
      Visited := To_Unbounded_String (" ");
      Errors := 0;
      Load (In_Path, Is_Root => True);
      if Errors > 0 then
         return;   --  missing imports; do not proceed to sema/codegen
      end if;
      --  §10.4 `@dyn as name { ... }` is a namespace exactly like `@add`
      --  (its `as` clause is likewise mandatory, spec 10.4): each prototype
      --  is looked up on the Kurt side as `name$item`, registered as an
      --  alias `name -> name` so `Resolve_Aliases` collapses `name::item`
      --  call sites to match. The *external link symbol* is untouched — a
      --  `@dyn` prototype's `Symbol_Name` (empty = "derive from the
      --  identifier") is pinned to the ORIGINAL bare identifier first, so
      --  mangling the Kurt-side name never changes what gets linked.
      for I in Unit.Dyns.First_Index .. Unit.Dyns.Last_Index loop
         declare
            D : Kurt.Parser.Dyn_Decl := Unit.Dyns.Element (I);
         begin
            for J in D.Items.First_Index .. D.Items.Last_Index loop
               declare
                  P : Kurt.Parser.Fn_Proto := D.Items.Element (J);
               begin
                  if Length (P.Symbol_Name) = 0 then
                     P.Symbol_Name := P.Name;
                  end if;
                  P.Name := D.Alias & "$" & P.Name;
                  D.Items.Replace_Element (J, P);
               end;
            end loop;
            Unit.Dyns.Replace_Element (I, D);
            Alias_Names.Append (D.Alias);
            Alias_Prefixes.Append (D.Alias);
         end;
      end loop;
      --  §10.3/§10.4 resolve every `alias::item` reference anywhere in the
      --  fully merged unit against the alias table built above.
      Kurt.Parser.Resolve_Aliases (Unit, Alias_Names, Alias_Prefixes);
      --  Built-in types verdict (§4.5) and the ranges (§4.8) are intrinsic —
      --  recognised by name/structure in Kurt.Layout like the primitives, not
      --  monomorphised here.
      Kurt.Mono.Monomorphize (Unit);   --  section 5.9.3 specialise generics
      Kurt.Layout.Register (Unit);     --  section 4.11 KSA layout
      Kurt.Sema.Check (Unit, Errors);  --  section 10.2 stages 3-4
      --  §9.9.3: Kurt.Sema completes each anonymous closure-capture struct
      --  (filling field types from the creating scope); re-register so codegen
      --  sees the finalised layout.
      Kurt.Layout.Register (Unit);
      if Errors = 0 and then Emit then
         Kurt.Codegen.Emit (Unit, Out_Path);   --  section 10.2 stage 5
      end if;
   end Translate;
