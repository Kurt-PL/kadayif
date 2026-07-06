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

      --  §10.2/§10.3 every `@add`-ed source unit lives in ONE flat
      --  compilation: each canonical file is assigned one mangling prefix
      --  (implementation-defined; derived from its file name here) the
      --  first time it is loaded.
      Canon_Paths    : Kurt.Parser.Path_Segments.Vector;
      Canon_Prefixes : Kurt.Parser.Path_Segments.Vector;

      --  §10.3 `@add pub` / §10.4 `@dyn pub` re-export registry:
      --  (Export_Owner, Export_Name, Export_Target) triples. Populated once
      --  per loaded file (keyed by its OWN assigned prefix) with every
      --  alias it makes directly usable, bare, by its importers -- a
      --  `@add pub ... as name;` or `@dyn pub as name {...}` site it
      --  declares itself, plus anything it in turn inherited from one of
      --  ITS OWN pub-marked imports. Propagation is transitive and, once
      --  granted, permanent ("pub is viral": a name that reached
      --  visibility through one `pub` link keeps propagating through
      --  further `@add`s regardless of whether those further sites are
      --  themselves marked `pub` -- see Load's `@add` loop). A name never
      --  added here (i.e. every alias by default) stays strictly private
      --  to the one source unit that declared it -- this is §10.3's
      --  alias-privacy rule, and the entire reason the OLD flat/global
      --  alias table was wrong: every `@add ... as name;` site anywhere in
      --  the graph used to register `name` unconditionally, so a private
      --  alias in one file silently leaked into (and could shadow/collide
      --  with) every other file's resolution.
      Export_Owner  : Kurt.Parser.Path_Segments.Vector;
      Export_Name   : Kurt.Parser.Path_Segments.Vector;
      Export_Target : Kurt.Parser.Path_Segments.Vector;

      --  §10.6 flat, whole-programme registry of every `module`'s fully
      --  mangled namespace prefix (e.g. "geoPrefix$shapes") and whether it
      --  was declared `pub module`. Unlike `@add pub`/`@dyn pub` above, a
      --  module's mangled prefix is already globally unique (composed from
      --  its owning file's own mangling prefix), so there is no need to
      --  hand-propagate it through each importer's local alias table: it
      --  is instead checked directly, the moment a collapse step's head
      --  matches it, by Kurt.Parser.Resolve_Aliases's Prefix_Of. A
      --  cross-unit qualified access always reaches a module through an
      --  ordinary `@add` alias first (`fileAlias::modname::item`, per
      --  spec 10.6's own examples) -- this registry gates only the second
      --  (module) segment.
      NS_Names : Kurt.Parser.Path_Segments.Vector;
      NS_Pubs  : Kurt.Parser.Bool_Vectors.Vector;

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
            --  §10.3 this file's OWN per-source-unit alias table (see the
            --  design note above Kurt.Parser.Resolve_Aliases): every name
            --  usable, bare, from WITHIN this file's own source text --
            --  its own `@add`/`@dyn` sites (regardless of `pub` -- a unit
            --  always sees its own declarations) and its own `module`
            --  namespaces (self-mapped, likewise unconditional), plus
            --  anything transitively inherited from a `pub`-marked import.
            Local_Names    : Kurt.Parser.Path_Segments.Vector;
            Local_Prefixes : Kurt.Parser.Path_Segments.Vector;
         begin
            Canon_Paths.Append (To_Unbounded_String (Canon));
            Canon_Prefixes.Append (To_Unbounded_String (Prefix));
            U := Parse_One (Path);
            if not Is_Root then
               --  §5.5.1/§6.2.2 non-`pub` visibility, and §10.4's same-
               --  source-unit `@dyn` exemption: registered up front (rather
               --  than after Apply_Namespace, as before the per-unit
               --  refactor) so Resolve_Aliases below can already tell this
               --  unit apart from others while it runs.
               Kurt.Layout.Register_File_Prefix (Prefix);
            end if;
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
            --  §10.6 this file's own `module` namespaces: self-mapped local
            --  aliases (unprefixed, matching how Close_Module left them),
            --  so an in-file qualified reference `modname::item` collapses
            --  through the SAME alias machinery as an `@add`. A `pub
            --  module`'s eventual fully mangled prefix is also registered
            --  into the cross-unit namespace registry -- computed directly
            --  here (Prefix & "$" & name) rather than waiting for
            --  Apply_Namespace below; the formula is the same one
            --  Apply_Namespace itself applies to this same name.
            for MI in U.Module_Names.First_Index ..
                      U.Module_Names.Last_Index loop
               Local_Names.Append (U.Module_Names.Element (MI));
               Local_Prefixes.Append (U.Module_Names.Element (MI));
               if not Is_Root then
                  NS_Names.Append
                    (To_Unbounded_String
                       (Prefix & "$"
                        & To_String (U.Module_Names.Element (MI))));
                  NS_Pubs.Append (U.Module_Pubs.Element (MI));
               end if;
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
                        --  alias for the target's canonical prefix, USABLE
                        --  ONLY FROM THIS FILE -- Local_Names/Local_Prefixes
                        --  are this Load call's own locals, never shared
                        --  with any other file's resolution.
                        declare
                           Target_Prefix : constant String :=
                             Prefix_For_Canon (Dir.Full_Name (Sub));
                           Nm          : constant Unbounded_String :=
                             U.Add_Names.Element (I);
                           Is_Pub_Site : constant Boolean :=
                             U.Add_Pubs.Element (I);
                           --  Snapshot: iterate only entries that existed
                           --  BEFORE this site's own inheritance loop below
                           --  appends more (avoids scanning what we just
                           --  added, which would re-derive nothing new but
                           --  must not become an unbounded/self-referential
                           --  scan).
                           Snap : constant Natural :=
                             Natural (Export_Owner.Length);
                        begin
                           Local_Names.Append (Nm);
                           Local_Prefixes.Append
                             (To_Unbounded_String (Target_Prefix));
                           if Is_Pub_Site then
                              Export_Owner.Append
                                (To_Unbounded_String (Prefix));
                              Export_Name.Append (Nm);
                              Export_Target.Append
                                (To_Unbounded_String (Target_Prefix));
                           end if;
                           --  §10.3 `@add pub` re-export propagation: any
                           --  name Target_Prefix's own file already exports
                           --  becomes usable, bare, in THIS file too, and
                           --  (transitively -- once granted, `pub`
                           --  propagation is permanent regardless of a
                           --  further `@add` site's own `pub` flag) is
                           --  re-exported onward from this file as well.
                           for K in 1 .. Snap loop
                              if To_String (Export_Owner.Element (K))
                                   = Target_Prefix
                              then
                                 Local_Names.Append
                                   (Export_Name.Element (K));
                                 Local_Prefixes.Append
                                   (Export_Target.Element (K));
                                 Export_Owner.Append
                                   (To_Unbounded_String (Prefix));
                                 Export_Name.Append
                                   (Export_Name.Element (K));
                                 Export_Target.Append
                                   (Export_Target.Element (K));
                              end if;
                           end loop;
                        end;
                     end if;
                  end;
               end loop;
            end;
            --  §10.4 `@dyn as name { ... }` is a namespace exactly like
            --  `@add` (its `as` clause is likewise mandatory, spec 10.4):
            --  each prototype is renamed `[Prefix$]name$item` -- file-
            --  prefixed for a non-root unit, so Kurt.Layout.Same_Source_Unit
            --  can tell this `@dyn` block's own source unit apart from
            --  another's (spec 10.4's same-unit exemption on non-`pub`
            --  symbols) -- and registered as a self-mapped local alias so
            --  Resolve_Aliases collapses `name::item` call sites to match.
            --  The *external link symbol* is untouched — a `@dyn`
            --  prototype's `Symbol_Name` (empty = "derive from the
            --  identifier") is pinned to the ORIGINAL bare identifier
            --  first, so mangling the Kurt-side name never changes what
            --  gets linked. `@dyn pub` additionally exports the namespace
            --  identifier itself (bare) to this file's own importers.
            for I in U.Dyns.First_Index .. U.Dyns.Last_Index loop
               declare
                  D : Kurt.Parser.Dyn_Decl := U.Dyns.Element (I);
                  Qualified : constant String :=
                    (if Is_Root then To_String (D.Alias)
                     else Prefix & "$" & To_String (D.Alias));
               begin
                  for J in D.Items.First_Index .. D.Items.Last_Index loop
                     declare
                        P : Kurt.Parser.Fn_Proto := D.Items.Element (J);
                     begin
                        if Length (P.Symbol_Name) = 0 then
                           P.Symbol_Name := P.Name;
                        end if;
                        P.Name := To_Unbounded_String
                          (Qualified & "$" & To_String (P.Name));
                        D.Items.Replace_Element (J, P);
                     end;
                  end loop;
                  U.Dyns.Replace_Element (I, D);
                  Local_Names.Append (D.Alias);
                  Local_Prefixes.Append (To_Unbounded_String (Qualified));
                  if D.Is_Pub then
                     Export_Owner.Append (To_Unbounded_String (Prefix));
                     Export_Name.Append (D.Alias);
                     Export_Target.Append
                       (To_Unbounded_String (Qualified));
                  end if;
               end;
            end loop;
            --  §10.3/§10.4/§10.6 resolve this unit's OWN alias references
            --  (before it is mangled and merged) against ITS OWN per-unit
            --  table computed just above; `Unit` (the accumulator so far)
            --  already holds every dependency this unit `@add`s, fully
            --  merged (Load recurses dependency-first), so Check_Pub can
            --  already see it.
            Kurt.Parser.Resolve_Aliases
              (U, Unit, (if Is_Root then "" else Prefix),
               Local_Names, Local_Prefixes, NS_Names, NS_Pubs);
            if not Is_Root then
               --  §5.5.1/§6.2.2 non-`pub` visibility: this file's
               --  declarations all end up prefixed `Prefix$...` below, so
               --  Kurt.Layout can tell a same-source-unit access from a
               --  cross-unit one by that leading segment.
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
      --  Built-in types verdict (§4.5) and the ranges (§4.8) are intrinsic —
      --  recognised by name/structure in Kurt.Layout like the primitives, not
      --  monomorphised here.
      Kurt.Mono.Monomorphize (Unit);   --  section 5.9.3 specialise generics
      Kurt.Layout.Register (Unit);     --  section 4.11 KSA layout
      Kurt.Sema.Check (Unit, Errors);  --  section 10.2 stages 3-4
      --  §5.9.2 implicit instantiation: when Kurt.Sema inferred the type
      --  arguments of a bare generic call (writing them into the callee's
      --  P_Type_Args), run another monomorphise + register + check round
      --  so the new instances are generated and checked. Instantiated
      --  bodies may themselves contain further bare generic calls, so
      --  iterate to a fixpoint (bounded; each round only ever ADDS
      --  instances, so it terminates unless generation itself diverges).
      declare
         Rounds : Natural := 0;
      begin
         while Errors = 0 and then Unit.Needs_Mono_Rerun
           and then Rounds < 16
         loop
            Unit.Needs_Mono_Rerun := False;
            Kurt.Mono.Monomorphize (Unit);
            Kurt.Layout.Register (Unit);
            Kurt.Sema.Check (Unit, Errors);
            Rounds := Rounds + 1;
         end loop;
      end;
      --  §9.9.3: Kurt.Sema completes each anonymous closure-capture struct
      --  (filling field types from the creating scope); re-register so codegen
      --  sees the finalised layout.
      Kurt.Layout.Register (Unit);
      if Errors = 0 and then Emit then
         Kurt.Codegen.Emit (Unit, Out_Path);   --  section 10.2 stage 5
      end if;
   end Translate;
