--  Kadayif command-line entry point.
--
--  A conventional compiler command-line interface: the -h/-v/-a self-reports,
--  the -y semantic-check phase, -S assembly, -c object, and the default
--  translate-and-link to an executable.
--
--  Assembly and linking are delegated to the host `as`/`ld` through the C
--  library `system(3)`. That binding uses only standard Ada 2012 facilities
--  (Interfaces.C from Annex B plus a Convention-C Import); no GNAT-specific
--  package is used anywhere in this compiler.

with Ada.Command_Line;
with Ada.Text_IO;
with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded;
with Ada.Directories;
with Ada.Exceptions;
with Interfaces.C;

with Kurt.Lexer;
with Kurt.Parser;
with Kurt.Mono;
with Kurt.Layout;
with Kurt.Sema;
with Kurt.Codegen;

procedure Main is

   package CLI renames Ada.Command_Line;
   package IO  renames Ada.Text_IO;
   package Dir renames Ada.Directories;
   use Ada.Strings.Unbounded;

   --  Exit statuses: success / failure, with usage and internal-error codes
   --  refining "failure".
   Exit_OK       : constant := 0;
   Exit_TransErr : constant := 1;   --  translation or toolchain failure
   Exit_Usage    : constant := 2;   --  malformed / unsupported command line
   Exit_Internal : constant := 3;   --  compiler bug (unexpected exception)
   pragma Unreferenced (Exit_OK);

   Version_Line : constant String :=
     "kadayif 0.0.0-aleph.1 - Kurt bootstrap compiler (translates KPLSS 0.1)";

   --  C library system(3): run a command via the shell, return its status.
   --  Standard Ada 2012 (Annex B Interfaces.C + a Convention-C import) -
   --  not a GNAT extension.
   function C_System (Command : Interfaces.C.char_array)
     return Interfaces.C.int
     with Import, Convention => C, External_Name => "system";

   --  What the command was asked to do.
   type Mode_Kind is
     (M_Build,      --  default: translate, assemble, and link -> executable
      M_Obj,        --  -c: translate and assemble -> object, no link
      M_Asm,        --  -S: emit assembly and stop
      M_Check,      --  -y: stages 1-4 only, a full semantic check, no output
      M_Help,       --  -h: report usage
      M_Version,    --  -v: report version
      M_Licence);   --  -a: report legal status

   procedure Put_E (S : String) is
   begin
      IO.Put_Line (IO.Standard_Error, S);
   end Put_E;

   --  Run a shell command through system(3); True iff it exited 0.
   function Run (Command : String) return Boolean is
      use type Interfaces.C.int;
   begin
      return C_System (Interfaces.C.To_C (Command)) = 0;
   end Run;

   --  Shell-quote a path so spaces and most metacharacters are literal.
   function Q (S : String) return String is
      R : Unbounded_String := To_Unbounded_String ("'");
   begin
      for C of S loop
         if C = ''' then
            Append (R, "'\''");   --  close, escaped quote, reopen
         else
            Append (R, C);
         end if;
      end loop;
      Append (R, "'");
      return To_String (R);
   end Q;

   procedure Show_Version is
   begin
      IO.Put_Line (Version_Line);
   end Show_Version;

   --  `-a`: state the terms under which the utility is distributed.
   procedure Show_Licence is
   begin
      IO.Put_Line (Version_Line);
      IO.Put_Line ("");
      IO.Put_Line ("Licence: ISC. Copyright 2026 HanuL.");
      IO.Put_Line ("Full text: see the LICENCE file in the kadayif "
                   & "distribution.");
      IO.Put_Line ("Provided ""as is"" without warranty of any kind; the "
                   & "author is");
      IO.Put_Line ("not liable for any damages arising from its use.");
   end Show_Licence;

   --  `-h`: a usage summary naming every option.
   procedure Show_Usage is
   begin
      IO.Put_Line (Version_Line);
      IO.Put_Line ("");
      IO.Put_Line ("Compile a Kurt source file (arm64-apple-darwin).");
      IO.Put_Line ("");
      IO.Put_Line ("USAGE:");
      IO.Put_Line ("    kadayif [options] <input.kr>");
      IO.Put_Line ("");
      IO.Put_Line ("PHASE OPTIONS:");
      IO.Put_Line ("    (default)     Translate, assemble, and link to an "
                   & "executable.");
      IO.Put_Line ("    -c            Translate and assemble to an object "
                   & "(.o); no link.");
      IO.Put_Line ("    -S            Emit assembly and stop (.s).");
      IO.Put_Line ("    -y            Semantic check only (stages 1-4); no "
                   & "output file.");
      IO.Put_Line ("    -o <file>     Output path (default: a.out / .o / "
                   & ".s by phase).");
      IO.Put_Line ("");
      IO.Put_Line ("SELF-REPORTS (write to stdout, exit 0):");
      IO.Put_Line ("    -h, --help    Report usage.");
      IO.Put_Line ("    -v, --version Report version.");
      IO.Put_Line ("    -a, --licence Report legal status.");
      IO.Put_Line ("");
      IO.Put_Line ("PIPELINE:");
      IO.Put_Line ("    .kr -> lex -> parse -> built-ins -> mono -> layout "
                   & "-> sema -> codegen");
      IO.Put_Line ("         -> as -> ld");
      IO.Put_Line ("");
      IO.Put_Line ("NOT YET IMPLEMENTED: -E -G -O -T and other options.");
      IO.Put_Line ("");
      IO.Put_Line ("EXIT STATUS: 0 ok   1 failure   2 usage   3 internal");
   end Show_Usage;

   --  Read an entire file into a String, byte-for-byte (section 3.1).
   function Read_File (Path : String) return String is
      package SIO renames Ada.Streams.Stream_IO;
      F  : SIO.File_Type;
      L  : SIO.Count;
   begin
      SIO.Open (F, SIO.In_File, Path);
      L := SIO.Size (F);
      declare
         use Ada.Streams;
         Buf   : Stream_Element_Array (1 .. Stream_Element_Offset (L));
         Got   : Stream_Element_Offset;
         Out_S : String (1 .. Natural (L));
      begin
         SIO.Read (F, Buf, Got);
         SIO.Close (F);
         for I in Out_S'Range loop
            Out_S (I) := Character'Val (Buf (Stream_Element_Offset (I)));
         end loop;
         return Out_S;
      end;
   end Read_File;

   --  Strip a trailing ".kr" from a source path (its stem).
   function Stem (Input : String) return String is
   begin
      if Input'Length >= 3
        and then Input (Input'Last - 2 .. Input'Last) = ".kr"
      then
         return Input (Input'First .. Input'Last - 3);
      else
         return Input;
      end if;
   end Stem;

   --  Front + middle ends, then codegen when Emit. Returns the sema error
   --  count; lexer/parser failures propagate to the outer handler.
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

   --  Delete a temporary intermediate, ignoring absence.
   procedure Cleanup (Path : String) is
   begin
      if Dir.Exists (Path) then
         Dir.Delete_File (Path);
      end if;
   exception
      when others => null;
   end Cleanup;

   Mode     : Mode_Kind := M_Build;
   In_Path  : Unbounded_String;
   Out_Path : Unbounded_String;
   --  §10.7 translation-time flags from `-f NAME` options (space-delimited).
   Cmd_Flags : Unbounded_String;

begin
   ----------------------------------------------------------------------
   --  Command-line parsing. Each option is given separately; option
   --  grouping (e.g. -cS) is not recognised.
   ----------------------------------------------------------------------
   declare
      I : Natural := 1;

      --  Options the interface reserves but this bootstrap does not yet
      --  perform.
      function Is_Unsupported (A : String) return Boolean is
        (A = "-E" or else A = "-G" or else A = "-g" or else A = "-s"
         or else A = "-w" or else A = "-Werror" or else A = "-Wno-error"
         or else (A'Length >= 2
                  and then A (A'First) = '-'
                  and then A (A'First + 1) in
                    'O' | 'T' | 'K' | 'Q' | 'f' | 'B' | 'e' | 'n'
                    | 'F' | 'U' | 'X' | 'L' | 'l' | 'R'));
   begin
      while I <= CLI.Argument_Count loop
         declare
            A : constant String := CLI.Argument (I);
         begin
            if A = "-f" then
               --  §10.7 define a translation-time flag.
               if I = CLI.Argument_Count then
                  Put_E ("kadayif: -f requires a flag name");
                  CLI.Set_Exit_Status (Exit_Usage);
                  return;
               end if;
               I := I + 1;
               Append (Cmd_Flags, CLI.Argument (I) & " ");
            elsif A = "-o" then
               if I = CLI.Argument_Count then
                  Put_E ("kadayif: -o requires an output path");
                  CLI.Set_Exit_Status (Exit_Usage);
                  return;
               end if;
               I := I + 1;
               Out_Path := To_Unbounded_String (CLI.Argument (I));
            elsif A = "-c" then
               Mode := M_Obj;
            elsif A = "-S" then
               Mode := M_Asm;
            elsif A = "-y" then
               Mode := M_Check;
            elsif A = "-h" or else A = "--help" then
               Mode := M_Help;
            elsif A = "-v" or else A = "--version" then
               Mode := M_Version;
            elsif A = "-a" or else A = "--licence" or else A = "--license" then
               Mode := M_Licence;
            elsif Is_Unsupported (A) then
               Put_E ("kadayif: option '" & A & "' is reserved but not yet "
                      & "implemented by this bootstrap.");
               CLI.Set_Exit_Status (Exit_Usage);
               return;
            elsif A'Length >= 1 and then A (A'First) = '-' then
               Put_E ("kadayif: unknown option '" & A
                      & "' (run `kadayif -h`)");
               CLI.Set_Exit_Status (Exit_Usage);
               return;
            elsif Length (In_Path) = 0 then
               In_Path := To_Unbounded_String (A);
            else
               Put_E ("kadayif: this bootstrap accepts a single source "
                      & "operand; unexpected '" & A & "'");
               CLI.Set_Exit_Status (Exit_Usage);
               return;
            end if;
         end;
         I := I + 1;
      end loop;
   end;

   ----------------------------------------------------------------------
   --  Self-reports: no source operand required; exit success.
   ----------------------------------------------------------------------
   case Mode is
      when M_Help    => Show_Usage;   return;
      when M_Version => Show_Version; return;
      when M_Licence => Show_Licence; return;
      when others    => null;
   end case;

   ----------------------------------------------------------------------
   --  Translation modes require a source operand.
   ----------------------------------------------------------------------
   if Length (In_Path) = 0 then
      Put_E ("kadayif: no input file (run `kadayif -h`)");
      CLI.Set_Exit_Status (Exit_Usage);
      return;
   end if;

   if not Dir.Exists (To_String (In_Path)) then
      Put_E ("kadayif: input file not found: " & To_String (In_Path));
      CLI.Set_Exit_Status (Exit_TransErr);
      return;
   end if;

   declare
      In_S   : constant String := To_String (In_Path);
      Base   : constant String := Stem (In_S);
      --  Where assembly goes: the requested artefact for -S, else a temp.
      Asm    : constant String :=
        (if Mode = M_Asm and then Length (Out_Path) > 0
            then To_String (Out_Path)
         elsif Mode = M_Asm then Base & ".s"
         else Base & ".kt.s");                 --  build/obj intermediate
      Errors : Natural := 0;
   begin
      Translate (In_S, Asm, Emit => Mode /= M_Check,
                 Flags => To_String (Cmd_Flags), Errors => Errors);

      if Errors > 0 then
         Put_E ("kadayif: aborting after" & Natural'Image (Errors)
                & " error(s)");
         Cleanup (Asm);
         CLI.Set_Exit_Status (Exit_TransErr);
         return;
      end if;

      case Mode is
         when M_Check =>
            IO.Put_Line ("kadayif: " & In_S
                         & ": no errors (semantic check passed)");

         when M_Asm =>
            IO.Put_Line ("kadayif: wrote " & Asm);

         when M_Obj =>
            declare
               Obj : constant String :=
                 (if Length (Out_Path) > 0 then To_String (Out_Path)
                  else Base & ".o");
            begin
               if not Run ("as -arch arm64 " & Q (Asm) & " -o " & Q (Obj))
               then
                  Put_E ("kadayif: assembler (as) failed");
                  Cleanup (Asm);
                  CLI.Set_Exit_Status (Exit_TransErr);
                  return;
               end if;
               Cleanup (Asm);
               IO.Put_Line ("kadayif: wrote " & Obj);
            end;

         when M_Build =>
            declare
               Obj : constant String := Base & ".kt.o";
               Exe : constant String :=
                 (if Length (Out_Path) > 0 then To_String (Out_Path)
                  else "a.out");
            begin
               if not Run ("as -arch arm64 " & Q (Asm) & " -o " & Q (Obj))
               then
                  Put_E ("kadayif: assembler (as) failed");
                  Cleanup (Asm);
                  CLI.Set_Exit_Status (Exit_TransErr);
                  return;
               end if;
               --  Link with the host SDK; the shell expands xcrun.
               if not Run ("ld " & Q (Obj)
                           & " -lSystem -syslibroot ""$(xcrun "
                           & "--show-sdk-path)"" -e _main -o " & Q (Exe))
               then
                  Put_E ("kadayif: linker (ld) failed");
                  Cleanup (Asm);
                  Cleanup (Obj);
                  CLI.Set_Exit_Status (Exit_TransErr);
                  return;
               end if;
               Cleanup (Asm);
               Cleanup (Obj);
               IO.Put_Line ("kadayif: wrote " & Exe);
            end;

         when others =>
            null;
      end case;
   end;

exception
   when E : Kurt.Lexer.Translation_Failure =>
      Put_E ("kadayif: translation failure: "
             & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (Exit_TransErr);
   when E : Kurt.Parser.Syntax_Error =>
      Put_E ("kadayif: syntax error: "
             & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (Exit_TransErr);
   when E : Kurt.Layout.Layout_Error =>
      Put_E ("kadayif: translation failure: "
             & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (Exit_TransErr);
   when E : Kurt.Mono.Mono_Error =>
      --  §5.9 generic-instantiation errors (e.g. wrong type-argument count)
      --  are user translation failures, not compiler bugs.
      Put_E ("kadayif: translation failure: "
             & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (Exit_TransErr);
   when E : others =>
      Put_E ("kadayif: internal error: "
             & Ada.Exceptions.Exception_Information (E));
      CLI.Set_Exit_Status (Exit_Internal);
end Main;
