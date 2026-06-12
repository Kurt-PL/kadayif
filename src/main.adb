with Ada.Command_Line;
with Ada.Text_IO;
with Ada.Streams.Stream_IO;
with Ada.Strings.Unbounded;
with Ada.Directories;
with Ada.Exceptions;

with Kurt.Lexer;
with Kurt.Parser;
with Kurt.Mono;
with Kurt.Layout;
with Kurt.Sema;
with Kurt.Codegen;

procedure Main is

   package CLI renames Ada.Command_Line;
   package IO  renames Ada.Text_IO;

   procedure Usage is
   begin
      IO.Put_Line (IO.Standard_Error,
        "usage: kadayif <input.kr> [-o <output.s>]");
      IO.Put_Line (IO.Standard_Error,
        "  L0 bootstrap: accepts only `fn NAME() -> ui1 { return N; }`.");
   end Usage;

   --  Read an entire file into a String, byte-for-byte.
   function Read_File (Path : String) return String is
      package SIO renames Ada.Streams.Stream_IO;
      F  : SIO.File_Type;
      L  : SIO.Count;
   begin
      SIO.Open (F, SIO.In_File, Path);
      L := SIO.Size (F);
      declare
         use Ada.Streams;
         Buf : Stream_Element_Array (1 .. Stream_Element_Offset (L));
         Got : Stream_Element_Offset;
         Out_S : String (1 .. Natural (L));
      begin
         SIO.Read (F, Buf, Got);
         SIO.Close (F);
         for I in Out_S'Range loop
            Out_S (I) := Character'Val
              (Buf (Stream_Element_Offset (I)));
         end loop;
         return Out_S;
      end;
   end Read_File;

   --  Replace the trailing ".kr" extension with ".s". If no .kr suffix,
   --  just append ".s".
   function Default_Out_Path (Input : String) return String is
   begin
      if Input'Length >= 3
        and then Input (Input'Last - 2 .. Input'Last) = ".kr"
      then
         return Input (Input'First .. Input'Last - 3) & ".s";
      else
         return Input & ".s";
      end if;
   end Default_Out_Path;

   In_Path  : Ada.Strings.Unbounded.Unbounded_String;
   Out_Path : Ada.Strings.Unbounded.Unbounded_String;
   use Ada.Strings.Unbounded;

begin
   --  Argument parsing
   declare
      I : Natural := 1;
   begin
      while I <= CLI.Argument_Count loop
         declare
            A : constant String := CLI.Argument (I);
         begin
            if A = "-o" then
               if I = CLI.Argument_Count then
                  Usage;
                  CLI.Set_Exit_Status (2);
                  return;
               end if;
               I := I + 1;
               Out_Path := To_Unbounded_String (CLI.Argument (I));
            elsif A = "-h" or else A = "--help" then
               Usage;
               return;
            elsif Length (In_Path) = 0 then
               In_Path := To_Unbounded_String (A);
            else
               IO.Put_Line (IO.Standard_Error,
                 "kadayif: unexpected extra argument: " & A);
               Usage;
               CLI.Set_Exit_Status (2);
               return;
            end if;
         end;
         I := I + 1;
      end loop;
   end;

   if Length (In_Path) = 0 then
      Usage;
      CLI.Set_Exit_Status (2);
      return;
   end if;

   if not Ada.Directories.Exists (To_String (In_Path)) then
      IO.Put_Line (IO.Standard_Error,
        "kadayif: input file not found: " & To_String (In_Path));
      CLI.Set_Exit_Status (1);
      return;
   end if;

   if Length (Out_Path) = 0 then
      Out_Path := To_Unbounded_String
        (Default_Out_Path (To_String (In_Path)));
   end if;

   ----------------------------------------------------------------------
   --  Pipeline: read → lex → parse → emit
   ----------------------------------------------------------------------
   declare
      --  Implicit prelude: the built-in contract enum verdict.<T, F>
      --  (§4.5). `Pass = 1` is the success (truthy) variant; `Fail` is the
      --  `#wild#` failure variant. Monomorphisation drops it if unused.
      --
      --  Spec form (§4.5): tuple-variant payload (`Pass { pub T }`,
      --  positional) with a `with { contract -> self_t.<F, T>, discrim(ui1) }`
      --  block. The bootstrap recognises the tuple-variant payload and the
      --  with-block; the `-> inverted_pair_type` part is parsed-and-discarded
      --  (so `!verdict` is not yet usable). `pub` modifiers on payload
      --  fields are also discarded.
      Prelude : constant String :=
        "enum verdict.<T, F> { Pass { pub T } = 1, "
        & "Fail { pub F } = #wild#(0) } with { "
        & "contract -> self_t.<F, T>, discrim(ui1) }"
        & ASCII.LF;
      Source : constant String :=
        Prelude & Read_File (To_String (In_Path));
      Lex    : Kurt.Lexer.Lexer;
      Unit   : Kurt.Parser.Translation_Unit;
   begin
      Kurt.Lexer.Init (Lex, Source);
      Unit := Kurt.Parser.Parse_Unit (Lex);
      Kurt.Mono.Monomorphize (Unit);   --  §5.8.1: specialise generic types
      Kurt.Layout.Register (Unit);

      declare
         Errors : Natural;
      begin
         Kurt.Sema.Check (Unit, Errors);
         if Errors > 0 then
            IO.Put_Line (IO.Standard_Error,
              "kadayif: aborting after"
              & Natural'Image (Errors) & " type error(s)");
            CLI.Set_Exit_Status (1);
            return;
         end if;
      end;

      Kurt.Codegen.Emit (Unit, To_String (Out_Path));
      IO.Put_Line ("kadayif: wrote " & To_String (Out_Path));
   end;

exception
   when E : Kurt.Lexer.Translation_Failure =>
      IO.Put_Line (IO.Standard_Error,
        "kadayif: translation failure: "
        & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (1);
   when E : Kurt.Parser.Syntax_Error =>
      IO.Put_Line (IO.Standard_Error,
        "kadayif: syntax error: "
        & Ada.Exceptions.Exception_Message (E));
      CLI.Set_Exit_Status (1);
   when E : others =>
      IO.Put_Line (IO.Standard_Error,
        "kadayif: internal error: "
        & Ada.Exceptions.Exception_Information (E));
      CLI.Set_Exit_Status (3);
end Main;
