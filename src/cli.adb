with Ada.Command_Line;
with Ada.Directories;
with Ada.Strings.Unbounded;
with Ada.Text_IO;
with Diagnostics;
with Pipeline;

package body CLI is

   package CL renames Ada.Command_Line;
   package IO renames Ada.Text_IO;
   use Ada.Strings.Unbounded;
   use type Pipeline.Stop_After;

   Target_Name : constant String := "aarch64-apple";

   procedure Usage is
   begin
      IO.Put_Line ("usage: kadayif [options...] file.kr");
      IO.Put_Line ("");
      IO.Put_Line ("Options marked * are not implemented yet and fail.");
      IO.Put_Line ("  -c              *translate to an object representation");
      IO.Put_Line ("  -y               analyse only, no output");
      IO.Put_Line ("  -S               write instruction output (.s)");
      IO.Put_Line ("  -V               report version");
      IO.Put_Line ("  -a               report legal status");
      IO.Put_Line ("  -h               report usage");
      IO.Put_Line ("  -o outfile       name the output file");
      IO.Put_Line ("  -G              *produce a dynamic library");
      IO.Put_Line ("  -g              *position-independent code");
      IO.Put_Line ("  -d              *debugging information");
      IO.Put_Line ("  -s              *strip symbols");
      IO.Put_Line ("  -T target        programme machine environment: "
                   & Target_Name);
      IO.Put_Line ("  -e encoding     *character data encoding (UTF-8)");
      IO.Put_Line ("  -O level        *optimisation level");
      IO.Put_Line ("  -Q key=value    *resource constraint");
      IO.Put_Line ("  -f name         *implementation feature");
      IO.Put_Line ("  -B mode         *linkage mode");
      IO.Put_Line ("  -L dir          *library search path");
      IO.Put_Line ("  -l name         *link a library");
      IO.Put_Line ("  -R dir          *runtime library search path");
      IO.Put_Line ("  -i script       *linker script");
      IO.Put_Line ("  -K version       KPLSS edition: 0.1");
      IO.Put_Line ("  -w name         *toggle a warning");
      IO.Put_Line ("  -v level        *least severity written");
      IO.Put_Line ("  -F name         *set a flag");
      IO.Put_Line ("  -U name         *unset a flag");
      IO.Put_Line ("  -P prefix=path  *declare a path prefix");
   end Usage;

   procedure Version is
   begin
      IO.Put_Line ("kadayif 0.0.0-aleph-1");
      IO.Put_Line ("KPLSS editions: 0.1");
      IO.Put_Line ("KCSS: preliminary edition 1 (draft)");
   end Version;

   procedure Legal is
   begin
      IO.Put_Line ("kadayif is distributed under the ISC licence.");
      IO.Put_Line ("Full text: LICENCE in the kadayif source distribution,"
                   & " https://github.com/Kurt-PL/kadayif");
      IO.Put_Line ("It is provided ""as is"", without warranty of any kind;"
                   & " the authors are not liable for any damages.");
   end Legal;

   procedure Run is
      Check_Only, Assembly, Reported : Boolean := False;
      Output  : Unbounded_String;
      Inputs  : Natural := 0;
      Input   : Unbounded_String;
      I       : Positive := 1;
      Failed  : Boolean := False;

      procedure Halt (Message : String) is
      begin
         Diagnostics.Report (Diagnostics.Halt, Message);
         Failed := True;
      end Halt;

      --  -o file 과 -ofile 을 모두 받는다
      function Operand (Arg : String) return String is
      begin
         if Arg'Length > 2 then
            return Arg (Arg'First + 2 .. Arg'Last);
         elsif I < CL.Argument_Count then
            I := I + 1;
            return CL.Argument (I);
         end if;
         Halt ("option " & Arg & " needs an operand");
         return "";
      end Operand;

      procedure Unimplemented_Option (Arg : String; Clause : String) is
      begin
         Diagnostics.Report
           (Diagnostics.Error,
            "unimplemented: option " & Arg (Arg'First .. Arg'First + 1)
            & " (KCSS " & Clause & ")");
         Failed := True;
      end Unimplemented_Option;

   begin
      while I <= CL.Argument_Count loop
         declare
            Arg : constant String := CL.Argument (I);
         begin
            if Arg'Length >= 2 and then Arg (Arg'First) = '-' then
               case Arg (Arg'First + 1) is
                  when 'y' => Check_Only := True;
                  when 'S' => Assembly := True;
                  when 'V' => Version; Reported := True;
                  when 'a' => Legal; Reported := True;
                  when 'h' => Usage; Reported := True;
                  when 'o' => Output := To_Unbounded_String (Operand (Arg));
                  when 'T' =>
                     if Operand (Arg) /= Target_Name then
                        Halt ("unsupported target; supported: "
                              & Target_Name);
                     end if;
                  when 'K' =>
                     if Operand (Arg) /= "0.1" then
                        Halt ("unsupported KPLSS edition; supported: 0.1");
                     end if;
                  when 'c' => Unimplemented_Option (Arg, "§4.1");
                  when 'G' | 'g' | 'd' | 's' =>
                     Unimplemented_Option (Arg, "§4.3");
                  when 'e' =>
                     Unimplemented_Option (Arg, "§4.5");
                  when 'O' =>
                     Unimplemented_Option (Arg, "§4.6");
                  when 'Q' =>
                     Unimplemented_Option (Arg, "§4.7");
                  when 'f' =>
                     Unimplemented_Option (Arg, "§4.8");
                  when 'B' | 'L' | 'l' | 'R' | 'i' =>
                     Unimplemented_Option (Arg, "§4.9");
                  when 'w' | 'v' =>
                     Unimplemented_Option (Arg, "§4.11");
                  when 'F' | 'U' =>
                     Unimplemented_Option (Arg, "§4.12");
                  when 'P' =>
                     Unimplemented_Option (Arg, "§4.13");
                  when others =>
                     Halt ("unknown option " & Arg);
               end case;
            elsif Arg = "-" then
               Unimplemented_Option ("- ", "§5, standard input");
            else
               Inputs := Inputs + 1;
               Input := To_Unbounded_String (Arg);
            end if;
         end;
         I := I + 1;
      end loop;

      if Reported and then Inputs = 0 and then not Failed then
         return;
      elsif Failed then
         CL.Set_Exit_Status (CL.Failure);
         return;
      elsif Inputs = 0 then
         Halt ("no input; see -h");
      elsif Inputs > 1 then
         Diagnostics.Report
           (Diagnostics.Error,
            "unimplemented: more than one pathname operand (KCSS §5)");
         Failed := True;
      end if;
      if Failed then
         CL.Set_Exit_Status (CL.Failure);
         return;
      end if;

      declare
         Path : constant String := To_String (Input);
         Base : constant String := Ada.Directories.Base_Name (Path);
         Stop : constant Pipeline.Stop_After :=
           (if Check_Only then Pipeline.Analysis
            elsif Assembly then Pipeline.Instructions
            else Pipeline.Artefact);
         Out_Path : constant String :=
           (if Length (Output) > 0 then To_String (Output)
            elsif Stop = Pipeline.Instructions then Base & ".s"
            else "a.out");
      begin
         if Ada.Directories.Extension (Path) /= "kr" then
            Diagnostics.Report
              (Diagnostics.Error,
               "unimplemented: operands other than file.kr (KCSS §5)");
            CL.Set_Exit_Status (CL.Failure);
         elsif not Pipeline.Translate (Path, Out_Path, Stop) then
            CL.Set_Exit_Status (CL.Failure);
         end if;
      end;
   end Run;

end CLI;
