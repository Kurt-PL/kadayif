with AArch64;
with AST;
with Ada.Directories;
with Ada.Environment_Variables;
with Ada.Text_IO;
with Apple_Arm64;
with Check;
with Diagnostics;
with Emit;
with GNAT.OS_Lib;
with Parser;
with Source_Map;
with Strip;
with Targets;

package body Pipeline is

   use type Source_Map.Source_Id;

   function Write_File (Path, Contents : String) return Boolean is
      use Ada.Text_IO;
      F : File_Type;
   begin
      Create (F, Out_File, Path);
      Put (F, Contents);
      Close (F);
      return True;
   exception
      when others =>
         Diagnostics.Report (Diagnostics.Halt, "cannot write '" & Path & "'");
         return False;
   end Write_File;

   --  자체 어셈블러·링커가 생기기 전까지 시스템 cc에 맡긴다
   function Link (Assembly, Output : String) return Boolean is
      use GNAT.OS_Lib;
      Tmp_Dir : constant String :=
        (if Ada.Environment_Variables.Exists ("TMPDIR")
         then Ada.Environment_Variables.Value ("TMPDIR") else "/tmp");
      Pid  : constant String :=
        Integer'Image (Pid_To_Integer (Current_Process_Id));
      Tmp  : constant String := Ada.Directories.Compose
        (Tmp_Dir, "kadayif-" & Pid (Pid'First + 1 .. Pid'Last) & ".s");
      CC   : String_Access := Locate_Exec_On_Path ("cc");
      Args : Argument_List_Access;
      OK, Deleted : Boolean;
   begin
      if CC = null then
         Diagnostics.Report
           (Diagnostics.Halt, "cannot find 'cc' to assemble and link");
         return False;
      end if;
      if not Write_File (Tmp, Assembly) then
         Free (CC);
         return False;
      end if;
      Args := Argument_String_To_List ("-arch arm64 -o " & Output & " " & Tmp);
      Spawn (CC.all, Args.all, OK);
      Free (Args);
      Free (CC);
      Delete_File (Tmp, Success => Deleted);
      if not OK then
         Diagnostics.Report (Diagnostics.Error, "link edit failed");
      end if;
      return OK;
   end Link;

   function Translate
     (Input : String; Output : String; Stop : Stop_After) return Boolean
   is
      Id   : constant Source_Map.Source_Id := Source_Map.Load (Input);
      Unit : AST.Node_Id;
   begin
      if Id = Source_Map.No_Source then
         Diagnostics.Report (Diagnostics.Halt, "cannot read '" & Input & "'");
         return False;
      end if;

      --  1단계: 소스 처리. 2단계(#add 수집)는 #add를 아직 받지 않으므로
      --  할 일이 없다.
      Unit := Parser.Parse (Strip.Run (Id));

      --  3, 4단계
      if Diagnostics.Failures = 0 then
         Check.Collect (Unit);
         Check.Analyse (Unit);
      end if;
      if Diagnostics.Failures > 0 then
         return False;
      elsif Stop = Analysis then
         return True;
      end if;

      --  5단계
      declare
         M    : AArch64.Machine := AArch64.Create (Targets.Format_MachO);
         ABI  : Apple_Arm64.Convention;
         Text : constant String := Emit.Generate (Unit, M, ABI);
      begin
         if Diagnostics.Failures > 0 then
            return False;
         elsif Stop = Instructions then
            return Write_File (Output, Text);
         end if;
         return Link (Text, Output);
      end;
   end Translate;

end Pipeline;
