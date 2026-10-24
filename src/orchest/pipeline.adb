with AArch64;
with AST;
with Ada.Environment_Variables;
with Ada.Text_IO;
with Apple_Arm64;
with Check;
with Diagnostics;
with Emit;
with MachO;
with Parser;
with Sections;
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

   function Link
     (Obj : Sections.Object; Output : String; Opts : Linker.Options)
      return Boolean
   is
   begin
      --  디버깅용: KURT_KEEP_OBJECT가 가리키는 경로에 오브젝트를 남긴다
      if Ada.Environment_Variables.Exists ("KURT_KEEP_OBJECT")
        and then not MachO.Write_Object
          (Obj, Ada.Environment_Variables.Value ("KURT_KEEP_OBJECT"))
      then
         Diagnostics.Report (Diagnostics.Warning,
                             "cannot write KURT_KEEP_OBJECT");
      end if;
      return Linker.Link (Obj, Output, Targets.AArch64_Apple, Opts);
   end Link;

   function Translate
     (Input  : String;
      Output : String;
      Stop   : Stop_After;
      Link   : Linker.Options) return Boolean
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
         M   : AArch64.Machine := AArch64.Create (Targets.Format_MachO);
         ABI : Apple_Arm64.Convention;
         Obj : Sections.Object;
         OK  : Boolean;
      begin
         Emit.Generate (Unit, M, ABI, Obj, OK);
         if not OK or else Diagnostics.Failures > 0 then
            return False;
         elsif Stop = Instructions then
            return Write_File (Output, Emit.Text (M, Obj));
         end if;
         M.Write_Code (Obj);
         return Pipeline.Link (Obj, Output, Link);
      end;
   end Translate;

end Pipeline;
