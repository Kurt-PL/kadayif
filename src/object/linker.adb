with Ada.Directories;
with Ada.Strings.Unbounded;
with Diagnostics;
with MachO.Executable;

package body Linker is

   use Ada.Strings.Unbounded;
   use type Targets.Format_Kind;

   function Link
     (Obj    : Sections.Object;
      Output : String;
      Target : Targets.Target;
      Opts   : Options) return Boolean
   is
      --  싣는 순서: -l 라이브러리를 명령행 순서대로. 요청하지 않은
      --  라이브러리는 싣지 않는다 (KCSS §4.9).
      Dylibs : Libraries.Library_Vectors.Vector;

      procedure Add (Lib : Libraries.Library) is
      begin
         for L of Dylibs loop
            if L.Install_Name = Lib.Install_Name then
               return;
            end if;
         end loop;
         Dylibs.Append (Lib);
      end Add;

   begin
      if Target.Format /= Targets.Format_MachO then
         Diagnostics.Report
           (Diagnostics.Error, "unimplemented: linking ELF executables");
         return False;
      end if;
      for L of Opts.Libraries loop
         Add (L);
      end loop;
      return MachO.Executable.Write
        (Obj, Output,
         Entry_Name => MachO.Symbol ("main"),
         Identifier => Ada.Directories.Simple_Name (Output),
         Dylibs     => Dylibs,
         Rpaths     => Opts.Rpaths);
   end Link;

end Linker;
