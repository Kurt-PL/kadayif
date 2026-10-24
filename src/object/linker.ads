--  링크 편집: 오브젝트를 실행 파일로 (KCSS §3의 link phase)
--
--  지금은 kadayif가 메모리에 만든 오브젝트 하나를 Mach-O arm64 실행
--  파일로 링크한다. 동적 라이브러리는 받고, 외부 .o와 정적
--  라이브러리는 아직 받지 않는다.
with Libraries;
with Sections;
with Targets;

package Linker is

   type Options is record
      --  -l로 찾은 라이브러리, 명령행 순서
      Libraries : Standard.Libraries.Library_Vectors.Vector;
      --  -R로 준 실행 시 검색 경로
      Rpaths    : Standard.Libraries.String_Vectors.Vector;
   end record;

   --  실패하면 진단을 내고 False
   function Link
     (Obj    : Sections.Object;
      Output : String;
      Target : Targets.Target;
      Opts   : Options) return Boolean;

end Linker;
