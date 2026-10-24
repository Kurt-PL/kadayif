--  arm64 Mach-O 실행 파일 쓰기
--
--  한 오브젝트를 받아 섹션을 배치하고, 재배치를 적용하고, 정의되지
--  않은 심볼마다 스텁과 GOT 칸을 만들어 동적 라이브러리에 바인딩하고
--  (chained fixups), ad-hoc 코드 서명을 붙인다.
with Libraries;
with Sections;

package MachO.Executable is

   --  Entry_Name은 진입점 심볼 이름(예: "_main"), Identifier는 코드
   --  서명의 식별자. 가져오는 심볼은 Dylibs를 순서대로 보아 처음
   --  내보내는 라이브러리에 바인딩한다(2단계 네임스페이스). 실패하면
   --  진단을 내고 False.
   function Write
     (Obj        : Sections.Object;
      Path       : String;
      Entry_Name : String;
      Identifier : String;
      Dylibs     : Libraries.Library_Vectors.Vector;
      Rpaths     : Libraries.String_Vectors.Vector) return Boolean;

end MachO.Executable;
