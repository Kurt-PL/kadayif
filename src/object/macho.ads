--  Mach-O: 어셈블리 지시어, 심볼 표기, 오브젝트 파일 쓰기
with Sections;

package MachO is

   --  C 계열 관례대로 외부 심볼 앞에 '_'를 붙인다
   function Symbol (Name : String) return String is ("_" & Name);

   --  어셈블러 지역 레이블: 심볼 표에 남지 않는다
   function Local_Label (Name : String) return String is ("L" & Name);

   --  링커 전용 심볼: 심볼 표에 지역 심볼로 남는다
   function Private_Symbol (Name : String) return String is ("l_" & Name);

   Text_Section  : constant String :=
     ".section __TEXT,__text,regular,pure_instructions";
   Const_Section : constant String := ".section __TEXT,__const";

   --  arm64 MH_OBJECT 파일. 쓸 수 없으면 False.
   function Write_Object (Obj : Sections.Object; Path : String)
                          return Boolean;

end MachO;
