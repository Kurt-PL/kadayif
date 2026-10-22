--  Mach-O: 어셈블리 지시어와 심볼 표기
--
--  오브젝트·실행 파일 쓰기는 아직 없다. 지금은 시스템 어셈블러에 넘길
--  텍스트의 지시어만 만든다.
package MachO is

   --  C 계열 관례대로 외부 심볼 앞에 '_'를 붙인다
   function Symbol (Name : String) return String is ("_" & Name);

   --  어셈블러 지역 레이블
   function Local_Label (Name : String) return String is ("L" & Name);

   Text_Section  : constant String :=
     ".section __TEXT,__text,regular,pure_instructions";
   Const_Section : constant String := ".section __TEXT,__const";

end MachO;
