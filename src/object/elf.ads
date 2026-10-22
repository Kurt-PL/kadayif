--  ELF: 어셈블리 지시어와 심볼 표기
--
--  오브젝트·실행 파일 쓰기는 아직 없다. 지금은 시스템 어셈블러에 넘길
--  텍스트의 지시어만 만든다.
package ELF is

   function Symbol (Name : String) return String is (Name);

   --  어셈블러 지역 레이블
   function Local_Label (Name : String) return String is (".L" & Name);

   Text_Section  : constant String := ".text";
   Const_Section : constant String := ".section .rodata";

end ELF;
