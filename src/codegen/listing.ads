--  어셈블리 텍스트 출력 버퍼
package Listing is

   procedure Clear;
   procedure Put_Line (S : String);

   --  들여쓴 명령 한 줄
   procedure Instr (S : String);

   function Contents return String;

end Listing;
