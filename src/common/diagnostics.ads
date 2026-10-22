--  진단 메시지 출력 (KCSS §10)
--
--  형식: severity - message at path on line:col
--  KPLSS의 translation failure는 error, advisory diagnostic은 warning이다.
with Source_Map;

package Diagnostics is

   type Severity is (Halt, Error, Warning, Note);

   procedure Report
     (Sev : Severity; Pos : Source_Map.Source_Pos; Message : String);
   procedure Report (Sev : Severity; Message : String);

   procedure Error (Pos : Source_Map.Source_Pos; Message : String);
   procedure Warn (Pos : Source_Map.Source_Pos; Message : String);

   --  구현하지 않은 규격 요소 (KCSS §10.2 unimplemented error).
   --  What은 KPLSS의 요소를 절 번호와 함께 밝힌다.
   procedure Unimplemented (Pos : Source_Map.Source_Pos; What : String);

   --  halt와 error의 수
   function Failures return Natural;

end Diagnostics;
