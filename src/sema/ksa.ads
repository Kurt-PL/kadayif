--  레이아웃 계산: 크기와 정렬 (§5.2, §2.2.5 Kurt standard alignment)
--
--  단위는 셀이다. 지금은 프로그램 기계 하나(AArch64: 셀 8비트,
--  주소·참조 64비트)만 다룬다.
with Types;

package KSA is

   Reference_Cells : constant := 8;

   function Size (T : Types.Type_Id) return Natural;
   function Align (T : Types.Type_Id) return Natural;

   --  ⌈Offset / Align⌉ · Align. Align이 0이면 Offset 그대로 (§2.2.5).
   function Round_Up (Offset, Align : Natural) return Natural is
     (if Align = 0 then Offset
      else (Offset + Align - 1) / Align * Align);

end KSA;
