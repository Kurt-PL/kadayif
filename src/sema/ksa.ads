--  레이아웃 계산: 크기와 정렬 (§5.2, §2.2.5 Kurt standard alignment,
--  §5.11)
--
--  단위는 셀이다. 지금은 프로그램 기계 하나(AArch64: 셀 8비트,
--  주소·참조 64비트)만 다룬다.
with Types;

package KSA is

   Reference_Cells : constant := 8;

   --  타입의 레이아웃이 자기 자신을 요구한다 (§5.11.1)
   Layout_Cycle : exception;

   function Size (T : Types.Type_Id) return Natural;
   function Align (T : Types.Type_Id) return Natural;

   --  ⌈Offset / Align⌉ · Align. Align이 0이면 Offset 그대로 (§2.2.5).
   function Round_Up (Offset, Align : Natural) return Natural is
     (if Align = 0 then Offset
      else (Offset + Align - 1) / Align * Align);

   --  구조체·익명 구조체의 Index번째 필드 오프셋
   function Field_Offset (T : Types.Type_Id; Index : Positive)
                          return Natural;

   --  variant 타입: 판별자 타입(void일 수 있다), 변형 Variant의 Field번째
   --  필드의 오프셋(타입 시작 기준)
   function Disc_Type (T : Types.Type_Id) return Types.Type_Id;
   function Variant_Field_Offset
     (T : Types.Type_Id; Variant, Field : Positive) return Natural;

end KSA;
