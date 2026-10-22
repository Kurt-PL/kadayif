package body KSA is

   use Types;

   --  verdict의 한 변형: [판별자 ui1, 페이로드]를 KSA로 배치
   procedure Variant_Layout (Payload : Type_Id; S, A : out Natural) is
      Payload_Offset : constant Natural := Round_Up (1, Align (Payload));
   begin
      A := Natural'Max (1, Align (Payload));
      S := Round_Up (Payload_Offset + Size (Payload), A);
   end Variant_Layout;

   function Size (T : Type_Id) return Natural is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error => return 1;
         when Ty_Void | Ty_Never => return 0;
         when Ty_Int => return R.Cells;
         when Ty_Ref | Ty_Fn => return Reference_Cells;
         when Ty_Slice => return 2 * Reference_Cells;
         when Ty_Array => return R.Length * Size (R.Target);
         when Ty_Verdict =>
            declare
               SP, AP, SF, AF : Natural;
            begin
               Variant_Layout (R.Pass, SP, AP);
               Variant_Layout (R.Fail, SF, AF);
               return Round_Up (Natural'Max (SP, SF), Natural'Max (AP, AF));
            end;
      end case;
   end Size;

   function Align (T : Type_Id) return Natural is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error => return 1;
         when Ty_Void | Ty_Never => return 0;
         when Ty_Int => return R.Cells;
         when Ty_Ref | Ty_Fn | Ty_Slice => return Reference_Cells;
         when Ty_Array => return Align (R.Target);
         when Ty_Verdict =>
            return Natural'Max
              (1, Natural'Max (Align (R.Pass), Align (R.Fail)));
      end case;
   end Align;

end KSA;
