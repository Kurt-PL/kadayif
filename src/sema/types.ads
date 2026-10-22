--  타입 표현과 인터닝 (§5)
--
--  구조가 같은 타입은 같은 Type_Id를 받는다. 타입 동일성 비교가
--  곧 Type_Id 비교다.
with Ada.Containers.Vectors;
with Idents;

package Types is

   type Type_Id is new Natural;
   No_Type : constant Type_Id := 0;

   type Type_Kind is
     (Ty_Error,    --  이미 진단한 오류. 연쇄 진단을 막는다.
      Ty_Void,
      Ty_Never,    --  -> ! 와 발산하는 식
      Ty_Int,
      Ty_Ref,      --  얇은 참조
      Ty_Slice,    --  slice 참조 (넓은 참조)
      Ty_Array,
      Ty_Verdict,
      Ty_Fn);

   type Tribe is (Shared, Exclusive, Unmanaged);

   type Modifiers is record
      Volatile, Mut, Atomic, Guard : Boolean := False;
   end record;

   package Type_Vectors is new Ada.Containers.Vectors (Positive, Type_Id);

   type Type_Rec is record
      Kind   : Type_Kind := Ty_Error;

      --  Ty_Int: 셀 수(ui1 → 1)와 부호. Addr면 uaddr/saddr.
      Signed : Boolean := False;
      Cells  : Natural := 0;
      Addr   : Boolean := False;

      --  Ty_Ref, Ty_Slice, Ty_Array
      Ref_Tribe : Tribe := Shared;
      Mods      : Modifiers;
      Target    : Type_Id := No_Type;  --  가리키는 타입 또는 원소 타입
      Length    : Natural := 0;        --  배열 길이

      --  Ty_Verdict
      Pass, Fail : Type_Id := No_Type;

      --  Ty_Fn
      Params    : Type_Vectors.Vector;
      Ret       : Type_Id := No_Type;
      Variadic  : Boolean := False;
      Airside   : Boolean := False;
      Invocation : Idents.Ident := Idents.No_Ident;  --  호출 인터페이스
   end record;

   function Make (R : Type_Rec) return Type_Id;
   function Get (T : Type_Id) return Type_Rec;
   function Kind (T : Type_Id) return Type_Kind;

   function Image (T : Type_Id) return String;

   --  내장 타입
   function Error_Type return Type_Id;
   function Void return Type_Id;
   function Never return Type_Id;
   function Uaddr return Type_Id;
   function Saddr return Type_Id;
   function Int (Signed : Boolean; Cells : Positive) return Type_Id;
   function Verdict (Pass, Fail : Type_Id) return Type_Id;
   --  verdict[void, void]: 비교와 논리 연산의 결과
   function Bool return Type_Id;
   function Ref (Of_Type : Type_Id; T : Tribe; M : Modifiers := (others => <>))
                 return Type_Id;
   function Array_Of (Elem : Type_Id; Length : Natural) return Type_Id;

   --  ui1, si4, uaddr, void 같은 내장 타입 이름. 아니면 No_Type.
   function Builtin (Name : String) return Type_Id;

   function Is_Int (T : Type_Id) return Boolean is (Kind (T) = Ty_Int);
   function Is_Signed (T : Type_Id) return Boolean is
     (Kind (T) = Ty_Int and then Get (T).Signed);

end Types;
