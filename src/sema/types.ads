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
      Ty_Fn,
      Ty_Composite, --  선언된 struct, enum, contract
      Ty_Anon);     --  익명 구조체: 필드 타입은 Params

   type Tribe is (Shared, Exclusive, Unmanaged);

   type Modifiers is record
      Volatile, Mut, Atomic, Guard : Boolean := False;
   end record;

   package Type_Vectors is new Ada.Containers.Vectors (Positive, Type_Id);

   --  §8.1.2 routes. 끝점은 매개변수의 층 하나(Deeper면 그보다 깊은 층
   --  전부도), static, 또는 return이다. Param은 0부터 센다.
   type Route_End_Kind is (End_Layer, End_Static, End_Return);
   type Route_End is record
      Kind   : Route_End_Kind := End_Return;
      Param  : Natural := 0;
      Layer  : Natural := 0;
      Deeper : Boolean := False;
   end record;
   package Route_End_Vectors is new Ada.Containers.Vectors
     (Positive, Route_End);
   type Route is record
      Sources : Route_End_Vectors.Vector;
      Target  : Route_End;
   end record;
   package Route_Vectors is new Ada.Containers.Vectors (Positive, Route);

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

      --  Ty_Composite: Composites의 색인
      Composite : Natural := 0;

      --  Ty_Fn, Ty_Anon
      Params    : Type_Vectors.Vector;
      Ret       : Type_Id := No_Type;
      Variadic  : Boolean := False;
      Airside   : Boolean := False;
      Invocation : Idents.Ident := Idents.No_Ident;  --  호출 인터페이스
      --  routes 절이 없으면 기본 routes: 모든 층과 static이 return으로
      Default_Routes : Boolean := True;
      Routes         : Route_Vectors.Vector;
   end record;

   ---------------------------------------------------------------------
   --  선언된 복합 타입 (§4.6–§4.8, §7.2)

   type Composite_Kind is (Struct_Type, Enum_Type, Contract_Type);
   type Form_Kind is (Unit_Form, Unnamed_Form, Named_Form);

   type Field_Info is record
      Name    : Idents.Ident := Idents.No_Ident;
      Ty      : Type_Id := No_Type;
      Pub     : Boolean := False;
      Airside : Boolean := False;
      Mut     : Boolean := False;
      Pad     : Boolean := False;   --  ? 필드
      Default : Natural := 0;       --  기본값 식 (AST.Node_Id)
      Offset  : Natural := 0;       --  KSA가 채운다: 구조체 안의 오프셋
   end record;
   package Field_Vectors is new Ada.Containers.Vectors (Positive, Field_Info);

   type Variant_Info is record
      Name      : Idents.Ident := Idents.No_Ident;
      Form      : Form_Kind := Unit_Form;
      Fields    : Field_Vectors.Vector;
      Value     : Long_Long_Integer := 0;  --  판별자 값
      Wild      : Boolean := False;
      Canonical : Boolean := False;        --  wild(V)
      Size      : Natural := 0;            --  KSA가 채운다
      Align     : Natural := 0;
   end record;
   package Variant_Vectors is new Ada.Containers.Vectors
     (Positive, Variant_Info);

   type Layout_State is (Not_Laid_Out, Laying_Out, Laid_Out);

   type Composite_Info is record
      Name      : Idents.Ident := Idents.No_Ident;
      Kind      : Composite_Kind := Struct_Type;
      Form      : Form_Kind := Unit_Form;     --  구조체의 형태
      Fields    : Field_Vectors.Vector;       --  구조체의 필드
      Variants  : Variant_Vectors.Vector;
      Disc      : Type_Id := No_Type;         --  판별자 타입 (void일 수 있다)
      Copyable  : Boolean := False;           --  with copyable
      Inverted  : Boolean := False;           --  contract!
      Inv       : Type_Id := No_Type;         --  with inv -> T
      Pack      : Natural := 0;               --  repr(pack(N)), 0이면 없음
      Min_Align : Natural := 0;               --  align(N), 0이면 없음
      Decl      : Natural := 0;               --  AST.Node_Id
      State     : Layout_State := Not_Laid_Out;
      Size      : Natural := 0;
      Align     : Natural := 0;
      Payload_Offset : Natural := 0;          --  변형 필드들이 시작하는 곳
   end record;
   package Composite_Vectors is new Ada.Containers.Vectors
     (Positive, Composite_Info);

   Composites : Composite_Vectors.Vector;

   --  새 복합 타입을 등록하고 그 타입을 돌려준다
   function New_Composite (Info : Composite_Info) return Type_Id;
   function Info (T : Type_Id) return Composite_Info;

   --  Info (T).Fields (I)처럼 임시값 안을 바로 색인하면 임시값이 참조보다
   --  먼저 정리되므로, 이 함수들로 복사해 꺼낸다
   function Field (T : Type_Id; Index : Positive) return Field_Info;
   function Variant (T : Type_Id; Index : Positive) return Variant_Info;
   procedure Set_Info (T : Type_Id; Info : Composite_Info);

   function Anon (Fields : Type_Vectors.Vector) return Type_Id;

   --  contract 타입인가: verdict, 또는 contract 선언이 들인 타입
   function Is_Contract (T : Type_Id) return Boolean;
   --  variant 타입인가: contract 타입이거나 enum
   function Is_Variant (T : Type_Id) return Boolean;

   --  서브루틴 타입 Fn이 From(층 하나 또는 static)을 To(층 하나, static,
   --  또는 return)로 보내는가 (§8.1.2 routes)
   function Routes_To (Fn : Type_Id; From, To : Route_End) return Boolean;

   --  §8.7 copyable
   function Is_Copyable (T : Type_Id) return Boolean;

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
