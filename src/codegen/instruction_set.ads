--  ISA가 구현할 추상 인터페이스
--
--  Emit은 c1974의 c1처럼 식 트리를 따라 내려가며 이 연산들을 부른다.
--  Temp는 c1의 레지스터 번호처럼 평가 깊이를 나타내는 가상 레지스터이고,
--  ISA가 실제 레지스터에 대응시킨다. 레지스터의 값은 언제나 표준형
--  (타입 폭을 넘는 비트를 부호 또는 0으로 채운 64비트)이다.
with Interfaces;
with Sections;
with Targets;

package Instruction_Set is

   type Temp is new Natural;
   type Label is new Positive;

   --  스칼라 값의 모양. Size는 셀(바이트) 수.
   type Scalar is record
      Size   : Positive := 8;
      Signed : Boolean  := False;
   end record;

   Word : constant Scalar := (8, False);

   type Condition is (Eq, Ne, Lt, Le, Gt, Ge, Lo, Ls, Hi, Hs);
   function Negate (C : Condition) return Condition is
     (case C is
        when Eq => Ne, when Ne => Eq,
        when Lt => Ge, when Ge => Lt, when Le => Gt, when Gt => Le,
        when Lo => Hs, when Hs => Lo, when Ls => Hi, when Hi => Ls);

   type Arith_Op is (Add, Sub, Mul, Div, Remainder, Bit_And, Bit_Or, Bit_Xor);
   type Unary_Op is (Neg, Bit_Not);

   type ISA is abstract tagged limited null record;

   --  동시에 쓸 수 있는 Temp의 수
   function Max_Temps (M : ISA) return Natural is abstract;

   --  오브젝트 형식 (지시어와 재배치 표기)
   function Format (M : ISA) return Targets.Format_Kind is abstract;

   --  서브루틴. Frame_Size는 자동 객체 영역의 셀 수.
   procedure Begin_Function
     (M : in out ISA; Symbol : String; Global : Boolean;
      Frame_Size : Natural) is abstract;
   procedure End_Function (M : in out ISA) is abstract;
   procedure Jump_To_Return (M : in out ISA) is abstract;

   function New_Label (M : in out ISA) return Label is abstract;
   procedure Place (M : in out ISA; L : Label) is abstract;
   procedure Jump (M : in out ISA; L : Label) is abstract;

   procedure Load_Immediate
     (M : in out ISA; Dst : Temp; Value : Interfaces.Unsigned_64)
   is abstract;
   procedure Move (M : in out ISA; Dst, Src : Temp) is abstract;

   --  프레임: Offset은 프레임 기준점 아래로의 거리
   procedure Load_Frame
     (M : in out ISA; Dst : Temp; Offset : Natural; Ty : Scalar)
   is abstract;
   procedure Store_Frame
     (M : in out ISA; Src : Temp; Offset : Natural; Ty : Scalar)
   is abstract;
   procedure Frame_Address (M : in out ISA; Dst : Temp; Offset : Natural)
   is abstract;

   --  [Addr + Offset]의 스칼라
   procedure Load_Field
     (M : in out ISA; Dst, Addr : Temp; Offset : Natural; Ty : Scalar)
   is abstract;
   procedure Store_Field
     (M : in out ISA; Src, Addr : Temp; Offset : Natural; Ty : Scalar)
   is abstract;

   --  정확히 Size(1–8)바이트: 적재는 0으로 확장하고, 저장은 하위 바이트만
   procedure Load_Bytes
     (M : in out ISA; Dst, Addr : Temp; Offset : Natural; Size : Positive)
   is abstract;
   procedure Store_Bytes
     (M : in out ISA; Src, Addr : Temp; Offset : Natural; Size : Positive)
   is abstract;

   --  집합체: [Dst .. Dst + Size)에 [Src ..)를 복사하거나 0으로 채운다
   procedure Copy_Memory (M : in out ISA; Dst, Src : Temp; Size : Natural)
   is abstract;
   procedure Zero_Memory (M : in out ISA; Dst : Temp; Size : Natural)
   is abstract;

   procedure Add_Immediate
     (M : in out ISA; Dst, Src : Temp; Value : Natural) is abstract;

   --  데이터 레이블의 주소
   procedure Data_Address (M : in out ISA; Dst : Temp; Symbol : String)
   is abstract;

   procedure Arith
     (M : in out ISA; Op : Arith_Op; Dst, Left, Right : Temp; Ty : Scalar)
   is abstract;
   procedure Unary (M : in out ISA; Op : Unary_Op; Dst, Src : Temp)
   is abstract;

   --  레지스터를 Ty의 표준형으로 맞춘다
   procedure Normalize (M : in out ISA; R : Temp; Ty : Scalar) is abstract;

   procedure Compare_And_Set
     (M : in out ISA; Dst, Left, Right : Temp; C : Condition) is abstract;
   procedure Compare_And_Branch
     (M : in out ISA; Left, Right : Temp; C : Condition; Target : Label)
   is abstract;
   --  R = Value 이면(Equal) 또는 아니면 Target으로
   procedure Test_And_Branch
     (M : in out ISA; R : Temp; Value : Natural; Equal : Boolean;
      Target : Label) is abstract;

   --  호출
   procedure Save_Temp (M : in out ISA; R : Temp) is abstract;
   procedure Restore_Temp (M : in out ISA; R : Temp) is abstract;
   procedure Reserve_Outgoing (M : in out ISA; Size : Natural) is abstract;
   procedure Release_Outgoing (M : in out ISA; Size : Natural) is abstract;
   procedure Store_Outgoing
     (M : in out ISA; Src : Temp; Offset : Natural; Ty : Scalar)
   is abstract;
   procedure Move_To_Argument (M : in out ISA; Index : Natural; Src : Temp)
   is abstract;
   procedure Move_From_Argument
     (M : in out ISA; Dst : Temp; Index : Natural) is abstract;
   --  나가는 스택 인자 영역의 Offset 주소
   procedure Stack_Address (M : in out ISA; Dst : Temp; Offset : Natural)
   is abstract;
   --  들어온 스택 인자 영역의 Offset 주소
   procedure Incoming_Address
     (M : in out ISA; Dst : Temp; Offset : Natural) is abstract;
   --  스택 포인터 기준 Offset의 한 워드를 읽는다
   procedure Load_Stack (M : in out ISA; Dst : Temp; Offset : Natural)
   is abstract;
   procedure Call (M : in out ISA; Symbol : String) is abstract;
   procedure Move_From_Result (M : in out ISA; Dst : Temp) is abstract;
   procedure Move_To_Result (M : in out ISA; Src : Temp) is abstract;

   --  진입 시 인자: 레지스터 Index의 값을 프레임에 저장하거나,
   --  호출자 스택의 Offset에서 읽는다
   procedure Store_Incoming
     (M : in out ISA; Index : Natural; Offset : Natural; Ty : Scalar)
   is abstract;
   procedure Load_Incoming
     (M : in out ISA; Dst : Temp; Offset : Natural; Ty : Scalar)
   is abstract;

   --  모은 명령을 내보낸다: 어셈블리 텍스트(Listing)로, 또는 기계어와
   --  심볼·재배치를 Obj의 Text 섹션으로
   procedure Write_Text (M : ISA) is abstract;
   procedure Write_Code (M : ISA; Obj : in out Sections.Object) is abstract;

end Instruction_Set;
