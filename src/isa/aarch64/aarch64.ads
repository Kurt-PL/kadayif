--  AArch64: Instruction_Set 구현
--
--  Temp 0–6은 x9–x15, 인자·결과 레지스터는 x0–x7, x16은 주소 계산용
--  스크래치다. 프레임 기준점은 x29이고 자동 객체는 그 아래에 있다.
--  지금은 Apple 어셈블러 문법의 텍스트를 Listing에 쓴다.
with Interfaces;
with Instruction_Set;
with Targets;

package AArch64 is

   use Instruction_Set;

   type Machine is new ISA with private;

   function Create (Format : Targets.Format_Kind) return Machine;

   overriding function Max_Temps (M : Machine) return Natural is (7);
   overriding function Format (M : Machine) return Targets.Format_Kind;

   overriding procedure Begin_Function
     (M : in out Machine; Symbol : String; Global : Boolean;
      Frame_Size : Natural);
   overriding procedure End_Function (M : in out Machine);
   overriding procedure Jump_To_Return (M : in out Machine);

   overriding function New_Label (M : in out Machine) return Label;
   overriding procedure Place (M : in out Machine; L : Label);
   overriding procedure Jump (M : in out Machine; L : Label);

   overriding procedure Load_Immediate
     (M : in out Machine; Dst : Temp; Value : Interfaces.Unsigned_64);
   overriding procedure Move (M : in out Machine; Dst, Src : Temp);

   overriding procedure Load_Frame
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar);
   overriding procedure Store_Frame
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar);
   overriding procedure Frame_Address
     (M : in out Machine; Dst : Temp; Offset : Natural);

   overriding procedure Load_Indirect
     (M : in out Machine; Dst, Addr : Temp; Ty : Scalar);
   overriding procedure Store_Indirect
     (M : in out Machine; Src, Addr : Temp; Ty : Scalar);

   overriding procedure Data_Address
     (M : in out Machine; Dst : Temp; Symbol : String);

   overriding procedure Arith
     (M : in out Machine; Op : Arith_Op; Dst, Left, Right : Temp;
      Ty : Scalar);
   overriding procedure Unary
     (M : in out Machine; Op : Unary_Op; Dst, Src : Temp);
   overriding procedure Normalize
     (M : in out Machine; R : Temp; Ty : Scalar);

   overriding procedure Compare_And_Set
     (M : in out Machine; Dst, Left, Right : Temp; C : Condition);
   overriding procedure Compare_And_Branch
     (M : in out Machine; Left, Right : Temp; C : Condition;
      Target : Label);
   overriding procedure Test_And_Branch
     (M : in out Machine; R : Temp; Value : Natural; Equal : Boolean;
      Target : Label);

   overriding procedure Save_Temp (M : in out Machine; R : Temp);
   overriding procedure Restore_Temp (M : in out Machine; R : Temp);
   overriding procedure Reserve_Outgoing (M : in out Machine; Size : Natural);
   overriding procedure Release_Outgoing (M : in out Machine; Size : Natural);
   overriding procedure Store_Outgoing
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar);
   overriding procedure Move_To_Argument
     (M : in out Machine; Index : Natural; Src : Temp);
   overriding procedure Call (M : in out Machine; Symbol : String);
   overriding procedure Move_From_Result (M : in out Machine; Dst : Temp);
   overriding procedure Move_To_Result (M : in out Machine; Src : Temp);

   overriding procedure Store_Incoming
     (M : in out Machine; Index : Natural; Offset : Natural; Ty : Scalar);
   overriding procedure Load_Incoming
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar);

private

   type Machine is new ISA with record
      Fmt          : Targets.Format_Kind := Targets.Format_MachO;
      Next_Label   : Positive := 1;
      Return_Label : Label := 1;
   end record;

end AArch64;
