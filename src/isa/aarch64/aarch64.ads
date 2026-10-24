--  AArch64: Instruction_Set 구현
--
--  Temp 0–6은 x9–x15, 인자·결과 레지스터는 x0–x7, x16은 주소 계산용
--  스크래치다. 프레임 기준점은 x29이고 자동 객체는 그 아래에 있다.
--  명령마다 Apple 문법 텍스트와 기계어를 함께 기록해 두었다가
--  Write_Text 또는 Write_Code로 내보낸다.
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Interfaces;
with Instruction_Set;
with Sections;
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

   overriding procedure Load_Field
     (M : in out Machine; Dst, Addr : Temp; Offset : Natural; Ty : Scalar);
   overriding procedure Store_Field
     (M : in out Machine; Src, Addr : Temp; Offset : Natural; Ty : Scalar);
   overriding procedure Load_Bytes
     (M : in out Machine; Dst, Addr : Temp; Offset : Natural;
      Size : Positive);
   overriding procedure Store_Bytes
     (M : in out Machine; Src, Addr : Temp; Offset : Natural;
      Size : Positive);
   overriding procedure Copy_Memory
     (M : in out Machine; Dst, Src : Temp; Size : Natural);
   overriding procedure Zero_Memory
     (M : in out Machine; Dst : Temp; Size : Natural);
   overriding procedure Add_Immediate
     (M : in out Machine; Dst, Src : Temp; Value : Natural);

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
   overriding procedure Load_Stack
     (M : in out Machine; Dst : Temp; Offset : Natural);
   overriding procedure Move_From_Argument
     (M : in out Machine; Dst : Temp; Index : Natural);
   overriding procedure Stack_Address
     (M : in out Machine; Dst : Temp; Offset : Natural);
   overriding procedure Incoming_Address
     (M : in out Machine; Dst : Temp; Offset : Natural);
   overriding procedure Call (M : in out Machine; Symbol : String);
   overriding procedure Move_From_Result (M : in out Machine; Dst : Temp);
   overriding procedure Move_To_Result (M : in out Machine; Src : Temp);

   overriding procedure Store_Incoming
     (M : in out Machine; Index : Natural; Offset : Natural; Ty : Scalar);
   overriding procedure Load_Incoming
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar);

   overriding procedure Write_Text (M : Machine);
   overriding procedure Write_Code
     (M : Machine; Obj : in out Sections.Object);

private

   type Entry_Kind is
     (Plain,          --  고칠 것 없는 명령
      Label_Branch,   --  레이블로 가는 b, b.cond
      Symbol_Call,    --  심볼로 가는 bl
      Symbol_Page,    --  adrp
      Symbol_Offset,  --  add …@PAGEOFF
      Define_Label,
      Define_Symbol,
      Directive);     --  텍스트에만 있는 줄

   type Entry_Rec is record
      Kind   : Entry_Kind := Plain;
      Text   : Ada.Strings.Unbounded.Unbounded_String;
      Code   : Interfaces.Unsigned_32 := 0;
      Target : Label := 1;
      Symbol : Ada.Strings.Unbounded.Unbounded_String;
      Global : Boolean := False;
   end record;

   package Entry_Vectors is new Ada.Containers.Vectors (Positive, Entry_Rec);

   type Machine is new ISA with record
      Fmt          : Targets.Format_Kind := Targets.Format_MachO;
      Next_Label   : Positive := 1;
      Return_Label : Label := 1;
      Entries      : Entry_Vectors.Vector;
   end record;

end AArch64;
