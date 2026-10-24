--  형식 독립 오브젝트 모델: 섹션, 심볼, 재배치
--
--  ISA의 인코더와 Emit이 채우고, MachO·ELF가 파일로 쓴다. 심볼 이름은
--  어셈블리 텍스트에 쓰는 이름 그대로다(Mach-O면 '_'가 붙어 있다).
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Interfaces;

package Sections is

   type Section_Kind is (Text, Const);

   subtype Byte is Interfaces.Unsigned_8;
   package Byte_Vectors is new Ada.Containers.Vectors
     (Natural, Byte, Interfaces."=");

   type Symbol is record
      Name    : Ada.Strings.Unbounded.Unbounded_String;
      Defined : Boolean := False;
      Section : Section_Kind := Text;
      Offset  : Natural := 0;
      Global  : Boolean := False;
   end record;
   package Symbol_Vectors is new Ada.Containers.Vectors (Positive, Symbol);

   --  AArch64 재배치. 다른 ISA가 오면 늘어난다.
   type Reloc_Kind is
     (Branch26,    --  b, bl의 26비트 PC 상대
      Page21,      --  adrp의 페이지
      Page_Off12); --  add의 페이지 안 오프셋

   type Relocation is record
      Section : Section_Kind := Text;
      Offset  : Natural := 0;
      Kind    : Reloc_Kind := Branch26;
      Target  : Positive := 1;  --  Symbols의 색인
   end record;
   package Reloc_Vectors is new Ada.Containers.Vectors (Positive, Relocation);

   type Content_Array is array (Section_Kind) of Byte_Vectors.Vector;

   type Object is record
      Contents : Content_Array;
      Symbols  : Symbol_Vectors.Vector;
      Relocs   : Reloc_Vectors.Vector;
   end record;

   --  이름의 심볼 색인. 없으면 정의되지 않은 심볼로 만든다.
   function Lookup (Obj : in out Object; Name : String) return Positive;

   procedure Define
     (Obj     : in out Object;
      Name    : String;
      Section : Section_Kind;
      Offset  : Natural;
      Global  : Boolean);

   procedure Append (Obj : in out Object; Section : Section_Kind; B : Byte);
   procedure Append_Word
     (Obj : in out Object; Section : Section_Kind;
      W   : Interfaces.Unsigned_32);

   function Size (Obj : Object; Section : Section_Kind) return Natural is
     (Natural (Obj.Contents (Section).Length));

end Sections;
