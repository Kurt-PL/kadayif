--  구문 트리
--
--  c1974의 tnode처럼 모든 노드가 같은 모양이다. 종류별로 A, B, C와
--  List가 무엇을 가리키는지는 Node_Kind 옆 주석에 적는다. Ty와 Sym은
--  의미 분석이 채운다.
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Idents;
with Source_Map;
with Tokens;

package AST is

   type Node_Id is new Natural;
   No_Node : constant Node_Id := 0;

   type List_Id is record
      First : Natural := 0;
      Count : Natural := 0;
   end record;
   Empty_List : constant List_Id := (0, 0);

   type Node_Kind is
     (N_None,

      --  항목
      N_Unit,        --  List: 항목
      N_Fn,          --  Name, List: N_Param, A: 반환 타입(없으면 void),
                     --  B: 본문(N_Block, 원형이면 없음),
                     --  C: N_Routes(없으면 기본 routes),
                     --  Name2: 호출 인터페이스 식별자
      N_Routes,      --  List: N_Route
      N_Route,       --  List: 원천(N_Route_Path), A: 대상(N_Route_Path)
      N_Route_Path,  --  F_Static / F_Return, 아니면 Name(식별자),
                     --  F_Self(self), Text(위치)로 매개변수, Sym: '*' 수,
                     --  F_Ellipsis면 더 깊은 층도
      N_Param,       --  Name(익명 원형 매개변수면 없음), A: 타입
      N_Dyn,         --  Name, List: 항목
      N_Struct,      --  Name, List: N_Field_Decl, C: N_With,
                     --  F_Unit / F_Named로 형태
      N_Enum,        --  Name, List: N_Variant, C: N_With
      N_Contract,    --  Name, List: N_Variant 둘, C: N_With,
                     --  F_Inverted면 contract!
      N_Variant,     --  Name, List: N_Field_Decl, F_Unit / F_Named,
                     --  A: 판별자 값(N_Int_Lit), F_Wild면 wild
      N_Field_Decl,  --  Name(이름 없는 필드면 없음), A: 타입,
                     --  B: 기본값 식, F_Pub/F_Airside/F_Mut, F_Pad면 ?
      N_With,        --  List: N_With_Item
      N_With_Item,   --  Name: 항목 이름(copyable, discrim, inv, repr,
                     --  align …), A: 타입 또는 정수 리터럴

      --  타입
      N_Path,        --  List: N_Segment (single_path)
      N_Segment,     --  Name
      N_Ref_Type,    --  Op: 부족(& $ %), A: 가리키는 타입
      N_Slice_Type,  --  Op: 부족, A: 원소 타입
      N_Array_Type,  --  A: 원소 타입, B: 길이 식
      N_Never_Type,  --  -> !
      N_Infer_Type,  --  ?
      N_Anon_Type,   --  List: 필드 타입

      --  문
      N_Let,         --  Name, A: 타입, B: 초기식

      --  식
      N_Name,        --  A: N_Path
      N_Int_Lit,     --  Text: 철자, A: 접미 타입
      N_Float_Lit,   --  Text: 철자, A: 접미 타입
      N_Char_Lit,    --  Text: 셀 값 열
      N_String_Lit,  --  Text: 셀 값 열
      N_Unary,       --  Op, A
      N_Binary,      --  Op, A, B (산술·비트·비교·논리)
      N_Assign,      --  Op(= 또는 복합 대입), A, B
      N_Cast,        --  A: 식, B: 타입, F_Reinterpret
      N_Call,        --  A: 피호출 식, List: 인자
      N_Field,       --  A: 식, Name 또는 Text(정수 필드)
      N_Construct,   --  A: N_Path, List: 식 또는 N_Field_Init,
                     --  F_Braces면 중괄호가 있다
      N_Field_Init,  --  Name, A: 식
      N_Anon,        --  List: 식 (익명 구조체 구성)
      N_Wild_Construct, --  A: N_Path
      N_Block,       --  List: 블록 항목, Name: 레이블
      N_Airside,     --  A: N_Block
      N_If,          --  A: 조건, B: 참 갈래, C: 거짓 갈래
      N_While,       --  A: 조건, B: 본문, Name: 레이블
      N_Loop,        --  A: 본문, Name: 레이블
      N_Return,      --  A: 값
      N_Break,       --  A: 값, Name: 레이블
      N_Continue);   --  Name: 레이블

   subtype Type_Node is Node_Kind range N_Path .. N_Anon_Type;

   type Flag is
     (F_Pub, F_Extern, F_Airside, F_Variadic, F_Mut,
      F_Volatile, F_Atomic, F_Guard, F_Xlat, F_Reinterpret,
      F_Unit, F_Named, F_Pad, F_Wild, F_Inverted, F_Braces,
      F_Static, F_Return, F_Self, F_Ellipsis);
   type Flag_Set is array (Flag) of Boolean with Pack;
   No_Flags : constant Flag_Set := [others => False];

   type Node is record
      Kind  : Node_Kind := N_None;
      Pos   : Source_Map.Source_Pos;
      Op    : Tokens.Token_Kind := Tokens.T_EOF;
      A     : Node_Id := No_Node;
      B     : Node_Id := No_Node;
      C     : Node_Id := No_Node;
      List  : List_Id;
      Name  : Idents.Ident := Idents.No_Ident;
      Name2 : Idents.Ident := Idents.No_Ident;
      Text  : Ada.Strings.Unbounded.Unbounded_String;
      Flags : Flag_Set := No_Flags;
      Ty    : Natural := 0;  --  Types.Type_Id
      Sym   : Natural := 0;  --  Symbols.Symbol_Id
   end record;

   package Node_Vectors is new Ada.Containers.Vectors (Positive, Node);
   package Id_Vectors is new Ada.Containers.Vectors (Positive, Node_Id);

   Nodes : Node_Vectors.Vector;

   function Add (N : Node) return Node_Id;

   function Make_List (Items : Id_Vectors.Vector) return List_Id;
   function Item (L : List_Id; Index : Positive) return Node_Id;

   function Kind (N : Node_Id) return Node_Kind is
     (if N = No_Node then N_None else Nodes (Positive (N)).Kind);

end AST;
