--  심볼 표
--
--  의미 분석이 선언마다 심볼 하나를 만든다. 코드 생성은 Slot과
--  Link_Name을 채워 쓴다.
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Idents;
with Source_Map;

package Symbols is

   type Symbol_Id is new Natural;
   No_Symbol : constant Symbol_Id := 0;

   type Symbol_Kind is
     (Sym_Fn,         --  서브루틴
      Sym_Param,      --  매개변수 바인딩
      Sym_Local,      --  let 바인딩
      Sym_Namespace,  --  #dyn 네임스페이스
      Sym_Type);      --  struct, enum, contract 선언

   type Symbol is record
      Kind     : Symbol_Kind := Sym_Local;
      Name     : Idents.Ident := Idents.No_Ident;
      Pos      : Source_Map.Source_Pos;
      Ty       : Natural := 0;   --  Types.Type_Id
      Decl     : Natural := 0;   --  AST.Node_Id
      Mutable  : Boolean := False;
      Dyn      : Boolean := False;  --  #dyn 블록의 선언
      Pub      : Boolean := False;
      Index    : Natural := 0;   --  매개변수 위치(1부터)
      Slot     : Natural := 0;   --  자동 객체의 프레임 오프셋(코드 생성)
      Link_Name : Ada.Strings.Unbounded.Unbounded_String;
   end record;

   package Symbol_Vectors is new Ada.Containers.Vectors (Positive, Symbol);
   Table : Symbol_Vectors.Vector;

   function Add (S : Symbol) return Symbol_Id;
   function Get (Id : Symbol_Id) return Symbol is (Table (Positive (Id)));

end Symbols;
