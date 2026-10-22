--  이름 해석 (§4.18, §10.7)
--
--  top-level namespace 하나, #dyn 네임스페이스의 멤버, 그리고 블록마다
--  쌓이는 지역 스코프를 다룬다. 안쪽 스코프의 이름은 바깥 이름을
--  가린다(hide). 한 스코프 안에서 철자가 같은 이름은 금지다.
with Idents;
with Source_Map;
with Symbols;

package Names is

   procedure Declare_Global (Name : Idents.Ident; Sym : Symbols.Symbol_Id);
   procedure Declare_Member
     (Namespace : Symbols.Symbol_Id;
      Name      : Idents.Ident;
      Sym       : Symbols.Symbol_Id);

   procedure Push_Scope;
   procedure Pop_Scope;
   procedure Declare_Local (Name : Idents.Ident; Sym : Symbols.Symbol_Id);

   --  가장 안쪽에서 바로 보이는(directly visible) 이름. 없으면
   --  No_Symbol.
   function Lookup (Name : Idents.Ident) return Symbols.Symbol_Id;

   function Lookup_Member
     (Namespace : Symbols.Symbol_Id;
      Name      : Idents.Ident) return Symbols.Symbol_Id;

   --  같은 스코프에 철자가 같은 이름이 이미 있으면 그 심볼
   function Clash (Name : Idents.Ident) return Symbols.Symbol_Id;

   procedure Report_Clash
     (Pos : Source_Map.Source_Pos; Name : Idents.Ident);

end Names;
