with Ada.Containers.Vectors;
with Diagnostics;

package body Names is

   use type Idents.Ident;
   use type Symbols.Symbol_Id;

   type Binding is record
      Owner : Symbols.Symbol_Id := Symbols.No_Symbol;  --  멤버의 네임스페이스
      Name  : Idents.Ident;
      Sym   : Symbols.Symbol_Id;
   end record;

   package Binding_Vectors is new Ada.Containers.Vectors (Positive, Binding);
   package Mark_Vectors is new Ada.Containers.Vectors (Positive, Natural);

   Globals : Binding_Vectors.Vector;  --  top-level 이름과 네임스페이스 멤버
   Locals  : Binding_Vectors.Vector;
   Marks   : Mark_Vectors.Vector;     --  스코프마다 시작 위치

   function Find
     (V : Binding_Vectors.Vector; From : Positive;
      Owner : Symbols.Symbol_Id; Name : Idents.Ident)
      return Symbols.Symbol_Id
   is
   begin
      for I in reverse From .. V.Last_Index loop
         if V (I).Name = Name and then V (I).Owner = Owner then
            return V (I).Sym;
         end if;
      end loop;
      return Symbols.No_Symbol;
   end Find;

   procedure Declare_Global (Name : Idents.Ident; Sym : Symbols.Symbol_Id) is
   begin
      Globals.Append (Binding'(Symbols.No_Symbol, Name, Sym));
   end Declare_Global;

   procedure Declare_Member
     (Namespace : Symbols.Symbol_Id;
      Name      : Idents.Ident;
      Sym       : Symbols.Symbol_Id)
   is
   begin
      Globals.Append (Binding'(Namespace, Name, Sym));
   end Declare_Member;

   procedure Push_Scope is
   begin
      Marks.Append (Natural (Locals.Length) + 1);
   end Push_Scope;

   procedure Pop_Scope is
   begin
      while Natural (Locals.Length) >= Marks.Last_Element loop
         Locals.Delete_Last;
      end loop;
      Marks.Delete_Last;
   end Pop_Scope;

   procedure Declare_Local (Name : Idents.Ident; Sym : Symbols.Symbol_Id) is
   begin
      Locals.Append (Binding'(Symbols.No_Symbol, Name, Sym));
   end Declare_Local;

   function Lookup (Name : Idents.Ident) return Symbols.Symbol_Id is
      S : constant Symbols.Symbol_Id :=
        Find (Locals, 1, Symbols.No_Symbol, Name);
   begin
      if S /= Symbols.No_Symbol then
         return S;
      end if;
      return Find (Globals, 1, Symbols.No_Symbol, Name);
   end Lookup;

   function Lookup_Member
     (Namespace : Symbols.Symbol_Id;
      Name      : Idents.Ident) return Symbols.Symbol_Id is
     (Find (Globals, 1, Namespace, Name));

   function Clash (Name : Idents.Ident) return Symbols.Symbol_Id is
   begin
      if Marks.Is_Empty then
         return Find (Globals, 1, Symbols.No_Symbol, Name);
      end if;
      return Find (Locals, Marks.Last_Element, Symbols.No_Symbol, Name);
   end Clash;

   procedure Report_Clash
     (Pos : Source_Map.Source_Pos; Name : Idents.Ident) is
   begin
      Diagnostics.Error
        (Pos, "'" & Idents.Image (Name)
         & "' is already introduced in this scope");
   end Report_Clash;

end Names;
