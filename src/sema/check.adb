with Ada.Containers.Ordered_Maps;
with Ada.Containers.Vectors;
with Ada.Containers;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Derivation;
with Diagnostics;
with Flow;
with Idents;
with KSA;
with Names;
with Symbols;
with Tokens;
with Types;

package body Check is

   use Ada.Numerics.Big_Numbers.Big_Integers;
   use Ada.Strings.Unbounded;
   use AST;
   use Symbols;
   use Tokens;
   use Types;
   use type Idents.Ident;
   use type Ada.Containers.Count_Type;

   ---------------------------------------------------------------------
   --  분석 상태

   type Loop_Entry is record
      Node  : Node_Id;
      Label : Idents.Ident;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Entry);

   Fn_Ret        : Type_Id := No_Type;

   --  접근 없이 객체만 가리키는 객체 식: 참조 만들기의 피연산자와 그
   --  receiver 열 (§6.3.5, §6.4.4). 이들을 거치는 접근의 airside 요구는
   --  실제로 접근하는 구성에서 따진다.
   No_Access : AST.Id_Vectors.Vector;
   Airside_Depth : Natural := 0;
   Loops         : Loop_Vectors.Vector;

   function Get (N : Node_Id) return Node is (Nodes (Positive (N)));

   procedure Set_Type (N : Node_Id; T : Type_Id) is
   begin
      Nodes (Positive (N)).Ty := Natural (T);
   end Set_Type;

   function Type_Of (N : Node_Id) return Type_Id is
     (Type_Id (Nodes (Positive (N)).Ty));

   procedure Error (N : Node_Id; Message : String) is
   begin
      Diagnostics.Error (Get (N).Pos, Message);
   end Error;

   type Natural_Array is array (Positive range <>) of Natural;

   procedure Unimplemented (N : Node_Id; What : String) is
   begin
      Diagnostics.Unimplemented (Get (N).Pos, What);
   end Unimplemented;

   function Quote (T : Type_Id) return String is ("'" & Image (T) & "'");

   function Img (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   ---------------------------------------------------------------------
   --  정수 리터럴 값 (§3.5.1)

   function Digit_Value (C : Character) return Natural is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when others     => Character'Pos (C) - Character'Pos ('A') + 10);

   function Int_Value (N : Node_Id) return Big_Integer is
      Text  : constant String := To_String (Get (N).Text);
      Neg   : constant Boolean := Text (Text'First) = '-';
      First : Positive := Text'First + (if Neg then 1 else 0);
      Base  : Positive := 10;
      V     : Big_Integer := 0;
   begin
      if Get (N).Kind = N_Char_Lit then
         return To_Big_Integer (Character'Pos (Text (Text'First)));
      end if;
      if Text'Last >= First + 1 and then Text (First) = '0' then
         case Text (First + 1) is
            when 'b' | 'B' => Base := 2;
            when 'q' | 'Q' => Base := 4;
            when 'o' | 'O' => Base := 8;
            when 'x' | 'X' => Base := 16;
            when others    => null;
         end case;
         if Base /= 10 then
            First := First + 2;
         end if;
      end if;
      for C of Text (First .. Text'Last) loop
         if C /= '_' then
            V := V * To_Big_Integer (Base)
              + To_Big_Integer (Digit_Value (C));
         end if;
      end loop;
      return (if Neg then -V else V);
   end Int_Value;

   function Fits (V : Big_Integer; T : Type_Id) return Boolean is
      Bits : constant Natural := 8 * Get (T).Cells;
   begin
      if Get (T).Signed then
         return V >= -(2 ** (Bits - 1)) and then V < 2 ** (Bits - 1);
      end if;
      return V >= 0 and then V < 2 ** Bits;
   end Fits;

   ---------------------------------------------------------------------
   --  타입 해석

   function Resolve_Type (N : Node_Id) return Type_Id;

   function Resolve_Path_Type (N : Node_Id) return Type_Id is
      Path : constant Node := Get (N);
   begin
      if Path.List.Count /= 1 then
         Unimplemented (N, "qualified type paths (§10.7)");
         return Error_Type;
      end if;
      declare
         Seg  : constant Node := Get (Item (Path.List, 1));
         Name : constant String := Idents.Image (Seg.Name);
         T    : constant Type_Id := Builtin (Name);
      begin
         if Name = "verdict" then
            if Seg.List.Count /= 2 then
               Error (N, "'verdict' takes two generic arguments");
               return Error_Type;
            end if;
            return Verdict (Resolve_Type (Item (Seg.List, 1)),
                            Resolve_Type (Item (Seg.List, 2)));
         elsif Seg.List.Count > 0 then
            Unimplemented (N, "generic arguments (§4.10)");
            return Error_Type;
         elsif T /= No_Type then
            return T;
         elsif Name'Length > 2 and then Name (Name'First .. Name'First + 1)
           = "fe"
         then
            Unimplemented
              (N, "floating radix point number types (§5.4)");
            return Error_Type;
         elsif Names.Lookup (Seg.Name) /= No_Symbol then
            declare
               S : constant Symbol := Symbols.Get (Names.Lookup (Seg.Name));
            begin
               if S.Kind = Sym_Type then
                  return Type_Id (S.Ty);
               end if;
               Error (N, "'" & Name & "' is not a type");
               return Error_Type;
            end;
         end if;
         Error (N, "unknown type '" & Name & "'");
         return Error_Type;
      end;
   end Resolve_Path_Type;

   function Ref_Tribe (Op : Token_Kind) return Tribe is
     (case Op is
        when P_Dollar  => Exclusive,
        when P_Percent => Unmanaged,
        when others    => Shared);

   function Mods_Of (N : Node) return Modifiers is
     ((Volatile => N.Flags (F_Volatile), Mut => N.Flags (F_Mut),
       Atomic => N.Flags (F_Atomic)));

   --  §8.2.1의 형태는 모든 조합을 허용한다. atomic은 아직 다루지 않는다.
   function Valid_Mods (N : Node_Id; T : Tribe; M : Modifiers)
                        return Boolean is
      pragma Unreferenced (T);
   begin
      if M.Atomic then
         Unimplemented (N, "atomic references (§8.4)");
         return False;
      end if;
      return True;
   end Valid_Mods;

   --  §8.1: exclusive 참조 타입이거나 그것을 구성으로 가진 타입
   function Has_Exclusive (T : Type_Id) return Boolean is
   begin
      case Kind (T) is
         when Ty_Ref | Ty_Slice =>
            return Get (T).Ref_Tribe = Exclusive;
         when Ty_Array =>
            return Has_Exclusive (Get (T).Target);
         when Ty_Verdict =>
            return Has_Exclusive (Get (T).Pass)
              or else Has_Exclusive (Get (T).Fail);
         when Ty_Anon =>
            return (for some P of Get (T).Params => Has_Exclusive (P));
         when Ty_Composite =>
            declare
               C : constant Composite_Info := Info (T);
            begin
               return (for some F of C.Fields => Has_Exclusive (F.Ty))
                 or else (for some V of C.Variants =>
                            (for some F of V.Fields =>
                               Has_Exclusive (F.Ty)));
            end;
         when others =>
            return False;
      end case;
   end Has_Exclusive;

   --  shared 참조의 referent 타입 검사. 복합 타입의 내용이 다 들어온
   --  뒤에야 볼 수 있으므로 그 전에는 미뤄 둔다.
   type Referent_Check is record
      Node   : Node_Id;
      Target : Type_Id;
   end record;
   package Referent_Vectors is new Ada.Containers.Vectors
     (Positive, Referent_Check);
   Deferred_Referents : Referent_Vectors.Vector;
   Composites_Ready   : Boolean := False;

   procedure Check_Shared_Referent (N : Node_Id; Target : Type_Id) is
   begin
      if not Composites_Ready then
         Deferred_Referents.Append (Referent_Check'(N, Target));
      elsif Has_Exclusive (Target) then
         Error (N, "the referent type of a shared reference shall not be"
                & " or have an exclusive reference type");
      end if;
   end Check_Shared_Referent;

   function Resolve_Type (N : Node_Id) return Type_Id is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Path =>
            return Resolve_Path_Type (N);
         when N_Ref_Type | N_Slice_Type =>
            if R.Op = T_EOF then
               Error (N, "a slice type appears only as a reference");
               return Error_Type;
            end if;
            declare
               T : constant Tribe := Ref_Tribe (R.Op);
               M : constant Modifiers := Mods_Of (R);
               Target : constant Type_Id := Resolve_Type (R.A);
               Rec : Type_Rec;
            begin
               if not Valid_Mods (N, T, M) then
                  return Error_Type;
               end if;
               if T = Shared then
                  Check_Shared_Referent (N, Target);
               end if;
               Rec.Kind := (if R.Kind = N_Slice_Type then Ty_Slice
                            else Ty_Ref);
               Rec.Ref_Tribe := T;
               Rec.Mods := M;
               Rec.Target := Target;
               return Make (Rec);
            end;
         when N_Array_Type =>
            declare
               Elem : constant Type_Id := Resolve_Type (R.A);
            begin
               if Kind (R.B) /= N_Int_Lit or else Get (R.B).A /= No_Node
               then
                  Unimplemented
                    (R.B, "array lengths other than an unsuffixed integer"
                     & " literal (§6.11)");
                  return Error_Type;
               end if;
               Set_Type (R.B, Uaddr);
               if not Fits (Int_Value (R.B), Uaddr)
                 or else Int_Value (R.B) > To_Big_Integer (Integer'Last)
               then
                  Error (R.B, "array length out of range");
                  return Error_Type;
               end if;
               return Array_Of
                 (Elem, To_Integer (Int_Value (R.B)));
            end;
         when N_Never_Type =>
            return Never;
         when N_Anon_Type =>
            declare
               Fields : Type_Vectors.Vector;
            begin
               for I in 1 .. R.List.Count loop
                  Fields.Append (Resolve_Type (Item (R.List, I)));
               end loop;
               return Anon (Fields);
            end;
         when N_Infer_Type =>
            Unimplemented (N, "the inferred type '?' (§5.12)");
            return Error_Type;
         when others =>
            Error (N, "expected type");
            return Error_Type;
      end case;
   end Resolve_Type;

   ---------------------------------------------------------------------
   --  선언 수집 (§10.2 3단계)

   --  route_path가 가리키는 매개변수의 층 (§8.1.2)
   function Route_End_Of (Fn, P : Node_Id) return Route_End is
      R      : constant Node := Get (P);
      Params : constant List_Id := Get (Fn).List;
      E      : Route_End;
   begin
      if R.Flags (F_Static) then
         return (Kind => End_Static, others => <>);
      elsif R.Flags (F_Return) then
         return (Kind => End_Return, others => <>);
      elsif R.Flags (F_Self) then
         Unimplemented (P, "self parameters (§9.2)");
         return E;
      end if;
      E := (Kind => End_Layer, Param => 0, Layer => R.Sym,
            Deeper => R.Flags (F_Ellipsis));
      if R.Name /= Idents.No_Ident then
         for I in 1 .. Params.Count loop
            if Get (Item (Params, I)).Name = R.Name then
               E.Param := I - 1;
               return E;
            end if;
         end loop;
         Error (P, "no parameter '" & Idents.Image (R.Name) & "'");
      else
         declare
            Pos : constant Natural := Natural'Value (To_String (R.Text));
         begin
            if Pos < Params.Count then
               E.Param := Pos;
               return E;
            end if;
            Error (P, "no parameter at position" & Pos'Image);
         end;
      end if;
      return E;
   end Route_End_Of;

   function Fn_Type (N : Node_Id; Airside : Boolean) return Type_Id is
      R   : constant Node := Get (N);
      Rec : Type_Rec;
   begin
      Rec.Kind := Ty_Fn;
      for I in 1 .. R.List.Count loop
         Rec.Params.Append (Resolve_Type (Get (Item (R.List, I)).A));
      end loop;
      Rec.Ret := (if R.A = No_Node then Void else Resolve_Type (R.A));
      Rec.Variadic := R.Flags (F_Variadic);
      Rec.Airside := Airside;
      Rec.Invocation := R.Name2;
      if R.C /= No_Node then
         Rec.Default_Routes := False;
         for I in 1 .. Get (R.C).List.Count loop
            declare
               RN : constant Node_Id := Item (Get (R.C).List, I);
               Rt : Route;
            begin
               for J in 1 .. Get (RN).List.Count loop
                  Rt.Sources.Append
                    (Route_End_Of (N, Item (Get (RN).List, J)));
               end loop;
               Rt.Target := Route_End_Of (N, Get (RN).A);
               if Rt.Target.Kind = End_Layer
                 and then Get (Get (RN).A).Sym = 0
               then
                  Error (Get (RN).A, "the target of a route is return, static,"
                         & " or a path that carries '*'");
               end if;
               Rec.Routes.Append (Rt);
            end;
         end loop;
      end if;
      return Make (Rec);
   end Fn_Type;

   function New_Fn_Symbol (N : Node_Id; Imported : Boolean) return Symbol_Id is
      R : constant Node := Get (N);
      S : Symbol;
   begin
      if R.Name2 /= Idents.No_Ident
        and then Idents.Image (R.Name2) /= "native"
      then
         Error (N, "unknown invocation interface '"
                & Idents.Image (R.Name2) & "'");
      end if;
      S.Kind := Sym_Fn;
      S.Name := R.Name;
      S.Pos := R.Pos;
      S.Decl := Natural (N);
      S.Imported := Imported;
      S.Pub := R.Flags (F_Pub);
      --  #extern 블록의 서브루틴은 airside fn이다 (§10.5)
      S.Ty := Natural (Fn_Type (N, R.Flags (F_Airside) or else Imported));
      if Imported or else R.Flags (F_Extern) then
         S.Link_Name := To_Unbounded_String (Idents.Image (R.Name));
      end if;
      return Add (S);
   end New_Fn_Symbol;

   --  복합 타입 선언 1단계: 이름만 들인다 (선언 순서와 상관없이 참조)
   procedure Declare_Composite (N : Node_Id) is
      R : constant Node := Get (N);
      C : Composite_Info;
      S : Symbol;
   begin
      C.Name := R.Name;
      C.Decl := Natural (N);
      C.Kind := (case R.Kind is
                    when N_Struct => Struct_Type,
                    when N_Enum   => Enum_Type,
                    when others   => Contract_Type);
      C.Inverted := R.Flags (F_Inverted);
      S.Kind := Sym_Type;
      S.Name := R.Name;
      S.Pos := R.Pos;
      S.Decl := Natural (N);
      S.Pub := R.Flags (F_Pub);
      S.Ty := Natural (New_Composite (C));
      Nodes (Positive (N)).Sym := Natural (Add (S));
      Names.Declare_Global (R.Name, Symbol_Id (Get (N).Sym));
   end Declare_Composite;

   function Form_Of (R : Node) return Form_Kind is
     (if R.Flags (F_Unit) then Unit_Form
      elsif R.Flags (F_Named) then Named_Form else Unnamed_Form);

   function Field_List (L : List_Id) return Field_Vectors.Vector is
      Fields : Field_Vectors.Vector;
   begin
      for I in 1 .. L.Count loop
         declare
            FN : constant Node_Id := Item (L, I);
            FR : constant Node := Get (FN);
            F  : Field_Info;
         begin
            F.Name := FR.Name;
            F.Ty := Resolve_Type (FR.A);
            F.Pub := FR.Flags (F_Pub);
            F.Airside := FR.Flags (F_Airside);
            F.Mut := FR.Flags (F_Mut);
            F.Pad := FR.Flags (F_Pad);
            F.Default := Natural (FR.B);
            if F.Pad and then FR.B /= No_Node then
               Error (FN, "a '?' field has no default value");
            end if;
            if F.Name /= Idents.No_Ident then
               for G of Fields loop
                  if G.Name = F.Name then
                     Error (FN, "field '" & Idents.Image (F.Name)
                            & "' is declared twice");
                  end if;
               end loop;
            end if;
            Fields.Append (F);
         end;
      end loop;
      return Fields;
   end Field_List;

   --  2의 거듭제곱인 접미사 없는 정수 리터럴 (pack, align)
   function Power_Of_Two (N : Node_Id) return Natural is
   begin
      if Kind (N) = N_Int_Lit and then Get (N).A = No_Node then
         Set_Type (N, Uaddr);
         declare
            V : constant Big_Integer := Int_Value (N);
         begin
            if V > 0 and then V <= 4096 then
               declare
                  P : Natural := To_Integer (V);
               begin
                  while P mod 2 = 0 loop
                     P := P / 2;
                  end loop;
                  if P = 1 then
                     return To_Integer (V);
                  end if;
               end;
            end if;
         end;
      end if;
      Error (N, "expected a power of two greater than zero");
      return 0;
   end Power_Of_Two;

   --  값들을 모두 담는 가장 좁은 정수 타입 (§5.11.2의 3)
   function Smallest_Int (Lo, Hi : Long_Long_Integer) return Type_Id is
   begin
      for Cells of Natural_Array'(1, 2, 4) loop
         declare
            Bits : constant Natural := 8 * Cells;
         begin
            if Lo >= 0 and then Hi < 2 ** Bits then
               return Int (False, Cells);
            elsif Lo < 0 and then Lo >= -(2 ** (Bits - 1))
              and then Hi < 2 ** (Bits - 1)
            then
               return Int (True, Cells);
            end if;
         end;
      end loop;
      return Int (Lo < 0, 8);
   end Smallest_Int;

   function Wild_Count (C : Composite_Info) return Natural is
      Count : Natural := 0;
   begin
      for V of C.Variants loop
         if V.Wild then
            Count := Count + 1;
         end if;
      end loop;
      return Count;
   end Wild_Count;

   --  복합 타입 선언 2단계: 필드, 변형, 판별자, with 절
   procedure Define_Composite (N : Node_Id) is
      R : constant Node := Get (N);
      T : constant Type_Id := Type_Id (Symbols.Get (Symbol_Id (R.Sym)).Ty);
      C : Composite_Info := Info (T);
      Discrim_Given : Type_Id := No_Type;
      Explicit      : Boolean := False;  --  값을 직접 준 변형이 있다
   begin
      if R.Kind = N_Struct then
         C.Form := Form_Of (R);
         C.Fields := Field_List (R.List);
      else
         for I in 1 .. R.List.Count loop
            declare
               VN : constant Node_Id := Item (R.List, I);
               VR : constant Node := Get (VN);
               V  : Variant_Info;
            begin
               V.Name := VR.Name;
               V.Form := Form_Of (VR);
               V.Fields := Field_List (VR.List);
               V.Wild := VR.Flags (F_Wild);
               for W of C.Variants loop
                  if W.Name = V.Name then
                     Error (VN, "variant '" & Idents.Image (V.Name)
                            & "' is declared twice");
                  end if;
               end loop;
               if VR.A /= No_Node then
                  declare
                     Value : constant Big_Integer := Int_Value (VR.A);
                  begin
                     Set_Type (VR.A, Saddr);
                     if Value < -(To_Big_Integer (2) ** 62)
                       or else Value > To_Big_Integer (2) ** 62
                     then
                        Unimplemented (VR.A, "discriminant values beyond"
                                       & " 62 bits (§4.8)");
                     else
                        V.Value := Long_Long_Integer'Value
                          (To_String (Value));
                        V.Canonical := True;
                        Explicit := True;
                     end if;
                  end;
               end if;
               C.Variants.Append (V);
            end;
         end loop;

         --  wild는 많아야 하나, 직접 준 값은 서로 달라야 한다
         if Wild_Count (C) > 1 then
            Error (N, "a type has at most one wild variant");
         end if;
         for I in C.Variants.First_Index .. C.Variants.Last_Index loop
            for J in I + 1 .. C.Variants.Last_Index loop
               if C.Variants (I).Canonical and then C.Variants (J).Canonical
                 and then C.Variants (I).Value = C.Variants (J).Value
               then
                  Error (N, "discriminant value"
                         & C.Variants (J).Value'Image & " is given twice");
               end if;
            end loop;
         end loop;

         --  자동 판별자 배정 (§4.8)
         for I in C.Variants.First_Index .. C.Variants.Last_Index loop
            if not C.Variants (I).Canonical then
               declare
                  V    : Variant_Info := C.Variants (I);
                  Cand : Long_Long_Integer := 0;
               begin
                  while (for some J in C.Variants.First_Index
                                       .. C.Variants.Last_Index =>
                           (C.Variants (J).Canonical or else J < I)
                           and then C.Variants (J).Value = Cand)
                  loop
                     Cand := Cand + 1;
                  end loop;
                  V.Value := Cand;
                  C.Variants.Replace_Element (I, V);
               end;
            end if;
         end loop;

         if R.Kind = N_Contract then
            if C.Variants.Length /= 2 then
               Error (N, "a contract declares exactly two variants");
            elsif Wild_Count (C) /= 1 then
               Error (N, "exactly one variant of a contract is wild");
            end if;
            for V of C.Variants loop
               if V.Form /= Unnamed_Form or else V.Fields.Length /= 1 then
                  Error (N, "each variant of a contract has exactly one"
                         & " unnamed field");
               end if;
            end loop;
         end if;
      end if;

      --  with 절 (§4.12)
      if R.C /= No_Node then
         for I in 1 .. Get (R.C).List.Count loop
            declare
               WN   : constant Node_Id := Item (Get (R.C).List, I);
               WR   : constant Node := Get (WN);
               Word : constant String := Idents.Image (WR.Name);
            begin
               if Word = "copyable" then
                  C.Copyable := True;
               elsif Word = "variadic" then
                  Unimplemented (WN, "with variadic (§5.11.5)");
               elsif Word = "inv" then
                  if R.Kind /= N_Contract then
                     Error (WN, "only a contract declares inv");
                  else
                     C.Inv := Resolve_Type (WR.A);
                  end if;
               elsif Word = "discrim" then
                  if R.Kind = N_Struct then
                     Error (WN, "a struct has no discriminant");
                  else
                     Discrim_Given := Resolve_Type (WR.A);
                     if not Is_Int (Discrim_Given)
                       and then Discrim_Given /= Void
                       and then Kind (Discrim_Given) /= Ty_Error
                     then
                        Error (WN, "the discrim argument shall be an integer"
                               & " type or void");
                        Discrim_Given := No_Type;
                     end if;
                  end if;
               elsif Word = "repr" then
                  if Idents.Image (WR.Name2) = "pack" then
                     C.Pack := Power_Of_Two (WR.A);
                  elsif Idents.Image (WR.Name2) /= "native" then
                     Error (WN, "unknown repr '" & Idents.Image (WR.Name2)
                            & "'");
                  end if;
               elsif Word = "align" then
                  C.Min_Align := Power_Of_Two (WR.A);
               end if;
            end;
         end loop;
      end if;

      --  판별자 타입 (§5.11.2)
      if R.Kind /= N_Struct then
         declare
            Would_Be_Void : constant Boolean :=
              C.Variants.Length <= 1 and then not Explicit;
            Lo, Hi : Long_Long_Integer := 0;
         begin
            for V of C.Variants loop
               Lo := Long_Long_Integer'Min (Lo, V.Value);
               Hi := Long_Long_Integer'Max (Hi, V.Value);
            end loop;
            if Discrim_Given = Void then
               if not Would_Be_Void then
                  Error (N, "discrim(void) needs a type whose discriminant"
                         & " would be void");
               end if;
               C.Disc := Void;
            elsif Discrim_Given /= No_Type then
               if Is_Int (Discrim_Given)
                 and then (not Fits (From_String (Lo'Image), Discrim_Given)
                           or else not Fits (From_String (Hi'Image),
                                             Discrim_Given))
               then
                  Error (N, "a discriminant value does not fit in "
                         & Quote (Discrim_Given));
               end if;
               C.Disc := Discrim_Given;
            elsif Would_Be_Void then
               C.Disc := Void;
            else
               C.Disc := Smallest_Int (Lo, Hi);
            end if;
         end;
      end if;
      Set_Info (T, C);
   end Define_Composite;

   --  contract의 성공 쪽 변형 색인: contract면 wild 아닌 쪽, contract!면
   --  wild 쪽 (§7.2)
   function Success_Variant (T : Type_Id) return Positive is
      C : constant Composite_Info := Info (T);
   begin
      for I in C.Variants.First_Index .. C.Variants.Last_Index loop
         if C.Variants (I).Wild = C.Inverted then
            return I;
         end if;
      end loop;
      return 1;
   end Success_Variant;

   function Payload (T : Type_Id; Success : Boolean) return Type_Id is
   begin
      if Kind (T) = Ty_Verdict then
         return (if Success then Get (T).Pass else Get (T).Fail);
      end if;
      declare
         S : constant Positive := Success_Variant (T);
         C : constant Composite_Info := Info (T);
      begin
         for I in C.Variants.First_Index .. C.Variants.Last_Index loop
            if (I = S) = Success then
               return C.Variants (I).Fields.First_Element.Ty;
            end if;
         end loop;
         return Error_Type;
      end;
   end Payload;

   procedure Check_Against (N : Node_Id; Expected : Type_Id);

   --  복합 타입 선언 마무리: 레이아웃, 기본값, inv 짝
   procedure Finish_Composite (N : Node_Id) is
      R : constant Node := Get (N);
      T : constant Type_Id := Type_Id (Symbols.Get (Symbol_Id (R.Sym)).Ty);
   begin
      begin
         if KSA.Size (T) = Natural'Last then
            raise Program_Error;
         end if;
      exception
         when KSA.Layout_Cycle =>
            Error (N, "the layout of '" & Idents.Image (R.Name)
                   & "' requires itself");
            return;
      end;

      declare
         C : constant Composite_Info := Info (T);
      begin
         for F of C.Fields loop
            if F.Default /= 0 then
               Check_Against (Node_Id (F.Default), F.Ty);
            end if;
         end loop;
         for V of C.Variants loop
            for F of V.Fields loop
               if F.Default /= 0 then
                  Check_Against (Node_Id (F.Default), F.Ty);
               end if;
            end loop;
         end loop;

         if C.Inv /= No_Type and then Kind (C.Inv) /= Ty_Error then
            if Kind (C.Inv) /= Ty_Composite or else not Is_Contract (C.Inv)
              or else Info (C.Inv).Inv /= T
            then
               Error (N, "the type that inv names shall declare inv back to '"
                      & Idents.Image (R.Name) & "'");
            elsif Payload (C.Inv, True) /= Payload (T, False)
              or else Payload (C.Inv, False) /= Payload (T, True)
            then
               Error (N, "the payload types of an inverted pair shall be"
                      & " swapped");
            end if;
         end if;
      end;
   end Finish_Composite;

   procedure Collect (Unit : Node_Id) is
      U : constant Node := Get (Unit);
   begin
      --  1단계: 이름
      for I in 1 .. U.List.Count loop
         declare
            N : constant Node_Id := Item (U.List, I);
            R : constant Node := Get (N);
         begin
            if Names.Clash (R.Name) /= No_Symbol then
               Names.Report_Clash (R.Pos, R.Name);
            end if;
            if R.Kind in N_Struct | N_Enum | N_Contract then
               Declare_Composite (N);
            end if;
         end;
      end loop;

      --  2단계: 타입의 내용
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) in N_Struct | N_Enum | N_Contract then
            Define_Composite (Item (U.List, I));
         end if;
      end loop;

      Composites_Ready := True;
      for D of Deferred_Referents loop
         Check_Shared_Referent (D.Node, D.Target);
      end loop;
      Deferred_Referents.Clear;

      --  3단계: 서브루틴과 #extern
      for I in 1 .. U.List.Count loop
         declare
            N : constant Node_Id := Item (U.List, I);
            R : constant Node := Get (N);
         begin
            case R.Kind is
               when N_Fn =>
                  declare
                     S : constant Symbol_Id := New_Fn_Symbol (N, False);
                  begin
                     Nodes (Positive (N)).Sym := Natural (S);
                     Names.Declare_Global (R.Name, S);
                  end;
               when N_Extern =>
                  if R.Flags (F_Xlat) then
                     Unimplemented (N, "#extern(xlat) (§10.5)");
                  end if;
                  declare
                     NS_Rec : Symbol;
                     NS     : Symbol_Id;
                  begin
                     NS_Rec.Kind := Sym_Namespace;
                     NS_Rec.Name := R.Name;
                     NS_Rec.Pos := R.Pos;
                     NS_Rec.Decl := Natural (N);
                     NS := Add (NS_Rec);
                     Nodes (Positive (N)).Sym := Natural (NS);
                     Names.Declare_Global (R.Name, NS);
                     for J in 1 .. R.List.Count loop
                        declare
                           M  : constant Node_Id := Item (R.List, J);
                           MR : constant Node := Get (M);
                           S  : Symbol_Id;
                        begin
                           if Names.Lookup_Member (NS, MR.Name) /= No_Symbol
                           then
                              Names.Report_Clash (MR.Pos, MR.Name);
                           end if;
                           S := New_Fn_Symbol (M, True);
                           Nodes (Positive (M)).Sym := Natural (S);
                           Names.Declare_Member (NS, MR.Name, S);
                        end;
                     end loop;
                  end;
               when others =>
                  null;
            end case;
         end;
      end loop;

      --  4단계: 레이아웃과 기본값
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) in N_Struct | N_Enum | N_Contract then
            Finish_Composite (Item (U.List, I));
         end if;
      end loop;
   end Collect;

   ---------------------------------------------------------------------
   --  식 검사

   function Check_Expr (N : Node_Id; Expected : Type_Id) return Type_Id;

   --  §8.2.3 참조 캐스트의 네 가지 변환
   type Conversion is (Same, Landside, Needs_Airside, Forbidden);

   function Ref_Conversion (From, To : Type_Id) return Conversion is
      F      : constant Type_Rec := Get (From);
      T      : constant Type_Rec := Get (To);
      Result : Conversion := Landside;

      F_Mut  : constant Boolean := F.Mods.Mut;
      T_Mut  : constant Boolean := T.Mods.Mut;
      F_Atom : constant Boolean := F.Mods.Atomic;
      T_Atom : constant Boolean := T.Mods.Atomic;

      procedure Note (C : Conversion; Modifier : Boolean := True) is
         --  비관리 원천에서는 수식자 변환의 실패가 airside 요구가 된다
         Effective : constant Conversion :=
           (if C = Forbidden and then Modifier and then F.Ref_Tribe = Unmanaged
            then Needs_Airside else C);
      begin
         if Effective > Result then
            Result := Effective;
         end if;
      end Note;

   begin
      if From = To then
         return Same;
      end if;
      case F.Ref_Tribe is
         when Exclusive => null;
         when Shared =>
            if T.Ref_Tribe = Exclusive then
               Note (Forbidden, Modifier => False);
            end if;
         when Unmanaged =>
            if T.Ref_Tribe /= Unmanaged then
               Note (Needs_Airside, Modifier => False);
            end if;
      end case;
      if F.Mods.Volatile and then not T.Mods.Volatile then
         Note (Forbidden);
      end if;
      if T_Mut and then not F_Mut then
         Note (Forbidden);
      end if;
      if F_Atom and then not T_Atom then
         Note (Needs_Airside);
      end if;
      return Result;
   end Ref_Conversion;

   --  decay: 대상 타입이 같고 airside 없이 허용되는 캐스트 (§8.2.3)
   function Decays (From, To : Type_Id) return Boolean is
     (Kind (From) = Ty_Ref and then Kind (To) = Ty_Ref
      and then Get (From).Target = Get (To).Target
      and then Ref_Conversion (From, To) in Same | Landside);

   package Decay_Maps is new Ada.Containers.Ordered_Maps (Node_Id, Type_Id);
   Decay_Map : Decay_Maps.Map;

   function Decayed (N : AST.Node_Id) return Natural is
     (if Decay_Map.Contains (N) then Natural (Decay_Map.Element (N))
      else 0);

   --  N을 검사하고 그 타입이 Expected에 배정될 수 있는지 본다 (§6.8)
   procedure Check_Against (N : Node_Id; Expected : Type_Id) is
      T : constant Type_Id := Check_Expr (N, Expected);
   begin
      if T = Expected or else Kind (T) in Ty_Error | Ty_Never
        or else Kind (Expected) = Ty_Error
      then
         return;
      elsif Decays (T, Expected) then
         Decay_Map.Include (N, Expected);
         return;
      end if;
      Error (N, "expected " & Quote (Expected) & ", found " & Quote (T));
   end Check_Against;

   --  합성으로 타입이 정해지지 않는 식: 접미사 없는 정수 리터럴과 그
   --  부호 붙임, 그런 피연산자끼리의 산술 (§5.12)
   function Undetermined (N : Node_Id) return Boolean is
      R : constant Node := (if N = No_Node then (others => <>) else Get (N));
   begin
      case R.Kind is
         when N_Int_Lit =>
            return R.A = No_Node;
         when N_Unary =>
            return R.Op in P_Minus | P_Plus | P_Bang
              and then Undetermined (R.A);
         when N_Binary =>
            return R.Op in P_Plus | P_Minus | P_Star | P_Slash | P_Percent
                         | P_Amp | P_Pipe | P_Caret
              and then Undetermined (R.A) and then Undetermined (R.B);
         when others =>
            return False;
      end case;
   end Undetermined;

   --  범위 검사 없이 리터럴의 타입만 정한다
   function Literal_Type (N : Node_Id; Expected : Type_Id) return Type_Id
   is
      R : constant Node := Get (N);
      T : Type_Id;
   begin
      if R.A /= No_Node then
         T := Resolve_Type (R.A);
         if Kind (T) = Ty_Error then
            return T;
         elsif not Is_Int (T) then
            Error (N, "the type suffix of an integer literal shall name an"
                   & " integer type");
            return Error_Type;
         end if;
      elsif Is_Int (Expected) then
         T := Expected;
      elsif Expected = No_Type then
         --  합성이 정해지지 않으면 기본 타입 (§3.5.2)
         T := Saddr;
      elsif Kind (Expected) = Ty_Error then
         return Expected;
      else
         Error (N, "an integer literal cannot have type " & Quote (Expected));
         return Error_Type;
      end if;
      return T;
   end Literal_Type;

   function Check_Int_Literal (N : Node_Id; Expected : Type_Id)
                               return Type_Id
   is
      T : constant Type_Id := Literal_Type (N, Expected);
   begin
      if Is_Int (T) and then not Fits (Int_Value (N), T) then
         Error (N, "value does not fit in " & Quote (T));
         return Error_Type;
      end if;
      return T;
   end Check_Int_Literal;

   --  airside 안에서만 허용되는 연산 (§2.7)
   procedure Require_Airside (N : Node_Id; What : String) is
   begin
      if Airside_Depth = 0 then
         Error (N, What & " requires airside");
      end if;
   end Require_Airside;

   --  값 위치의 경로가 가리키는 것: 바인딩이나 서브루틴, 타입, 변형
   type Value_Kind is (V_None, V_Symbol, V_Type, V_Variant);

   type Value_Target is record
      Kind    : Value_Kind := V_None;
      Sym     : Symbol_Id := No_Symbol;
      --  V_Type, V_Variant. 인자를 생략한 verdict면 No_Type.
      Ty      : Type_Id := No_Type;
      Variant : Natural := 0;
   end record;

   function Resolve_Value (N : Node_Id) return Value_Target is
      Path   : constant Node := Get (Get (N).A);
      Count  : constant Natural := Path.List.Count;
      First  : constant Node := Get (Item (Path.List, 1));
      Name   : constant String := Idents.Image (First.Name);
      S      : Symbol_Id := Names.Lookup (First.Name);
      Result : Value_Target;

      function Seg (I : Positive) return Node is (Get (Item (Path.List, I)));

      function Not_Found (What : Idents.Ident) return Value_Target is
      begin
         Error (N, "unknown name '" & Idents.Image (What) & "'");
         return (others => <>);
      end Not_Found;

   begin
      for I in 1 .. Count loop
         if Seg (I).List.Count > 0
           and then not (I = 1 and then S = No_Symbol
                         and then Name = "verdict")
         then
            Unimplemented (N, "generic arguments (§4.10)");
            return Result;
         end if;
      end loop;

      if S = No_Symbol then
         if Name = "verdict" then
            if First.List.Count = 2 then
               Result.Ty := Verdict (Resolve_Type (Item (First.List, 1)),
                                     Resolve_Type (Item (First.List, 2)));
            elsif First.List.Count /= 0 then
               Error (N, "'verdict' takes two generic arguments");
               return Result;
            end if;
            if Count = 1 then
               Result.Kind := V_Type;
            elsif Count = 2 and then Idents.Image (Seg (2).Name) = "Pass" then
               Result := (V_Variant, No_Symbol, Result.Ty, 1);
            elsif Count = 2 and then Idents.Image (Seg (2).Name) = "Fail" then
               Result := (V_Variant, No_Symbol, Result.Ty, 2);
            else
               return Not_Found (Seg (Count).Name);
            end if;
            return Result;
         elsif Builtin (Name) /= No_Type and then Count = 1 then
            return (V_Type, No_Symbol, Builtin (Name), 0);
         end if;
         return Not_Found (First.Name);
      end if;

      for I in 2 .. Count loop
         case Symbols.Get (S).Kind is
            when Sym_Namespace =>
               S := Names.Lookup_Member (S, Seg (I).Name);
               if S = No_Symbol then
                  return Not_Found (Seg (I).Name);
               end if;
            when Sym_Type =>
               declare
                  T : constant Type_Id := Type_Id (Symbols.Get (S).Ty);
               begin
                  if I = Count and then Is_Variant (T) then
                     for V in Info (T).Variants.First_Index
                              .. Info (T).Variants.Last_Index
                     loop
                        if Variant (T, V).Name = Seg (I).Name then
                           return (V_Variant, S, T, V);
                        end if;
                     end loop;
                  end if;
                  return Not_Found (Seg (I).Name);
               end;
            when others =>
               Error (N, "'" & Idents.Image (Symbols.Get (S).Name)
                      & "' is not a namespace");
               return Result;
         end case;
      end loop;

      if Symbols.Get (S).Kind = Sym_Type then
         return (V_Type, S, Type_Id (Symbols.Get (S).Ty), 0);
      end if;
      Nodes (Positive (N)).Sym := Natural (S);
      return (V_Symbol, S, No_Type, 0);
   end Resolve_Value;

   --  바인딩이나 서브루틴을 가리켜야 하는 이름 식의 심볼
   function Resolve_Name (N : Node_Id) return Symbol_Id is
      V : constant Value_Target := Resolve_Value (N);
   begin
      if V.Kind = V_Symbol then
         return V.Sym;
      elsif V.Kind /= V_None then
         Error (N, "expected a subroutine or a binding, found a type");
      end if;
      return No_Symbol;
   end Resolve_Name;

   function Field_Of (T : Type_Id; Index : Positive) return Field_Info;

   --  필드 식의 receiver 타입 (참조 투명성 뒤)
   function Receiver_Base (N : Node_Id) return Type_Id is
     (if Kind (Type_Of (Get (N).A)) = Ty_Ref
      then Get (Type_Of (Get (N).A)).Target else Type_Of (Get (N).A));

   --  field mutability를 가진 필드를 가리키는 필드 식 (§4.6.1)
   function Names_Mut_Field (N : Node_Id) return Boolean is
     (Kind (N) = N_Field and then Get (N).Sym /= 0
      and then Kind (Receiver_Base (N)) in Ty_Composite | Ty_Anon
      and then Field_Of (Receiver_Base (N), Get (N).Sym).Mut);

   --  저장을 허락하는가 (§6.3.2, §8.1): 다중 대입 바인딩, mut을 가진
   --  참조를 거친 역참조, 다중 대입 필드(airside 안의 field mutability),
   --  또는 그런 객체 안을 참조 없이 고르는 필드 식
   function Storable (N : Node_Id) return Boolean is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Name =>
            return R.Sym /= 0
              and then Symbols.Get (Symbol_Id (R.Sym)).Kind
                       in Sym_Local | Sym_Param
              and then Symbols.Get (Symbol_Id (R.Sym)).Mutable;
         when N_Unary =>
            return R.Op = P_Star and then Kind (Type_Of (R.A)) = Ty_Ref
              and then Get (Type_Of (R.A)).Mods.Mut;
         when N_Field =>
            if Airside_Depth > 0 and then Names_Mut_Field (N) then
               return True;
            elsif Kind (Type_Of (R.A)) = Ty_Ref then
               return Get (Type_Of (R.A)).Mods.Mut;
            end if;
            return Storable (R.A);
         when others =>
            return False;
      end case;
   end Storable;

   --  airside였다면 저장할 수 있었는가: 참조를 거치지 않는 필드 선택
   --  경로에 field mutability를 가진 필드가 있다
   function Through_Mut_Field (N : Node_Id) return Boolean is
     (Kind (N) = N_Field
      and then (Names_Mut_Field (N)
                or else (Kind (Type_Of (Get (N).A)) /= Ty_Ref
                         and then Through_Mut_Field (Get (N).A))));

   --  구조체·익명 구조체의 receiver 타입에서 필드 정보 (Index는 1부터)
   function Field_Of (T : Type_Id; Index : Positive) return Field_Info is
   begin
      if Kind (T) = Ty_Anon then
         return F : Field_Info do
            F.Ty := Get (T).Params (Index);
            F.Pub := True;
         end return;
      end if;
      return Field (T, Index);
   end Field_Of;

   --  저장할 수 있는 객체 식인가 (§6.8)
   procedure Check_Place (N : Node_Id) is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Name =>
            if R.Sym /= 0 then
               declare
                  S : constant Symbol := Symbols.Get (Symbol_Id (R.Sym));
               begin
                  if S.Kind not in Sym_Local | Sym_Param then
                     Error (N, "'" & Idents.Image (S.Name)
                            & "' is not an object");
                  elsif not S.Mutable and then not S.Deferred then
                     --  지연 초기화한 바인딩은 흐름 분석이 경로마다 한
                     --  번인지 본다
                     Error (N, "'" & Idents.Image (S.Name)
                            & "' is a single-assignment binding");
                  end if;
               end;
            end if;
         when N_Field =>
            if Kind (Type_Of (R.A)) in Ty_Array then
               Error (N, "a projection is a value");
            elsif R.Sym /= 0 and then not Storable (N) then
               if Through_Mut_Field (N) then
                  --  airside에서만 다중 대입 필드다 (§4.6.1, §6.3.2)
                  Require_Airside (N, "a store through field mutability");
               else
                  Error (N, "a store to this field is not permitted");
               end if;
            end if;
         when N_Unary =>
            if R.Op = P_Star then
               declare
                  RT : constant Type_Id := Type_Of (R.A);
               begin
                  if Kind (RT) = Ty_Ref and then not Get (RT).Mods.Mut then
                     Error (N, "a store through " & Quote (RT)
                            & " is not permitted");
                  end if;
               end;
            else
               Error (N, "expected an object expression");
            end if;
         when others =>
            Error (N, "expected an object expression");
      end case;
   end Check_Place;

   function Check_Call (N : Node_Id) return Type_Id is
      R      : constant Node := Get (N);
      S      : Symbol_Id;
      Fn     : Type_Rec;
      Params : Natural;
   begin
      if Kind (R.A) /= N_Name then
         Unimplemented (N, "invocation through a subroutine pointer"
                        & " (§6.3.1)");
         return Error_Type;
      end if;
      S := Resolve_Name (R.A);
      if S = No_Symbol then
         return Error_Type;
      elsif Symbols.Get (S).Kind /= Sym_Fn then
         Unimplemented (N, "invocation through a subroutine pointer"
                        & " (§6.3.1)");
         return Error_Type;
      end if;
      Fn := Get (Type_Id (Symbols.Get (S).Ty));
      Set_Type (R.A, Type_Id (Symbols.Get (S).Ty));
      Params := Natural (Fn.Params.Length);

      if R.List.Count < Params
        or else (R.List.Count > Params and then not Fn.Variadic)
      then
         Error (N, "'" & Idents.Image (Symbols.Get (S).Name) & "' takes"
                & Params'Image & " argument"
                & (if Params = 1 then "" else "s") & ", given"
                & R.List.Count'Image);
      end if;

      for I in 1 .. R.List.Count loop
         declare
            Arg : constant Node_Id := Item (R.List, I);
         begin
            if I <= Params then
               Check_Against (Arg, Fn.Params.Element (I));
            else
               --  가변 인자: variadic bound를 만족하는 타입 (§9.7.5)
               declare
                  T : constant Type_Id := Check_Expr (Arg, No_Type);
               begin
                  if Kind (T) not in Ty_Int | Ty_Ref | Ty_Error then
                     Unimplemented (Arg, "variadic arguments of type "
                                    & Quote (T) & " (§9.7.5)");
                  end if;
               end;
            end if;
         end;
      end loop;

      if Fn.Airside then
         Require_Airside (N, "invoking an airside subroutine");
      end if;
      return Fn.Ret;
   end Check_Call;

   --  객체 식인가: 바인딩, 필드, 역참조 (§6.1)
   function Is_Object_Expr (N : Node_Id) return Boolean is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Name =>
            return R.Sym /= 0
              and then Symbols.Get (Symbol_Id (R.Sym)).Kind
                       in Sym_Local | Sym_Param;
         when N_Field =>
            return R.Sym /= 0;
         when N_Unary =>
            return R.Op = P_Star;
         when others =>
            return False;
      end case;
   end Is_Object_Expr;

   --  객체 식이 객체에 닿을 때 거치는 가장 가까운 참조의 타입
   function Nearest_Ref (N : Node_Id) return Type_Id is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Unary =>
            return (if R.Op = P_Star then Type_Of (R.A) else No_Type);
         when N_Field =>
            if Kind (Type_Of (R.A)) = Ty_Ref then
               return Type_Of (R.A);
            end if;
            return Nearest_Ref (R.A);
         when others =>
            return No_Type;
      end case;
   end Nearest_Ref;

   --  참조 만들기 (§6.4.4)와 재참조 (§8.2.3)
   function Check_Reference (N : Node_Id) return Type_Id is
      R      : constant Node := Get (N);
      T      : constant Tribe := Ref_Tribe (R.Op);
      M      : Modifiers := Mods_Of (R);
      Stores : constant Boolean := M.Mut;
   begin
      if not Valid_Mods (N, T, M) then
         return Error_Type;
      end if;

      if Kind (R.A) = N_Unary and then Get (R.A).Op = P_Star then
         declare
            Src : constant Type_Id := Check_Expr (Get (R.A).A, No_Type);
         begin
            if Kind (Src) = Ty_Error then
               return Src;
            elsif Kind (Src) /= Ty_Ref then
               Error (R.A, "operand of '*' shall be a thin reference");
               return Error_Type;
            end if;
            Set_Type (R.A, Get (Src).Target);
            declare
               Target : constant Type_Id := Ref (Get (Src).Target, T, M);
            begin
               case Ref_Conversion (Src, Target) is
                  when Forbidden =>
                     Error (N, Quote (Src) & " cannot become "
                            & Quote (Target));
                     return Error_Type;
                  when Needs_Airside =>
                     Require_Airside (N, "this re-reference");
                  when Same | Landside =>
                     null;
               end case;
               if T = Shared then
                  Check_Shared_Referent (N, Get (Src).Target);
               end if;
               return Target;
            end;
         end;
      end if;

      --  피연산자와 참조를 거치지 않는 receiver 열은 접근하지 않는다
      declare
         X : Node_Id := R.A;
      begin
         while Kind (X) in N_Field | N_Unary loop
            exit when Kind (X) = N_Unary and then Get (X).Op /= P_Star;
            No_Access.Append (X);
            exit when Kind (X) = N_Unary;
            X := Get (X).A;
         end loop;
      end;
      declare
         Operand : constant Type_Id := Check_Expr (R.A, No_Type);
      begin
         if Kind (Operand) = Ty_Error then
            return Operand;
         elsif Kind (Operand) in Ty_Void | Ty_Never then
            Error (N, "no reference to a value of type " & Quote (Operand));
            return Error_Type;
         end if;
         if Is_Object_Expr (R.A) then
            declare
               Near : constant Type_Id := Nearest_Ref (R.A);
            begin
               if T /= Unmanaged and then Near /= No_Type
                 and then Get (Near).Ref_Tribe = Unmanaged
               then
                  Require_Airside (N, "a managed reference to an object"
                                   & " reached through an unmanaged"
                                   & " reference");
               end if;
               if T = Exclusive and then Near /= No_Type
                 and then Get (Near).Ref_Tribe = Shared
               then
                  --  §6.4.4: shared 참조를 거쳐 exclusive를 만들 수 없다
                  Error (N, "an exclusive reference to an object reached"
                         & " through " & Quote (Near));
               end if;
               if Stores and then not Storable (R.A) then
                  if Through_Mut_Field (R.A) then
                     Require_Airside (N, "a store-permitting reference"
                                      & " through field mutability");
                  else
                     Error (N, "a store-permitting reference needs a"
                            & " storable object");
                  end if;
               end if;
               if Near /= No_Type and then Get (Near).Mods.Volatile then
                  M.Volatile := True;
               end if;
            end;
         elsif Stores and then T /= Unmanaged then
            --  값 식은 임시 객체를 가리킨다: 저장 가능한 객체가 아니다
            Error (N, "a store-permitting managed reference needs a storable"
                   & " object");
         end if;
         if T = Shared then
            Check_Shared_Referent (N, Operand);
         end if;
         return Ref (Operand, T, M);
      end;
   end Check_Reference;

   function Check_Unary (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
   begin
      case R.Op is
         when P_Minus | P_Plus =>
            --  음수 리터럴: '-'와 리터럴이 함께 부정을 나타낸다 (§3.5.1)
            if R.Op = P_Minus and then Kind (R.A) = N_Int_Lit then
               declare
                  T : constant Type_Id := Literal_Type (R.A, Expected);
               begin
                  Set_Type (R.A, T);
                  if Is_Int (T) and then Fits (-Int_Value (R.A), T) then
                     declare
                        Folded : Node := Get (N);
                     begin
                        Folded.Kind := N_Int_Lit;
                        Folded.Text := "-" & Get (R.A).Text;
                        Folded.A := Get (R.A).A;
                        Nodes.Replace_Element (Positive (N), Folded);
                     end;
                     return T;
                  elsif Is_Int (T) and then not Fits (Int_Value (R.A), T)
                  then
                     Error (R.A, "value does not fit in " & Quote (T));
                     return Error_Type;
                  end if;
                  --  부정이 맞지 않으면 리터럴은 제 값을 나타내고 '-'는
                  --  보통의 단항 부정이다
                  return T;
               end;
            end if;
            declare
               T : constant Type_Id :=
                 Check_Expr (R.A, (if Is_Int (Expected) then Expected
                                   else No_Type));
            begin
               if Kind (T) /= Ty_Error and then not Is_Int (T) then
                  Error (N, "operand of '" & Spelling (R.Op)
                         & "' shall be an integer");
                  return Error_Type;
               end if;
               return T;
            end;

         when P_Bang =>
            declare
               T : constant Type_Id :=
                 Check_Expr (R.A, (if Is_Int (Expected) then Expected
                                   else No_Type));
            begin
               if Kind (T) = Ty_Verdict then
                  --  극성 반전: verdict[T, F] → verdict[F, T] (§7.2.1)
                  return Verdict (Get (T).Fail, Get (T).Pass);
               elsif Is_Contract (T) then
                  if Info (T).Inv = No_Type then
                     Error (N, "contract '" & Image (T)
                            & "' declares no inv");
                     return Error_Type;
                  end if;
                  return Info (T).Inv;
               elsif Kind (T) /= Ty_Error and then not Is_Int (T) then
                  Error (N, "operand of '!' shall be an integer or a"
                         & " contract");
                  return Error_Type;
               end if;
               return T;
            end;

         when P_Star =>
            declare
               T : constant Type_Id := Check_Expr (R.A, No_Type);
            begin
               if Kind (T) = Ty_Error then
                  return T;
               elsif Kind (T) /= Ty_Ref then
                  Error (N, "operand of '*' shall be a thin reference");
                  return Error_Type;
               end if;
               if Get (T).Ref_Tribe = Unmanaged then
                  Require_Airside
                    (N, "dereferencing an unmanaged reference");
               elsif Get (T).Ref_Tribe = Shared and then Get (T).Mods.Mut
                 and then not No_Access.Contains (N)
               then
                  --  §8.1: 공유 mut 참조를 거친 접근
                  Require_Airside (N, "an access through a shared mut"
                                   & " reference");
               end if;
               return Get (T).Target;
            end;

         when P_Amp | P_Dollar | P_Percent =>
            return Check_Reference (N);

         when others =>
            Error (N, "unknown unary operator");
            return Error_Type;
      end case;
   end Check_Unary;

   function Check_Binary (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
      L, Rt : Type_Id;

      --  두 피연산자를 같은 타입으로 맞춘다. 앞쪽이 합성되지 않으면
      --  뒤쪽을 먼저 본다 (검사 순서일 뿐, 평가 순서는 아니다).
      procedure Operands (Hint : Type_Id) is
      begin
         if Undetermined (R.A) and then not Undetermined (R.B) then
            Rt := Check_Expr (R.B, No_Type);
            L := Check_Expr (R.A, Rt);
         else
            L := Check_Expr (R.A, (if Undetermined (R.A) then Hint
                                   else No_Type));
            Rt := Check_Expr (R.B, L);
         end if;
         if L /= Rt and then Kind (L) /= Ty_Error
           and then Kind (Rt) /= Ty_Error
         then
            Error (N, "operands of '" & Spelling (R.Op) & "' have types "
                   & Quote (L) & " and " & Quote (Rt));
            L := Error_Type;
         end if;
      end Operands;

   begin
      case R.Op is
         when P_Plus | P_Minus | P_Star | P_Slash | P_Percent
            | P_Amp | P_Pipe | P_Caret =>
            Operands (if Is_Int (Expected) then Expected else No_Type);
            if Kind (L) /= Ty_Error and then not Is_Int (L) then
               if Kind (L) = Ty_Ref and then R.Op in P_Plus | P_Minus then
                  Unimplemented (N, "unmanaged reference arithmetic (§8.5)");
               else
                  Error (N, "operands of '" & Spelling (R.Op)
                         & "' shall be integers");
               end if;
               return Error_Type;
            end if;
            return L;

         when P_Plus_Pipe | P_Minus_Pipe | P_Star_Pipe | P_Slash_Pipe =>
            Unimplemented (N, "saturating integer arithmetic (§6.5.2)");
            return Error_Type;
         when P_Plus_At | P_Star_At =>
            Unimplemented (N, "widening integer arithmetic (§6.5.3)");
            return Error_Type;
         when P_Shl | P_Shr =>
            Unimplemented (N, "shift operators (§6.6.2)");
            return Error_Type;

         when P_Eq_Eq | P_Ne | P_Lt | P_Gt | P_Le | P_Ge =>
            Operands (No_Type);
            if Kind (L) /= Ty_Error and then not Is_Int (L) then
               Unimplemented (N, "comparison of " & Quote (L) & " (§6.7)");
               return Error_Type;
            end if;
            return Bool;

         when K_And | K_Or | K_Xor =>
            L := Check_Expr (R.A, No_Type);
            Rt := Check_Expr (R.B, No_Type);
            if (Kind (L) /= Ty_Error and then not Is_Contract (L))
              or else (Kind (Rt) /= Ty_Error and then not Is_Contract (Rt))
            then
               Error (N, "operands of '" & Spelling (R.Op)
                      & "' shall be of a contract type");
            end if;
            return Bool;

         when others =>
            Error (N, "unknown binary operator");
            return Error_Type;
      end case;
   end Check_Binary;

   ---------------------------------------------------------------------
   --  초기식도 타입 표기도 없는 let의 타입 (§5.12)
   --
   --  바인딩의 타입은 그 바인딩을 앞 피연산자로 하는 단순 대입들의 뒤
   --  피연산자들(그런 바인딩을 언급하는 것은 빼고)의 공통 타입이다.
   --  선언 뒤의 스코프를 훑어 그런 피연산자를 센다. 모두 합성으로
   --  타입이 정해지지 않는 리터럴이면 기본 타입 saddr, 하나도 없으면
   --  void다. 합성되는 피연산자가 있으면 바인딩은 보류 상태(타입 0)로
   --  두고, 검사 순서에서 처음 만나는 그것의 타입으로 정한다. 그 전의
   --  리터럴 피연산자는 그때 검사한다. 보류 중인 바인딩을 쓰는 것은
   --  이 구현이 아직 다루지 못한다.

   type Pending_Assign is record
      Sym     : Symbol_Id;
      Assign  : Node_Id;
      Checked : Boolean;  --  뒤 피연산자를 이미 검사했다(발산식)
   end record;
   package Pending_Vectors is new Ada.Containers.Vectors
     (Positive, Pending_Assign);

   Pending : Pending_Vectors.Vector;

   --  본문을 미리 훑어 얻는 것: 그런 바인딩(타입 표기도 초기식도 없는
   --  let)으로의 단순 대입과, 그 뒤 피연산자가 가리키는 그런 바인딩.
   --  바인딩은 let 노드로 나타낸다.
   type Assign_Info is record
      Assign   : Node_Id;
      Target   : Node_Id;
      Excluded : Boolean := False;  --  Target에 draws on하는 바인딩을 가리킨다
   end record;
   package Assign_Vectors is new Ada.Containers.Vectors
     (Positive, Assign_Info);

   type Edge is record
      From, To : Node_Id;  --  From의 대입 Via가 To를 가리킨다
      Via      : Node_Id;
   end record;
   package Edge_Vectors is new Ada.Containers.Vectors (Positive, Edge);

   Assigns : Assign_Vectors.Vector;
   Edges   : Edge_Vectors.Vector;
   Untyped : Id_Vectors.Vector;  --  그런 바인딩의 let 전부

   --  group의 대표(가장 작은 let 노드)와 group이 얻은 타입
   package Node_Maps is new Ada.Containers.Ordered_Maps (Node_Id, Node_Id);
   package Group_Type_Maps is new Ada.Containers.Ordered_Maps
     (Node_Id, Type_Id);
   Group_Of    : Node_Maps.Map;
   Group_Types : Group_Type_Maps.Map;

   --  경로 하나짜리 이름 식의 이름, 아니면 No_Ident
   function Simple_Name (N : Node_Id) return Idents.Ident is
   begin
      if Kind (N) /= N_Name or else Get (N).A = No_Node
        or else Get (Get (N).A).List.Count /= 1
        or else Get (Item (Get (Get (N).A).List, 1)).List.Count /= 0
      then
         return Idents.No_Ident;
      end if;
      return Get (Item (Get (Get (N).A).List, 1)).Name;
   end Simple_Name;

   procedure Collect_Untyped (Body_N : Node_Id) is
      Visible : Id_Vectors.Vector;  --  보이는 그런 바인딩의 let

      function Resolve (N : Node_Id) return Node_Id is
         Name : constant Idents.Ident := Simple_Name (N);
      begin
         if Name /= Idents.No_Ident then
            for I in reverse 1 .. Natural (Visible.Length) loop
               if Get (Visible (I)).Name = Name then
                  return Visible (I);
               end if;
            end loop;
         end if;
         return No_Node;
      end Resolve;

      procedure Names_In (N : Node_Id; From, Via : Node_Id) is
      begin
         if N = No_Node or else Kind (N) in Type_Node | N_Fn then
            return;
         end if;
         declare
            R : constant Node := Get (N);
            Z : constant Node_Id := Resolve (N);
         begin
            if Z /= No_Node then
               Edges.Append (Edge'(From, Z, Via));
               return;
            end if;
            Names_In (R.A, From, Via);
            Names_In (R.B, From, Via);
            Names_In (R.C, From, Via);
            for I in 1 .. R.List.Count loop
               Names_In (Item (R.List, I), From, Via);
            end loop;
         end;
      end Names_In;

      procedure Walk (N : Node_Id) is
      begin
         if N = No_Node or else Kind (N) in Type_Node | N_Fn then
            return;
         end if;
         declare
            R : constant Node := Get (N);
         begin
            if R.Kind = N_Block then
               declare
                  Mark : constant Ada.Containers.Count_Type := Visible.Length;
               begin
                  for I in 1 .. R.List.Count loop
                     declare
                        It : constant Node_Id := Item (R.List, I);
                     begin
                        Walk (It);
                        if Kind (It) = N_Let and then Get (It).A = No_Node
                          and then Get (It).B = No_Node
                        then
                           Visible.Append (It);
                           Untyped.Append (It);
                        end if;
                     end;
                  end loop;
                  Visible.Set_Length (Mark);
               end;
               return;
            end if;
            if R.Kind = N_Assign and then R.Op = P_Eq then
               declare
                  L : constant Node_Id := Resolve (R.A);
               begin
                  if L /= No_Node then
                     Assigns.Append (Assign_Info'(N, L, False));
                     Names_In (R.B, L, N);
                  end if;
               end;
            end if;
            Walk (R.A);
            Walk (R.B);
            Walk (R.C);
            for I in 1 .. R.List.Count loop
               Walk (Item (R.List, I));
            end loop;
         end;
      end Walk;

      --  From이 To에 draws on하는가 (From = To 포함)
      function Reaches (From, To : Node_Id) return Boolean is
         Seen  : Id_Vectors.Vector;
         Stack : Id_Vectors.Vector;
      begin
         Stack.Append (From);
         while not Stack.Is_Empty loop
            declare
               X : constant Node_Id := Stack.Last_Element;
            begin
               Stack.Delete_Last;
               if X = To then
                  return True;
               elsif not Seen.Contains (X) then
                  Seen.Append (X);
                  for E of Edges loop
                     if E.From = X then
                        Stack.Append (E.To);
                     end if;
                  end loop;
               end if;
            end;
         end loop;
         return False;
      end Reaches;
   begin
      Assigns.Clear;
      Edges.Clear;
      Untyped.Clear;
      Group_Of.Clear;
      Group_Types.Clear;
      Walk (Body_N);
      --  서로 draws on하는 바인딩들이 group을 이룬다
      for L of Untyped loop
         declare
            Rep : Node_Id := L;
         begin
            for M of Untyped loop
               if M < Rep and then Reaches (L, M) and then Reaches (M, L)
               then
                  Rep := M;
               end if;
            end loop;
            Group_Of.Insert (L, Rep);
         end;
      end loop;
      --  group의 바인딩을 가리키는 피연산자는 공통 타입에서 빠진다
      for A of Assigns loop
         for E of Edges loop
            if E.Via = A.Assign
              and then Group_Of (E.To) = Group_Of (A.Target)
            then
               A.Excluded := True;
            end if;
         end loop;
      end loop;
   end Collect_Untyped;

   function Info_Of (Assign : Node_Id) return Assign_Info is
   begin
      for A of Assigns loop
         if A.Assign = Assign then
            return A;
         end if;
      end loop;
      return (No_Node, No_Node, False);
   end Info_Of;

   function Is_Pending (S : Symbol_Id) return Boolean is
     (S /= No_Symbol and then Symbols.Get (S).Kind = Sym_Local
      and then Symbols.Get (S).Ty = 0);

   function Group_Of_Symbol (S : Symbol_Id) return Node_Id is
     (Group_Of (Node_Id (Symbols.Get (S).Decl)));

   --  보류한 바인딩의 group 전체의 타입을 T로 정하고 미뤄 둔 대입을
   --  검사한다. 아직 선언하지 않은 구성원은 선언할 때 이 타입을 얻는다.
   procedure Resolve_Pending (S : Symbol_Id; T : Type_Id) is
      Rep : constant Node_Id := Group_Of_Symbol (S);
      I   : Positive := 1;
   begin
      Group_Types.Include (Rep, T);
      for L of Untyped loop
         if Group_Of (L) = Rep and then Get (L).Sym /= 0
           and then Is_Pending (Symbol_Id (Get (L).Sym))
         then
            Symbols.Table (Get (L).Sym).Ty := Natural (T);
            Set_Type (L, T);
         end if;
      end loop;
      while I <= Pending.Last_Index loop
         if Group_Of_Symbol (Pending (I).Sym) = Rep then
            declare
               P : constant Pending_Assign := Pending (I);
            begin
               Set_Type (Get (P.Assign).A, T);
               if not P.Checked then
                  Check_Against (Get (P.Assign).B, T);
               end if;
               Pending.Delete (I);
            end;
         else
            I := I + 1;
         end if;
      end loop;
   end Resolve_Pending;

   --  스코프가 끝날 때까지 보류된 바인딩: 리터럴만 남았으면 saddr
   procedure Settle_Pending (S : Symbol_Id) is
   begin
      if Is_Pending (S) then
         Resolve_Pending
           (S, (if (for some P of Pending =>
                      Group_Of_Symbol (P.Sym) = Group_Of_Symbol (S)
                      and then not P.Checked)
                then Saddr else Void));
      end if;
   end Settle_Pending;

   --  보류 중인 바인딩으로의 단순 대입
   procedure Check_Pending_Assign (N : Node_Id; S : Symbol_Id) is
      R : constant Node := Get (N);
   begin
      Nodes (Positive (R.A)).Sym := Natural (S);
      if Info_Of (N).Excluded then
         --  공통 타입에서 빠진다. 타입이 정해진 뒤 검사한다.
         Unimplemented (N, "an assignment whose operand names a binding"
                        & " of the group of the binding it stores into,"
                        & " before the type of that group is determined"
                        & " (§5.12)");
      elsif Undetermined (R.B) then
         Pending.Append (Pending_Assign'(S, N, False));
      else
         declare
            T : constant Type_Id := Check_Expr (R.B, No_Type);
         begin
            if Kind (T) = Ty_Never then
               --  발산식은 공통 타입에서 빠진다
               Pending.Append (Pending_Assign'(S, N, True));
            else
               Resolve_Pending (S, T);
               Set_Type (R.A, T);
            end if;
         end;
      end if;
   end Check_Pending_Assign;

   procedure Check_Assign_Rest (N : Node_Id; L : Type_Id);

   --  단순 대입의 앞 피연산자가 보류 중인 바인딩이면 그 심볼
   function Pending_Target (N : Node_Id) return Symbol_Id is
      R    : constant Node := Get (N);
      Name : constant Idents.Ident :=
        (if R.Op = P_Eq then Simple_Name (R.A) else Idents.No_Ident);
      S    : constant Symbol_Id :=
        (if Name = Idents.No_Ident then No_Symbol else Names.Lookup (Name));
   begin
      return (if Is_Pending (S) then S else No_Symbol);
   end Pending_Target;

   function Check_Assign (N : Node_Id) return Type_Id is
      R : constant Node := Get (N);
      S : constant Symbol_Id := Pending_Target (N);
   begin
      if S /= No_Symbol then
         Check_Pending_Assign (N, S);
         return Void;
      end if;
      declare
         L : constant Type_Id := Check_Expr (R.A, No_Type);
      begin
         Check_Place (R.A);
         Check_Assign_Rest (N, L);
      end;
      return Void;
   end Check_Assign;

   procedure Check_Assign_Rest (N : Node_Id; L : Type_Id) is
      R : constant Node := Get (N);
   begin
      if R.Op = P_Eq then
         Check_Against (R.B, L);
      elsif R.Op in P_Plus_Eq | P_Minus_Eq | P_Star_Eq | P_Slash_Eq
                  | P_Percent_Eq | P_Amp_Eq | P_Pipe_Eq | P_Caret_Eq
      then
         if Kind (L) /= Ty_Error and then not Is_Int (L) then
            Error (N, "operands of '" & Spelling (R.Op)
                   & "' shall be integers");
         end if;
         Check_Against (R.B, L);
      else
         Unimplemented (N, "compound assignment '" & Spelling (R.Op)
                        & "' (§6.8.2)");
      end if;
   end Check_Assign_Rest;

   --  정수·참조·uaddr 사이의 캐스트
   function Check_Plain_Cast (N : Node_Id; Source, Target : Type_Id)
                              return Type_Id is
   begin
      if Get (N).Flags (F_Reinterpret) then
         Unimplemented (N, "bitwise reinterpretation (§6.9.8)");
         return Error_Type;
      elsif Kind (Source) = Ty_Error or else Kind (Target) = Ty_Error then
         return Error_Type;
      elsif Is_Int (Source) and then Is_Int (Target) then
         return Target;
      elsif Kind (Source) in Ty_Ref | Ty_Slice and then Target = Uaddr then
         return Target;
      elsif Kind (Source) = Ty_Ref and then Kind (Target) = Ty_Ref then
         if Get (Target).Ref_Tribe /= Unmanaged
           and then Get (Source).Target /= Get (Target).Target
         then
            Error (N, "a cast to a managed reference keeps the referent"
                   & " type");
            return Error_Type;
         end if;
         case Ref_Conversion (Source, Target) is
            when Forbidden =>
               Error (N, Quote (Source) & " cannot become " & Quote (Target));
               return Error_Type;
            when Needs_Airside =>
               Require_Airside (N, "this reference cast");
            when Same | Landside =>
               null;
         end case;
         return Target;
      elsif Source = Uaddr and then Kind (Target) = Ty_Ref then
         if Get (Target).Ref_Tribe /= Unmanaged then
            Error (N, "a cast from 'uaddr' reaches only an unmanaged"
                   & " reference");
            return Error_Type;
         end if;
         return Target;
      end if;
      Unimplemented (N, "cast from " & Quote (Source) & " to "
                     & Quote (Target) & " (§6.9, §8.2.3)");
      return Error_Type;
   end Check_Plain_Cast;

   function Check_Cast (N : Node_Id) return Type_Id is
      R      : constant Node := Get (N);
      Source : constant Type_Id := Check_Expr (R.A, No_Type);
   begin
      if not Is_Variant (Source) or else R.Flags (F_Reinterpret) then
         return Check_Plain_Cast (N, Source, Resolve_Type (R.B));
      end if;
      --  판별자 추출 (§6.9.6)
      if Kind (R.B) = N_Infer_Type then
         return KSA.Disc_Type (Source);
      end if;
      declare
         Target : constant Type_Id := Resolve_Type (R.B);
      begin
         if Is_Int (Target) or else Target = KSA.Disc_Type (Source)
           or else Kind (Target) = Ty_Error
         then
            return Target;
         end if;
         Error (N, "a cast from a variant type reaches an integer type or"
                & " its discriminant type");
         return Error_Type;
      end;
   end Check_Cast;

   function Check_Field (N : Node_Id) return Type_Id is
      R    : constant Node := Get (N);
      Base : Type_Id := Check_Expr (R.A, No_Type);
      Name : constant String := Idents.Image (R.Name);
   begin
      if Kind (Base) = Ty_Error then
         return Base;
      end if;
      --  참조 투명성: 참조를 한 번 거쳐 가리키는 객체에 적용 (§6.3.5)
      if Kind (Base) = Ty_Ref then
         if No_Access.Contains (N) then
            null;  --  참조를 만들 뿐 접근하지 않는다
         elsif Get (Base).Ref_Tribe = Unmanaged then
            Require_Airside (N, "an access through an unmanaged reference");
         elsif Get (Base).Ref_Tribe = Shared and then Get (Base).Mods.Mut then
            Require_Airside (N, "an access through a shared mut reference");
         end if;
         Base := Get (Base).Target;
      end if;
      if Is_Variant (Base) then
         Error (N, "a field expression shall not have a receiver of a variant"
                & " type");
         return Error_Type;
      elsif Kind (Base) = Ty_Anon
        or else (Kind (Base) = Ty_Composite
                 and then Info (Base).Kind = Struct_Type)
      then
         declare
            Count : constant Natural :=
              (if Kind (Base) = Ty_Anon then Natural (Get (Base).Params.Length)
               else Natural (Info (Base).Fields.Length));
            Index : Natural := 0;
         begin
            if R.Name /= Idents.No_Ident then
               if Kind (Base) = Ty_Composite then
                  for I in 1 .. Count loop
                     if Field (Base, I).Name = R.Name
                       and then not Field (Base, I).Pad
                     then
                        Index := I;
                     end if;
                  end loop;
               end if;
            elsif Kind (Base) = Ty_Anon
              or else Info (Base).Form = Unnamed_Form
            then
               declare
                  Pos : constant Integer :=
                    Integer'Value (To_String (R.Text));
               begin
                  if Pos < Count then
                     Index := Pos + 1;
                  end if;
               end;
            end if;
            if Index = 0 then
               Error (N, "'" & Image (Base) & "' has no field '"
                      & (if R.Name /= Idents.No_Ident then Name
                         else To_String (R.Text)) & "'");
               return Error_Type;
            end if;
            if Field_Of (Base, Index).Airside then
               Require_Airside (N, "an access to an airside field");
            end if;
            Nodes (Positive (N)).Sym := Index;
            return Field_Of (Base, Index).Ty;
         end;
      elsif Kind (Base) = Ty_Array and then Name = "ptr" then
         --  투영 (§8.2.5). 공유 참조를 거치면 mut이 붙지 않는다.
         return Ref (Get (Base).Target, Unmanaged);
      elsif Kind (Base) = Ty_Array and then Name = "len" then
         return Uaddr;
      end if;
      Unimplemented (N, "field expressions on " & Quote (Base) & " (§6.3.2)");
      return Error_Type;
   end Check_Field;

   --  구성식이 만드는 타입의 필드와 형태
   procedure Construction_Shape
     (T       : Type_Id;
      Variant : Natural;
      Fields  : out Field_Vectors.Vector;
      Form    : out Form_Kind)
   is
   begin
      Fields.Clear;
      Form := Unit_Form;
      if Kind (T) = Ty_Verdict then
         declare
            F : Field_Info;
         begin
            F.Ty := (if Variant = 1 then Get (T).Pass else Get (T).Fail);
            F.Pub := True;
            Fields.Append (F);
            Form := Unnamed_Form;
         end;
      elsif Kind (T) = Ty_Composite then
         if Variant = 0 then
            Fields := Info (T).Fields;
            Form := Info (T).Form;
         else
            Fields := Types.Variant (T, Variant).Fields;
            Form := Types.Variant (T, Variant).Form;
         end if;
      end if;
   end Construction_Shape;

   --  composite construction (§6.2.3)
   function Check_Construct (N : Node_Id; Expected : Type_Id) return Type_Id
   is
      R       : constant Node := Get (N);
      V       : constant Value_Target := Resolve_Value (N);
      T       : Type_Id := V.Ty;
      Fields  : Field_Vectors.Vector;
      Form    : Form_Kind;
      Filled  : array (1 .. 64) of Boolean := [others => False];
   begin
      case V.Kind is
         when V_None =>
            return Error_Type;
         when V_Symbol =>
            Error (N, "expected a type or a variant");
            return Error_Type;
         when V_Type =>
            if T = No_Type or else Is_Variant (T) then
               Error (N, "a value of a variant type is constructed through"
                      & " one of its variants");
               return Error_Type;
            elsif T /= Void and then Kind (T) /= Ty_Composite then
               Error (N, "'" & Image (T) & "' has no composite construction");
               return Error_Type;
            end if;
         when V_Variant =>
            if T = No_Type then
               if Kind (Expected) = Ty_Verdict then
                  T := Expected;
               else
                  Error (N, "cannot infer the generic arguments of"
                         & " 'verdict'");
                  return Error_Type;
               end if;
            end if;
      end case;

      Construction_Shape (T, V.Variant, Fields, Form);
      if Natural (Fields.Length) > Filled'Length then
         Unimplemented (N, "composite types with more than 64 fields");
         return Error_Type;
      end if;

      if R.Flags (F_Braces) and then Form = Unit_Form then
         Error (N, "a type or variant in unit form takes no curly brackets");
         return Error_Type;
      end if;

      for I in 1 .. R.List.Count loop
         declare
            It : constant Node_Id := Item (R.List, I);
         begin
            if Kind (It) = N_Field_Init then
               if Form /= Named_Form then
                  Error (It, "field initializers need a type in named-field"
                         & " form");
                  return Error_Type;
               end if;
               declare
                  Index : Natural := 0;
               begin
                  for F in 1 .. Natural (Fields.Length) loop
                     if Fields (F).Name = Get (It).Name
                       and then not Fields (F).Pad
                     then
                        Index := F;
                     end if;
                  end loop;
                  if Index = 0 then
                     Error (It, "no field '" & Idents.Image (Get (It).Name)
                            & "'");
                  elsif Filled (Index) then
                     Error (It, "field '" & Idents.Image (Get (It).Name)
                            & "' is initialized twice");
                  else
                     Filled (Index) := True;
                     Nodes (Positive (It)).Sym := Index;
                     Check_Against (Get (It).A, Fields (Index).Ty);
                     Set_Type (It, Fields (Index).Ty);
                  end if;
               end;
            else
               if Form /= Unnamed_Form then
                  Error (It, "an expression list needs a type in"
                         & " unnamed-field form");
                  return Error_Type;
               elsif I > Natural (Fields.Length) then
                  Error (It, "too many fields");
                  return Error_Type;
               end if;
               Filled (I) := True;
               Check_Against (It, Fields (I).Ty);
            end if;
         end;
      end loop;

      --  빠진 필드는 기본값이 있어야 한다
      for F in 1 .. Natural (Fields.Length) loop
         if not Filled (F) and then not Fields (F).Pad
           and then Fields (F).Default = 0
         then
            Error (N, "field "
                   & (if Fields (F).Name /= Idents.No_Ident
                      then "'" & Idents.Image (Fields (F).Name) & "'"
                      else Img (F - 1))
                   & " is not initialized");
         end if;
         if Fields (F).Airside then
            Require_Airside (N, "constructing a type with an airside field");
         end if;
      end loop;

      Nodes (Positive (N)).Sym := V.Variant;
      return T;
   end Check_Construct;

   --  wild construction (§6.2.4). 고른 판별자 값은 Text에 둔다.
   function Check_Wild (N : Node_Id) return Type_Id is
      V : constant Value_Target := Resolve_Value (N);
   begin
      if V.Kind /= V_Type or else V.Ty = No_Type
        or else Kind (V.Ty) /= Ty_Composite or else not Is_Variant (V.Ty)
      then
         if V.Kind /= V_None then
            Error (N, "a wild construction needs a declared variant type");
         end if;
         return Error_Type;
      end if;
      declare
         C     : constant Composite_Info := Info (V.Ty);
         Value : Long_Long_Integer := 0;
         Limit : constant Long_Long_Integer :=
           (if C.Disc = Void then 1
            else 2 ** Natural'Min (62, 8 * Get (C.Disc).Cells
                                       - (if Get (C.Disc).Signed then 1
                                          else 0)));
      begin
         if (for some W of C.Variants => W.Wild) then
            Error (N, "a declared wild variant covers every value, so the"
                   & " wild construction yields none");
            return Error_Type;
         end if;
         --  구현 정의 값: 어느 변형도 갖지 않은 가장 작은 비음수
         while (for some W of C.Variants => W.Value = Value) loop
            Value := Value + 1;
         end loop;
         if Value >= Limit then
            Error (N, "every discriminant value is covered, so the wild"
                   & " construction yields none");
            return Error_Type;
         end if;
         declare
            Chosen : Node := Get (N);
         begin
            Chosen.Text := To_Unbounded_String (Value'Image);
            Nodes.Replace_Element (Positive (N), Chosen);
         end;
         return V.Ty;
      end;
   end Check_Wild;

   procedure Check_Let (N : Node_Id) is
      R    : constant Node := Get (N);
      T    : Type_Id;
      Sym  : Symbol;
   begin
      if R.B = No_Node then
         --  지연 초기화 (§4.3)
         if R.A = No_Node then
            --  타입은 뒤따르는 대입에서 정해진다 (§5.12)
            declare
               Rep : constant Node_Id := Group_Of (N);
               Literals, Synthesized : Natural := 0;
            begin
               for A of Assigns loop
                  if Group_Of (A.Target) = Rep and then not A.Excluded then
                     if Undetermined (Get (A.Assign).B) then
                        Literals := Literals + 1;
                     elsif Kind (Get (A.Assign).B)
                           not in N_Return | N_Break | N_Continue
                     then
                        --  발산식은 공통 타입에서 빠진다
                        Synthesized := Synthesized + 1;
                     end if;
                  end if;
               end loop;
               if Group_Types.Contains (Rep) then
                  T := Group_Types (Rep);  --  group이 이미 타입을 얻었다
               elsif Synthesized > 0 then
                  T := No_Type;
               elsif Literals > 0 then
                  T := Saddr;
               else
                  T := Void;
               end if;
               if T /= No_Type then
                  Group_Types.Include (Rep, T);
               end if;
            end;
         else
            T := Resolve_Type (R.A);
         end if;
      elsif R.A /= No_Node then
         T := Resolve_Type (R.A);
         Check_Against (R.B, T);
      else
         T := Check_Expr (R.B, No_Type);
         if Kind (T) in Ty_Void | Ty_Never then
            Error (N, "a binding cannot hold " & Quote (T));
         end if;
      end if;
      if Names.Clash (R.Name) /= No_Symbol then
         Names.Report_Clash (R.Pos, R.Name);
      end if;
      Sym.Kind := Sym_Local;
      Sym.Name := R.Name;
      Sym.Pos := R.Pos;
      Sym.Ty := Natural (T);
      Sym.Decl := Natural (N);
      Sym.Mutable := R.Flags (F_Mut);
      Sym.Deferred := R.B = No_Node;
      Nodes (Positive (N)).Sym := Natural (Add (Sym));
      Nodes (Positive (N)).Ty := Natural (T);
      Names.Declare_Local (R.Name, Symbol_Id (Get (N).Sym));
   end Check_Let;

   function Find_Loop (N : Node_Id) return Node_Id is
      Label : constant Idents.Ident := Get (N).Name;
   begin
      for I in reverse Loops.First_Index .. Loops.Last_Index loop
         if Label = Idents.No_Ident or else Loops (I).Label = Label then
            return Loops (I).Node;
         end if;
      end loop;
      if Label = Idents.No_Ident then
         Error (N, "'" & Spelling (if Get (N).Kind = N_Break then K_Break
                                   else K_Continue)
                & "' outside a loop");
      else
         Error (N, "unknown label '" & Idents.Image (Label) & "'");
      end if;
      return No_Node;
   end Find_Loop;

   procedure Check_Condition (N : Node_Id) is
      T : constant Type_Id := Check_Expr (N, No_Type);
   begin
      if Kind (T) not in Ty_Error | Ty_Never and then not Is_Contract (T)
      then
         Error (N, "a condition shall be of a contract type, found "
                & Quote (T));
      end if;
   end Check_Condition;

   function Check_Expr (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
      T : Type_Id := Void;
   begin
      case R.Kind is
         when N_Int_Lit =>
            T := Check_Int_Literal (N, Expected);
         when N_Char_Lit =>
            if Length (R.Text) /= 1 then
               Error (N, "a character literal shall denote one cell");
            end if;
            T := Int (False, 1);
         when N_Float_Lit =>
            Unimplemented
              (N, "floating radix point number literals (§3.5.2)");
            T := Error_Type;
         when N_String_Lit =>
            T := Ref (Array_Of (Int (False, 1), Length (R.Text)), Shared);
         when N_Name =>
            declare
               V : constant Value_Target := Resolve_Value (N);
            begin
               case V.Kind is
                  when V_None =>
                     T := Error_Type;
                  when V_Type | V_Variant =>
                     --  타입이나 변형을 가리키는 경로는 구성식이다 (§6.2.3)
                     Nodes (Positive (N)).Kind := N_Construct;
                     T := Check_Construct (N, Expected);
                  when V_Symbol =>
                     case Symbols.Get (V.Sym).Kind is
                        when Sym_Local | Sym_Param =>
                           T := Type_Id (Symbols.Get (V.Sym).Ty);
                           if Is_Pending (V.Sym) then
                              Unimplemented
                                (N, "a use of a binding before an"
                                 & " assignment determines its type"
                                 & " (§5.12)");
                              T := Error_Type;
                           end if;
                        when Sym_Fn =>
                           Unimplemented (N, "subroutine values (§5.10)");
                           T := Error_Type;
                        when Sym_Namespace | Sym_Type =>
                           Error (N, "a namespace is not a value");
                           T := Error_Type;
                     end case;
               end case;
            end;
         when N_Construct =>
            T := Check_Construct (N, Expected);
         when N_Wild_Construct =>
            T := Check_Wild (N);
         when N_Unwritten =>
            --  타입은 검사로만 정해진다 (§6.2.7)
            Require_Airside (N, "unwritten");
            if Expected = No_Type then
               Error (N, "unwritten takes its type from its context alone");
               T := Error_Type;
            else
               T := Expected;
            end if;
         when N_Anon =>
            declare
               Fields : Type_Vectors.Vector;
               Hint   : constant Type_Vectors.Vector :=
                 (if Kind (Expected) = Ty_Anon
                  and then Natural (Get (Expected).Params.Length)
                           = R.List.Count
                  then Get (Expected).Params else Type_Vectors.Empty_Vector);
            begin
               for I in 1 .. R.List.Count loop
                  Fields.Append
                    (Check_Expr (Item (R.List, I),
                                 (if Hint.Is_Empty then No_Type
                                  else Hint (I))));
               end loop;
               T := Anon (Fields);
            end;
         when N_Call =>
            T := Check_Call (N);
         when N_Unary =>
            T := Check_Unary (N, Expected);
         when N_Binary =>
            T := Check_Binary (N, Expected);
         when N_Assign =>
            T := Check_Assign (N);
         when N_Cast =>
            T := Check_Cast (N);
         when N_Field =>
            T := Check_Field (N);

         when N_Block =>
            if R.Name /= Idents.No_Ident then
               Unimplemented (N, "labelled blocks (§7.9)");
            end if;
            Names.Push_Scope;
            for I in 1 .. R.List.Count loop
               declare
                  Item_N : constant Node_Id := Item (R.List, I);
               begin
                  if Kind (Item_N) = N_Let then
                     Check_Let (Item_N);
                  else
                     declare
                        Ignored : constant Type_Id :=
                          Check_Expr (Item_N, No_Type);
                     begin
                        null;
                     end;
                  end if;
               end;
            end loop;
            for I in 1 .. R.List.Count loop
               if Kind (Item (R.List, I)) = N_Let
                 and then Get (Item (R.List, I)).Sym /= 0
               then
                  Settle_Pending (Symbol_Id (Get (Item (R.List, I)).Sym));
               end if;
            end loop;
            Names.Pop_Scope;

         when N_Airside =>
            Airside_Depth := Airside_Depth + 1;
            T := Check_Expr (R.A, No_Type);
            Airside_Depth := Airside_Depth - 1;

         when N_If =>
            Check_Condition (R.A);
            if Kind (R.B) = N_Block then
               T := Check_Expr (R.B, No_Type);
               if R.C /= No_Node then
                  T := Check_Expr (R.C, No_Type);
               end if;
               T := Void;
            else
               declare
                  TB : constant Type_Id := Check_Expr (R.B, Expected);
                  TC : constant Type_Id :=
                    Check_Expr (R.C, (if Kind (TB) = Ty_Never then Expected
                                      else TB));
               begin
                  T := (if Kind (TB) = Ty_Never then TC else TB);
                  if TB /= TC and then Kind (TB) not in Ty_Never | Ty_Error
                    and then Kind (TC) not in Ty_Never | Ty_Error
                  then
                     Error (R.C, "expected " & Quote (TB) & ", found "
                            & Quote (TC));
                  end if;
               end;
            end if;

         when N_While | N_Loop =>
            if R.Kind = N_While then
               Check_Condition (R.A);
            end if;
            Loops.Append (Loop_Entry'(N, R.Name));
            T := Check_Expr ((if R.Kind = N_While then R.B else R.A),
                             No_Type);
            Loops.Delete_Last;
            T := (if R.Kind = N_Loop and then Get (N).Sym = 0 then Never
                  else Void);

         when N_Break | N_Continue =>
            declare
               Target : constant Node_Id := Find_Loop (N);
            begin
               Nodes (Positive (N)).Sym := Natural (Target);
               if R.Kind = N_Break and then Target /= No_Node then
                  --  loop가 끝날 수 있음을 표시 (Sym = 1)
                  Nodes (Positive (Target)).Sym := 1;
               end if;
            end;
            T := Never;

         when N_Return =>
            if Kind (Fn_Ret) = Ty_Never then
               Error (N, "a subroutine that returns '!' shall not return");
            elsif R.A /= No_Node then
               Check_Against (R.A, Fn_Ret);
            elsif Fn_Ret /= Void then
               Error (N, "expected a return value of type " & Quote (Fn_Ret));
            end if;
            T := Never;

         when others =>
            Error (N, "expected expression");
            T := Error_Type;
      end case;
      Set_Type (N, T);
      return T;
   end Check_Expr;

   ---------------------------------------------------------------------
   --  도달성 (§2.4)

   function Diverges (N : Node_Id) return Boolean is
   begin
      if N = No_Node then
         return False;
      end if;
      declare
         R : constant Node := Get (N);
      begin
         case R.Kind is
            when N_Return | N_Break | N_Continue =>
               return True;
            when N_Loop =>
               return R.Sym = 0;
            when N_Block =>
               return (for some I in 1 .. R.List.Count =>
                         Diverges (Item (R.List, I)));
            when N_Airside =>
               return Diverges (R.A);
            when N_Let =>
               return Diverges (R.B);
            when N_If =>
               return Diverges (R.A)
                 or else (R.C /= No_Node and then Diverges (R.B)
                          and then Diverges (R.C));
            when N_While =>
               return Diverges (R.A);
            when N_Call =>
               return Kind (Type_Id (R.Ty)) = Ty_Never
                 or else (for some I in 1 .. R.List.Count =>
                            Diverges (Item (R.List, I)));
            when N_Binary =>
               return Diverges (R.A)
                 or else (R.Op not in K_And | K_Or and then Diverges (R.B));
            when N_Assign =>
               return Diverges (R.A) or else Diverges (R.B);
            when N_Unary | N_Cast | N_Field =>
               return Diverges (R.A);
            when others =>
               return False;
         end case;
      end;
   end Diverges;

   ---------------------------------------------------------------------
   --  본문 분석 (§10.2 4단계)

   procedure Analyse_Fn (N : Node_Id) is
      Failures_Before : constant Natural := Diagnostics.Failures;
      R  : constant Node := Get (N);
      FT : constant Type_Rec := Get (Type_Id (Symbols.Get
                                  (Symbol_Id (R.Sym)).Ty));
   begin
      Fn_Ret := FT.Ret;
      Airside_Depth := (if R.Flags (F_Airside) then 1 else 0);
      Pending.Clear;
      Collect_Untyped (R.B);
      Names.Push_Scope;
      for I in 1 .. R.List.Count loop
         declare
            P   : constant Node_Id := Item (R.List, I);
            PR  : constant Node := Get (P);
            Sym : Symbol;
         begin
            if Names.Clash (PR.Name) /= No_Symbol then
               Names.Report_Clash (PR.Pos, PR.Name);
            end if;
            Sym.Kind := Sym_Param;
            Sym.Name := PR.Name;
            Sym.Pos := PR.Pos;
            Sym.Ty := Natural (FT.Params.Element (I));
            Sym.Decl := Natural (P);
            Sym.Mutable := PR.Flags (F_Mut);
            Sym.Index := I;
            Nodes (Positive (P)).Sym := Natural (Add (Sym));
            Nodes (Positive (P)).Ty := Natural (FT.Params.Element (I));
            Names.Declare_Local (PR.Name, Symbol_Id (Get (P).Sym));
         end;
      end loop;

      declare
         Ignored : constant Type_Id := Check_Expr (R.B, No_Type);
      begin
         null;
      end;
      Flow.Check_Transfers (N);
      if Diagnostics.Failures = Failures_Before then
         Derivation.Check_Body (N);
      end if;
      if Fn_Ret /= Void and then not Diverges (R.B) then
         Diagnostics.Error
           (R.Pos, "the end of the body of '" & Idents.Image (R.Name)
            & "' is reachable, but it returns " & Quote (Fn_Ret));
      end if;
      Names.Pop_Scope;
   end Analyse_Fn;

   procedure Analyse (Unit : Node_Id) is
      U : constant Node := Get (Unit);
   begin
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) = N_Fn then
            Analyse_Fn (Item (U.List, I));
         end if;
      end loop;
   end Analyse;

end Check;
