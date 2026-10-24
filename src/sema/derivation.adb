with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Strings.Fixed;
with Check;
with Diagnostics;
with Idents;
with Source_Map;
with Symbols;
with Tokens;
with Types;

package body Derivation is

   use AST;
   use Tokens;
   use Types;

   ---------------------------------------------------------------------
   --  참조, 객체, 경로

   package Token_Sets is new Ada.Containers.Ordered_Sets (Positive);
   use type Token_Sets.Set;
   subtype Token_Set is Token_Sets.Set;

   package Path_Vectors is new Ada.Containers.Vectors (Positive, Positive);
   use type Path_Vectors.Vector;
   subtype Path is Path_Vectors.Vector;

   package Natural_Sets is new Ada.Containers.Ordered_Sets (Natural);

   --  참조가 무엇에 연결되었는가 (§8.1.1)
   type Chain_Kind is (To_Object, To_Refs, To_Nothing);

   type Token_Info is record
      Exclusive : Boolean := False;
      Mut       : Boolean := False;
      Node      : Node_Id := No_Node;      --  만든 곳
      Kind      : Chain_Kind := To_Nothing;
      Object    : Natural := 0;            --  To_Object
      Own       : Path;                    --  자기 필드 식
      Parents   : Token_Set;               --  To_Refs
      --  매개변수 층: Param * 64 + Layer (§8.1.2 come from)
      Origins   : Natural_Sets.Set;
   end record;
   package Token_Vectors is new Ada.Containers.Vectors (Positive, Token_Info);

   type Object_Info is record
      Sym         : Natural := 0;      --  바인딩이면 그 심볼
      Scope       : Natural := 0;
      Order       : Natural := 0;
      Temp        : Boolean := False;
      Extended_To : Natural := 0;      --  let이 붙잡은 임시 객체 (§2.2.6)
      Ty          : Type_Id := No_Type;
   end record;
   package Object_Vectors is new Ada.Containers.Vectors
     (Positive, Object_Info);
   package Natural_Vectors is new Ada.Containers.Vectors (Positive, Natural);

   Toks       : Token_Vectors.Vector;
   Objs       : Object_Vectors.Vector;
   Scope_Up   : Natural_Vectors.Vector;  --  스코프의 바깥 스코프 (0이면 없음)

   ---------------------------------------------------------------------
   --  명령

   type Op_Kind is
     (Op_Nop,
      Op_Load,          --  Dst := Obj가 담은 참조
      Op_Store,         --  Obj := Src (Strong이면 덮어쓰기)
      Op_Create,        --  Dst := {Tok}, Tok의 부모 ∪= Src
      Op_Union,         --  Dst := ∪ Srcs
      Op_Access,        --  Src(또는 Obj의 암묵 참조 Tok)를 거친 접근
      Op_Deref,         --  Dst := Src를 거쳐 적재한 값이 담은 참조
      Op_Store_Through, --  Src를 거쳐 Src2를 저장
      Op_Lend,          --  호출: Srcs를 빌려주고 Dst := {Tok}
      Op_Return,        --  Src를 반환
      Op_Jump,          --  Target으로
      Op_Branch);       --  다음 또는 Target으로

   type Instr is record
      Op        : Op_Kind := Op_Nop;
      Node      : Node_Id := No_Node;
      Dst       : Natural := 0;
      Src       : Natural := 0;
      Src2      : Natural := 0;
      Srcs      : Natural_Vectors.Vector;
      Obj       : Natural := 0;
      Tok       : Natural := 0;
      Strong    : Boolean := False;
      Exclusive : Boolean := False;
      Access_At : Path;
      Target    : Natural := 0;    --  레이블 번호, 나중에 명령 번호로
      Fn        : Natural := 0;    --  Op_Lend: 피호출 서브루틴의 타입
   end record;
   package Instr_Vectors is new Ada.Containers.Vectors (Positive, Instr);

   Code     : Instr_Vectors.Vector;
   Self_Fn  : Type_Id := No_Type;  --  검사하는 서브루틴의 타입
   Self_Params : List_Id;          --  그 매개변수들
   Labels   : Natural_Vectors.Vector;  --  레이블 → 명령 번호
   Reg_Count : Natural := 0;

   ---------------------------------------------------------------------
   --  도우미

   function Get (N : Node_Id) return Node is (Nodes (Positive (N)));
   function Type_Of (N : Node_Id) return Type_Id is (Type_Id (Get (N).Ty));

   function Img (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   function Where (N : Node_Id) return String is
      Line, Col : Positive;
   begin
      Source_Map.Line_Col (Get (N).Pos, Line, Col);
      return Img (Line) & ":" & Img (Col);
   end Where;

   --  관리 참조를 담는 타입인가
   function Holds_Refs (T : Type_Id) return Boolean is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Ref | Ty_Slice =>
            return R.Ref_Tribe /= Unmanaged;
         when Ty_Array =>
            return Holds_Refs (R.Target);
         when Ty_Anon =>
            return (for some P of R.Params => Holds_Refs (P));
         when Ty_Verdict =>
            return Holds_Refs (R.Pass) or else Holds_Refs (R.Fail);
         when Ty_Composite =>
            declare
               C : constant Composite_Info := Info (T);
            begin
               for F of C.Fields loop
                  if Holds_Refs (F.Ty) then
                     return True;
                  end if;
               end loop;
               for V of C.Variants loop
                  for F of V.Fields loop
                     if Holds_Refs (F.Ty) then
                        return True;
                     end if;
                  end loop;
               end loop;
               return False;
            end;
         when others =>
            return False;
      end case;
   end Holds_Refs;

   function Exclusive_Type (T : Type_Id) return Boolean is
     (Kind (T) in Ty_Ref | Ty_Slice and then Get (T).Ref_Tribe = Exclusive);

   function Mut_Type (T : Type_Id) return Boolean is
     (Kind (T) in Ty_Ref | Ty_Slice
      and then (Get (T).Mods.Mut or else Get (T).Ref_Tribe = Exclusive));

   function New_Reg return Natural is
   begin
      Reg_Count := Reg_Count + 1;
      return Reg_Count;
   end New_Reg;

   function New_Token (Info : Token_Info) return Positive is
   begin
      Toks.Append (Info);
      return Toks.Last_Index;
   end New_Token;

   function New_Label return Natural is
   begin
      Labels.Append (0);
      return Labels.Last_Index;
   end New_Label;

   procedure Place_Label (L : Natural) is
   begin
      Labels.Replace_Element (L, Code.Last_Index + 1);
   end Place_Label;

   procedure Emit (I : Instr) is
   begin
      Code.Append (I);
   end Emit;

   ---------------------------------------------------------------------
   --  낮추기

   --  스코프와 선언 순서 (§2.2.6의 수명 비교용)
   Current_Scope : Natural := 0;
   Next_Order    : Natural := 0;
   Let_Object    : Natural := 0;   --  지금 초기식을 낮추는 let의 객체

   Sym_Objects : Natural_Vectors.Vector;  --  심볼 → 객체 (0이면 없음)

   type Loop_Entry is record
      Node        : Node_Id;
      Head, Exits : Natural;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Entry);
   Loops     : Loop_Vectors.Vector;
   End_Label : Natural := 0;

   procedure Push_Scope is
   begin
      Scope_Up.Append (Current_Scope);
      Current_Scope := Scope_Up.Last_Index;
   end Push_Scope;

   procedure Pop_Scope is
   begin
      Current_Scope := Scope_Up (Current_Scope);
   end Pop_Scope;

   function Object_Of (Sym : Natural) return Natural is
   begin
      while Natural (Sym_Objects.Length) < Sym loop
         Sym_Objects.Append (0);
      end loop;
      if Sym_Objects (Sym) = 0 then
         Next_Order := Next_Order + 1;
         Objs.Append (Object_Info'
                        (Sym => Sym, Scope => Current_Scope,
                         Order => Next_Order,
                         Ty => Type_Id (Symbols.Get (Symbols.Symbol_Id (Sym))
                                          .Ty),
                         others => <>));
         Sym_Objects.Replace_Element (Sym, Objs.Last_Index);
      end if;
      return Sym_Objects (Sym);
   end Object_Of;

   function New_Temp (T : Type_Id) return Natural is
   begin
      Next_Order := Next_Order + 1;
      Objs.Append (Object_Info'(Sym => 0, Scope => Current_Scope,
                                Order => Next_Order, Temp => True,
                                Extended_To => Let_Object, Ty => T));
      return Objs.Last_Index;
   end New_Temp;

   --  객체 식이 가리키는 곳
   type Place_Kind is (Root, Through, Value);
   type Place is record
      Kind : Place_Kind := Value;
      Obj  : Natural := 0;    --  Root
      Reg  : Natural := 0;    --  Through: 참조, Value: 값
      At_P : Path;
   end record;

   function Lower (N : Node_Id) return Natural;
   procedure Lower_Stmt (N : Node_Id);

   function Lower_Place (N : Node_Id) return Place is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Name =>
            if R.Sym /= 0
              and then Symbols.Get (Symbols.Symbol_Id (R.Sym)).Kind
                       in Symbols.Sym_Local | Symbols.Sym_Param
            then
               return (Root, Object_Of (R.Sym), 0, Path_Vectors.Empty_Vector);
            end if;
            --  서브루틴 이름처럼 객체가 아닌 이름
            return (Value, 0, 0, Path_Vectors.Empty_Vector);
         when N_Field =>
            if R.Sym /= 0 then
               if Kind (Type_Of (R.A)) = Ty_Ref then
                  return (Through, 0, Lower (R.A),
                          Path_Vectors.To_Vector (R.Sym, 1));
               end if;
               declare
                  P : Place := Lower_Place (R.A);
               begin
                  P.At_P.Append (R.Sym);
                  return P;
               end;
            end if;
         when N_Unary =>
            if R.Op = P_Star then
               return (Through, 0, Lower (R.A), Path_Vectors.Empty_Vector);
            end if;
         when others =>
            null;
      end case;
      return (Value, 0, Lower (N), Path_Vectors.Empty_Vector);
   end Lower_Place;

   --  객체 식으로의 접근. 참조를 거치지 않으면 그 자리에서 만든 암묵
   --  참조를 거친 접근이다 (§8.1.1).
   procedure Emit_Access (P : Place; Exclusive : Boolean; At_Node : Node_Id)
   is
   begin
      case P.Kind is
         when Root =>
            declare
               Tok : constant Positive :=
                 New_Token ((Exclusive => Exclusive, Mut => Exclusive,
                             Node => At_Node, Kind => To_Object,
                             Object => P.Obj, Own => P.At_P, others => <>));
            begin
               Emit ((Op => Op_Access, Node => At_Node, Obj => P.Obj,
                      Tok => Tok, Exclusive => Exclusive, Access_At => P.At_P,
                      others => <>));
            end;
         when Through =>
            if P.Reg /= 0 then
               Emit ((Op => Op_Access, Node => At_Node, Src => P.Reg,
                      Exclusive => Exclusive, Access_At => P.At_P,
                      others => <>));
            end if;
         when Value =>
            null;
      end case;
   end Emit_Access;

   --  객체 식의 값을 읽는다: 접근하고, 담은 참조를 꺼낸다
   function Load_Place (P : Place; T : Type_Id; At_Node : Node_Id)
                        return Natural
   is
      Dst : Natural := 0;
   begin
      if P.Kind = Value then
         return P.Reg;
      end if;
      Emit_Access (P, Exclusive => False, At_Node => At_Node);
      if Holds_Refs (T) then
         Dst := New_Reg;
         if P.Kind = Root then
            Emit ((Op => Op_Load, Node => At_Node, Dst => Dst, Obj => P.Obj,
                   others => <>));
         elsif P.Reg /= 0 then
            Emit ((Op => Op_Deref, Node => At_Node, Dst => Dst, Src => P.Reg,
                   Tok => New_Token ((Node => At_Node, Kind => To_Nothing,
                                      Exclusive => Exclusive_Type (T),
                                      others => <>)),
                   others => <>));
         else
            return 0;
         end if;
      end if;
      return Dst;
   end Load_Place;

   --  Src의 참조에서 새 참조를 만든다 (재참조, 캐스트, decay)
   function Chain_From (Src : Natural; T : Type_Id; At_Node : Node_Id)
                        return Natural
   is
      Dst : constant Natural := New_Reg;
   begin
      Emit ((Op => Op_Create, Node => At_Node, Dst => Dst, Src => Src,
             Tok => New_Token ((Exclusive => Exclusive_Type (T),
                                Mut => Mut_Type (T), Node => At_Node,
                                Kind => To_Refs, others => <>)),
             others => <>));
      return Dst;
   end Chain_From;

   function Union (Regs : Natural_Vectors.Vector; At_Node : Node_Id)
                   return Natural
   is
      Dst : Natural;
   begin
      if Regs.Is_Empty then
         return 0;
      elsif Natural (Regs.Length) = 1 then
         return Regs.First_Element;
      end if;
      Dst := New_Reg;
      Emit ((Op => Op_Union, Node => At_Node, Dst => Dst, Srcs => Regs,
             others => <>));
      return Dst;
   end Union;

   --  참조 만들기 (§6.4.4)
   function Lower_Creation (N : Node_Id) return Natural is
      R : constant Node := Get (N);
      T : constant Type_Id := Type_Of (N);
   begin
      if R.Op = P_Percent then
         --  비관리 참조는 사슬에 참여하지 않는다
         if Kind (R.A) = N_Unary and then Get (R.A).Op = P_Star then
            declare
               Ignored : constant Natural := Lower (Get (R.A).A);
            begin
               null;
            end;
         elsif Lower_Place (R.A).Kind = Value then
            null;
         end if;
         return 0;
      end if;

      if Kind (R.A) = N_Unary and then Get (R.A).Op = P_Star then
         --  재참조: 참조에서 (§8.2.3)
         return Chain_From (Lower (Get (R.A).A), T, N);
      end if;

      declare
         P   : constant Place := Lower_Place (R.A);
         Dst : constant Natural := New_Reg;
         Tok : Token_Info := (Exclusive => Exclusive_Type (T),
                              Mut => Mut_Type (T), Node => N,
                              Own => P.At_P, others => <>);
      begin
         case P.Kind is
            when Root =>
               Tok.Kind := To_Object;
               Tok.Object := P.Obj;
            when Through =>
               Tok.Kind := To_Refs;
            when Value =>
               --  값 식: 그 값을 담은 임시 객체에 연결된다
               declare
                  Temp : constant Natural := New_Temp (Type_Of (R.A));
               begin
                  if P.Reg /= 0 then
                     Emit ((Op => Op_Store, Node => N, Obj => Temp,
                            Src => P.Reg, Strong => True, others => <>));
                  end if;
                  Tok.Kind := To_Object;
                  Tok.Object := Temp;
                  Tok.Own.Clear;
               end;
         end case;
         Emit ((Op => Op_Create, Node => N, Dst => Dst,
                Src => (if P.Kind = Through then P.Reg else 0),
                Tok => New_Token (Tok), others => <>));
         return Dst;
      end;
   end Lower_Creation;

   procedure Lower_Assign (N : Node_Id) is
      R      : constant Node := Get (N);
      Target : constant Place := Lower_Place (R.A);
      V      : constant Natural := Lower (R.B);
   begin
      --  객체를 정하고, 오른쪽을 평가하고, 저장한다 (§6.8.1)
      Emit_Access (Target, Exclusive => True, At_Node => N);
      if not Holds_Refs (Type_Of (R.A)) then
         return;
      end if;
      case Target.Kind is
         when Root =>
            Emit ((Op => Op_Store, Node => N, Obj => Target.Obj, Src => V,
                   Strong => Target.At_P.Is_Empty and then R.Op = P_Eq,
                   others => <>));
         when Through =>
            if Target.Reg /= 0 and then V /= 0 then
               Emit ((Op => Op_Store_Through, Node => N, Src => Target.Reg,
                      Src2 => V, others => <>));
            end if;
         when Value =>
            null;
      end case;
   end Lower_Assign;

   function Lower_Value (N : Node_Id) return Natural is
      R : constant Node := Get (N);
      T : constant Type_Id := Type_Of (N);
   begin
      case R.Kind is
         when N_Int_Lit | N_Char_Lit | N_Wild_Construct =>
            return 0;

         when N_String_Lit =>
            --  문자열 리터럴: 상주 객체를 가리키는 공유 참조
            declare
               Dst : constant Natural := New_Reg;
            begin
               Emit ((Op => Op_Create, Node => N, Dst => Dst,
                      Tok => New_Token ((Node => N, Kind => To_Nothing,
                                         others => <>)),
                      others => <>));
               return Dst;
            end;

         when N_Name | N_Field =>
            if R.Kind = N_Field and then R.Sym = 0 then
               --  투영 (.ptr, .len): 접근하지 않는다
               if not (Kind (R.A) in N_Name | N_Field
                       or else (Kind (R.A) = N_Unary
                                and then Get (R.A).Op = P_Star))
               then
                  declare
                     Ignored : constant Natural := Lower (R.A);
                  begin
                     null;
                  end;
               elsif Kind (Type_Of (R.A)) = Ty_Ref then
                  declare
                     Ignored : constant Natural := Lower (R.A);
                  begin
                     null;
                  end;
               end if;
               return 0;
            end if;
            return Load_Place (Lower_Place (N), T, N);

         when N_Unary =>
            case R.Op is
               when P_Star =>
                  return Load_Place (Lower_Place (N), T, N);
               when P_Amp | P_Dollar | P_Percent =>
                  return Lower_Creation (N);
               when others =>
                  --  부호, 비트 반전, 극성 반전: 반전은 페이로드를 옮긴다
                  return Lower (R.A);
            end case;

         when N_Binary =>
            if R.Op in K_And | K_Or then
               declare
                  Skip    : constant Natural := New_Label;
                  Ignored : Natural := Lower (R.A);
               begin
                  Emit ((Op => Op_Branch, Node => N, Target => Skip,
                         others => <>));
                  Ignored := Lower (R.B);
                  Place_Label (Skip);
               end;
            else
               declare
                  Ignored : Natural := Lower (R.A);
               begin
                  Ignored := Lower (R.B);
               end;
            end if;
            return 0;

         when N_Assign =>
            Lower_Assign (N);
            return 0;

         when N_Cast =>
            declare
               V : constant Natural := Lower (R.A);
            begin
               if Kind (T) = Ty_Ref and then Get (T).Ref_Tribe /= Unmanaged
                 and then V /= 0
               then
                  return Chain_From (V, T, N);
               end if;
               return 0;
            end;

         when N_Call =>
            declare
               Args : Natural_Vectors.Vector;
               Dst  : constant Natural :=
                 (if Holds_Refs (T) then New_Reg else 0);
            begin
               --  인자는 자리 순서대로 (참조가 없으면 0)
               for I in 1 .. R.List.Count loop
                  Args.Append (Lower (Item (R.List, I)));
               end loop;
               Emit ((Op => Op_Lend, Node => N, Dst => Dst, Srcs => Args,
                      Fn => Natural (Type_Of (R.A)),
                      Tok => New_Token ((Exclusive => Exclusive_Type (T),
                                         Mut => Mut_Type (T), Node => N,
                                         Kind => To_Refs, others => <>)),
                      others => <>));
               return Dst;
            end;

         when N_Construct | N_Anon =>
            declare
               Regs : Natural_Vectors.Vector;
            begin
               for I in 1 .. R.List.Count loop
                  declare
                     It : constant Node_Id := Item (R.List, I);
                     V  : constant Natural :=
                       Lower (if Kind (It) = N_Field_Init then Get (It).A
                              else It);
                  begin
                     if V /= 0 then
                        Regs.Append (V);
                     end if;
                  end;
               end loop;
               return (if Holds_Refs (T) then Union (Regs, N) else 0);
            end;

         when N_If =>
            if Kind (R.B) = N_Block then
               Lower_Stmt (N);
               return 0;
            end if;
            declare
               Else_L : constant Natural := New_Label;
               Done_L : constant Natural := New_Label;
               Dst    : constant Natural :=
                 (if Holds_Refs (T) then New_Reg else 0);
               C      : constant Natural := Lower (R.A);

               procedure Arm (E : Node_Id) is
                  V : constant Natural := Lower (E);
               begin
                  if Dst /= 0 and then V /= 0 then
                     Emit ((Op => Op_Union, Node => E, Dst => Dst,
                            Srcs => Natural_Vectors.To_Vector (V, 1),
                            others => <>));
                  end if;
               end Arm;
            begin
               pragma Unreferenced (C);
               Emit ((Op => Op_Branch, Node => N, Target => Else_L,
                      others => <>));
               Arm (R.B);
               Emit ((Op => Op_Jump, Node => N, Target => Done_L,
                      others => <>));
               Place_Label (Else_L);
               Arm (R.C);
               Place_Label (Done_L);
               return Dst;
            end;

         when others =>
            Lower_Stmt (N);
            return 0;
      end case;
   end Lower_Value;

   function Lower (N : Node_Id) return Natural is
      V : constant Natural := Lower_Value (N);
      D : constant Natural := Check.Decayed (N);
   begin
      if D /= 0 and then V /= 0 and then Kind (Type_Id (D)) = Ty_Ref
        and then Get (Type_Id (D)).Ref_Tribe /= Unmanaged
      then
         --  decay는 새 참조를 만든다 (§8.2.3)
         return Chain_From (V, Type_Id (D), N);
      end if;
      return V;
   end Lower;

   procedure Lower_Stmt (N : Node_Id) is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Block =>
            Push_Scope;
            for I in 1 .. R.List.Count loop
               Lower_Stmt (Item (R.List, I));
            end loop;
            Pop_Scope;

         when N_Let =>
            declare
               Obj   : constant Natural := Object_Of (R.Sym);
               Saved : constant Natural := Let_Object;
               V     : Natural;
            begin
               Let_Object := Obj;
               V := Lower (R.B);
               Let_Object := Saved;
               if Holds_Refs (Type_Of (N)) then
                  Emit ((Op => Op_Store, Node => N, Obj => Obj, Src => V,
                         Strong => True, others => <>));
               end if;
            end;

         when N_Airside =>
            Lower_Stmt (R.A);

         when N_If =>
            declare
               Else_L  : constant Natural := New_Label;
               Done_L  : constant Natural := New_Label;
               Ignored : constant Natural := Lower (R.A);
            begin
               Emit ((Op => Op_Branch, Node => N, Target => Else_L,
                      others => <>));
               Lower_Stmt (R.B);
               Emit ((Op => Op_Jump, Node => N, Target => Done_L,
                      others => <>));
               Place_Label (Else_L);
               if R.C /= No_Node then
                  Lower_Stmt (R.C);
               end if;
               Place_Label (Done_L);
            end;

         when N_While | N_Loop =>
            declare
               Head  : constant Natural := New_Label;
               Exits : constant Natural := New_Label;
            begin
               Place_Label (Head);
               Loops.Append (Loop_Entry'(N, Head, Exits));
               if R.Kind = N_While then
                  declare
                     Ignored : constant Natural := Lower (R.A);
                  begin
                     Emit ((Op => Op_Branch, Node => N, Target => Exits,
                            others => <>));
                  end;
                  Lower_Stmt (R.B);
               else
                  Lower_Stmt (R.A);
               end if;
               Emit ((Op => Op_Jump, Node => N, Target => Head,
                      others => <>));
               Loops.Delete_Last;
               Place_Label (Exits);
            end;

         when N_Break | N_Continue =>
            for L of reverse Loops loop
               if L.Node = Node_Id (R.Sym) then
                  Emit ((Op => Op_Jump, Node => N,
                         Target => (if R.Kind = N_Break then L.Exits
                                    else L.Head),
                         others => <>));
                  exit;
               end if;
            end loop;

         when N_Return =>
            declare
               V : constant Natural :=
                 (if R.A = No_Node then 0 else Lower (R.A));
            begin
               if V /= 0 then
                  Emit ((Op => Op_Return, Node => N, Src => V,
                         others => <>));
               end if;
               Emit ((Op => Op_Jump, Node => N, Target => End_Label,
                      others => <>));
            end;

         when others =>
            declare
               Ignored : constant Natural := Lower_Value (N);
            begin
               null;
            end;
      end case;
   end Lower_Stmt;

   ---------------------------------------------------------------------
   --  참조 사이의 관계

   type Anchor is record
      Root    : Integer;  --  > 0: 객체, < 0: 아무것에도 연결되지 않은 참조
      Descent : Path;
   end record;
   package Anchor_Vectors is new Ada.Containers.Vectors (Positive, Anchor);

   --  참조가 결국 이르는 객체(또는 무연결 참조)와 그 descent
   procedure Collect_Anchors
     (T       : Positive;
      Suffix  : Path;
      Visited : in out Token_Set;
      Result  : in out Anchor_Vectors.Vector)
   is
      I       : constant Token_Info := Toks (T);
      Descent : constant Path := I.Own & Suffix;
   begin
      case I.Kind is
         when To_Object =>
            Result.Append (Anchor'(Integer (I.Object), Descent));
         when To_Nothing =>
            Result.Append (Anchor'(-Integer (T), Descent));
         when To_Refs =>
            if I.Parents.Is_Empty then
               Result.Append (Anchor'(-Integer (T), Descent));
            end if;
            for P of I.Parents loop
               if not Visited.Contains (P) then
                  Visited.Insert (P);
                  Collect_Anchors (P, Descent, Visited, Result);
               end if;
            end loop;
      end case;
   end Collect_Anchors;

   function Anchors (T : Positive) return Anchor_Vectors.Vector is
      Result  : Anchor_Vectors.Vector;
      Visited : Token_Set := Token_Sets.To_Set (T);
   begin
      Collect_Anchors (T, Path_Vectors.Empty_Vector, Visited, Result);
      return Result;
   end Anchors;

   function Ancestors (T : Positive) return Token_Set is
      Result : Token_Set;
      Work   : Token_Set := Toks (T).Parents;
   begin
      while not Work.Is_Empty loop
         declare
            P : constant Positive := Work.First_Element;
         begin
            Work.Delete_First;
            if not Result.Contains (P) then
               Result.Insert (P);
               Work.Union (Toks (P).Parents);
            end if;
         end;
      end loop;
      return Result;
   end Ancestors;

   function Origins (T : Positive) return Natural_Sets.Set is
      Result : Natural_Sets.Set := Toks (T).Origins;
   begin
      for A of Ancestors (T) loop
         Result.Union (Toks (A).Origins);
      end loop;
      return Result;
   end Origins;

   function Prefix (A, B : Path) return Boolean is
     (Natural (A.Length) <= Natural (B.Length)
      and then (for all I in 1 .. Natural (A.Length) => A (I) = B (I)));

   function Overlap (A, B : Path) return Boolean is
     (Prefix (A, B) or else Prefix (A => B, B => A));

   --  §8.1.1 meet
   function Meet (A, B : Positive) return Boolean is
      AA : constant Anchor_Vectors.Vector := Anchors (A);
      BA : constant Anchor_Vectors.Vector := Anchors (B);
   begin
      for X of AA loop
         for Y of BA loop
            if X.Root = Y.Root and then Overlap (X.Descent, Y.Descent) then
               return True;
            end if;
         end loop;
      end loop;
      return False;
   end Meet;

   --  자손 D의 descent 가운데 E 다음 부분이 접근한 필드와 겹치는가
   function Overlaps_Access (E, D : Positive; Access_At : Path)
                             return Boolean
   is
      Matched : Boolean := False;
   begin
      for X of Anchors (E) loop
         for Y of Anchors (D) loop
            if X.Root = Y.Root and then Prefix (X.Descent, Y.Descent) then
               Matched := True;
               declare
                  Rel : Path;
               begin
                  for K in Natural (X.Descent.Length) + 1
                           .. Natural (Y.Descent.Length)
                  loop
                     Rel.Append (Y.Descent (K));
                  end loop;
                  if Overlap (Rel, Access_At) then
                     return True;
                  end if;
               end;
            end if;
         end loop;
      end loop;
      return not Matched;
   end Overlaps_Access;

   function Related (A, B : Positive) return Boolean is
     (Ancestors (A).Contains (B) or else Ancestors (B).Contains (A));

   --  참조가 가리키는 지역 객체들
   function Referents (T : Positive) return Natural_Sets.Set is
      Result : Natural_Sets.Set;
   begin
      for A of Anchors (T) loop
         if A.Root > 0 then
            Result.Include (Natural (A.Root));
         end if;
      end loop;
      return Result;
   end Referents;

   --  §2.2.6: A가 B보다 오래 사는가
   function Encloses (Outer, Inner : Natural) return Boolean is
      S : Natural := Inner;
   begin
      while S /= 0 loop
         S := Scope_Up (S);
         if S = Outer then
            return True;
         end if;
      end loop;
      return False;
   end Encloses;

   function Outlives (A, B : Positive) return Boolean is
      OA : constant Object_Info := Objs (A);
      OB : constant Object_Info := Objs (B);
   begin
      if A = B or else OA.Temp then
         return False;
      elsif OB.Temp then
         --  임시 객체는 문장이 끝날 때, let이 붙잡았으면 그 바인딩과 함께
         return OB.Extended_To = 0 or else Outlives (A, OB.Extended_To);
      end if;
      return Encloses (OA.Scope, OB.Scope)
        or else (OA.Scope = OB.Scope and then OA.Order < OB.Order);
   end Outlives;

   --  "layer K of 'name'"
   function Layer_Name (Org : Natural) return String is
     ("layer" & Natural'Image (Org mod 64) & " of '"
      & (if Org / 64 < Self_Params.Count
         then Idents.Image (Get (Item (Self_Params, Org / 64 + 1)).Name)
         else "?")
      & "'");

   function Object_Name (O : Positive) return String is
     (if Objs (O).Temp then "a temporary object"
      else "'" & Idents.Image (Symbols.Get (Symbols.Symbol_Id
                                             (Objs (O).Sym)).Name) & "'");

   ---------------------------------------------------------------------
   --  분석

   type Set_Array is array (Positive range <>) of Token_Set;
   type State (Objects, Regs : Natural) is record
      Holds : Set_Array (1 .. Objects);
      Vals  : Set_Array (1 .. Regs);
   end record;

   function Join (A, B : State) return State is
      R : State := A;
   begin
      for I in R.Holds'Range loop
         R.Holds (I).Union (B.Holds (I));
      end loop;
      for I in R.Vals'Range loop
         R.Vals (I).Union (B.Vals (I));
      end loop;
      return R;
   end Join;

   function Val (S : State; R : Natural) return Token_Set is
     (if R = 0 then Token_Sets.Empty_Set else S.Vals (R));

   --  매개변수 P의 층 K에 있는 참조 (§8.1.2 layer)
   Max_Depth  : constant := 8;
   Max_Params : constant := 32;
   type Layer_Table is array (0 .. Max_Params - 1, 0 .. Max_Depth)
     of Token_Set;

   Static_Sink : constant := 1;  --  static으로 가는 참조를 담는 객체

   function Layer (P, K : Natural) return Route_End is
     ((Kind => End_Layer, Param => P, Layer => K, Deeper => False));
   Return_End : constant Route_End := (Kind => End_Return, others => <>);
   Static_End : constant Route_End := (Kind => End_Static, others => <>);

   procedure Param_Layers
     (S : State; C : Instr; L : out Layer_Table; Count : out Natural)
   is
      FT    : constant Type_Rec := Get (Type_Id (C.Fn));
      Fixed : constant Natural := Natural (FT.Params.Length);
   begin
      L := [others => [others => Token_Sets.Empty_Set]];
      --  가변 인자는 고정 매개변수 뒤의 매개변수 하나로 친다
      Count := Natural'Min (Max_Params,
                            Fixed + (if FT.Variadic then 1 else 0));
      for I in 1 .. Natural (C.Srcs.Length) loop
         declare
            P : constant Natural := Natural'Min (I - 1, Fixed);
         begin
            if P < Count then
               L (P, 0).Union (Val (S, C.Srcs (I)));
            end if;
         end;
      end loop;
      for P in 0 .. Count - 1 loop
         declare
            Seen : Token_Set := L (P, 0);
         begin
            for K in 0 .. Max_Depth - 1 loop
               for T of L (P, K) loop
                  for O of Referents (T) loop
                     L (P, K + 1).Union (S.Holds (O));
                  end loop;
               end loop;
               L (P, K + 1).Difference (Seen);
               Seen.Union (L (P, K + 1));
            end loop;
         end;
      end loop;
   end Param_Layers;

   --  호출이 매개변수 P의 층 K에 있는 저장 가능한 참조의 대상에 넣는
   --  참조: 더 깊은 층과 그 층으로 routes된 참조 (§8.1.2)
   function Placed_At
     (L : Layer_Table; Count : Natural; Fn : Type_Id; P, K : Natural)
      return Token_Set
   is
      Result : Token_Set;
   begin
      for J in K + 1 .. Max_Depth loop
         Result.Union (L (P, J));
      end loop;
      for Q in 0 .. Count - 1 loop
         for J in 0 .. Max_Depth loop
            if Routes_To (Fn, Layer (Q, J), Layer (P, K + 1)) then
               Result.Union (L (Q, J));
            end if;
         end loop;
      end loop;
      return Result;
   end Placed_At;

   --  호출이 빌려주는 모든 참조
   procedure Layers (S : State; C : Instr; All_Layers : out Token_Set) is
      L     : Layer_Table;
      Count : Natural;
   begin
      Param_Layers (S, C, L, Count);
      All_Layers.Clear;
      for P in 0 .. Count - 1 loop
         for K in 0 .. Max_Depth loop
            All_Layers.Union (L (P, K));
         end loop;
      end loop;
   end Layers;

   procedure Transfer (I : Instr; S : in out State) is
   begin
      case I.Op is
         when Op_Load =>
            S.Vals (I.Dst) := S.Holds (I.Obj);
         when Op_Store =>
            if I.Strong then
               S.Holds (I.Obj) := Val (S, I.Src);
            else
               S.Holds (I.Obj).Union (Val (S, I.Src));
            end if;
         when Op_Create =>
            if I.Src /= 0 then
               declare
                  T : Token_Info := Toks (I.Tok);
               begin
                  T.Parents.Union (S.Vals (I.Src));
                  Toks.Replace_Element (I.Tok, T);
               end;
            end if;
            S.Vals (I.Dst) := Token_Sets.To_Set (I.Tok);
         when Op_Union =>
            S.Vals (I.Dst) := Token_Sets.Empty_Set;
            for R of I.Srcs loop
               S.Vals (I.Dst).Union (Val (S, R));
            end loop;
         when Op_Deref =>
            --  가리키는 지역 객체가 담은 참조와, 매개변수의 다음 층에서
            --  온 참조
            declare
               Result : Token_Set;
               T      : Token_Info := Toks (I.Tok);
               Known  : Boolean := True;
            begin
               for R of S.Vals (I.Src) loop
                  if Referents (R).Is_Empty then
                     Known := False;
                  end if;
                  for O of Referents (R) loop
                     Result.Union (S.Holds (O));
                  end loop;
                  for Org of Origins (R) loop
                     if Org mod 64 < 63 then
                        T.Origins.Include (Org + 1);
                     end if;
                  end loop;
               end loop;
               Toks.Replace_Element (I.Tok, T);
               if not Known then
                  Result.Include (I.Tok);
               end if;
               S.Vals (I.Dst) := Result;
            end;
         when Op_Store_Through =>
            for R of S.Vals (I.Src) loop
               for O of Referents (R) loop
                  S.Holds (O).Union (S.Vals (I.Src2));
               end loop;
            end loop;
         when Op_Lend =>
            declare
               L     : Layer_Table;
               Count : Natural;
               FT    : constant Type_Id := Type_Id (I.Fn);
               T     : Token_Info := Toks (I.Tok);
            begin
               Param_Layers (S, I, L, Count);
               for P in 0 .. Count - 1 loop
                  for K in 0 .. Max_Depth loop
                     --  결과는 return으로 가는 층의 참조에 연결된다
                     if Routes_To (FT, Layer (P, K), Return_End) then
                        T.Parents.Union (L (P, K));
                     end if;
                     --  static으로 가는 참조는 이후 내내 pending이다
                     if Routes_To (FT, Layer (P, K), Static_End) then
                        S.Holds (Static_Sink).Union (L (P, K));
                     end if;
                     if K < Max_Depth then
                        for R of L (P, K) loop
                           if Toks (R).Exclusive or else Toks (R).Mut then
                              for O of Referents (R) loop
                                 if Holds_Refs (Objs (O).Ty) then
                                    S.Holds (O).Union
                                      (Placed_At (L, Count, FT, P, K));
                                 end if;
                              end loop;
                           end if;
                        end loop;
                     end if;
                  end loop;
               end loop;
               Toks.Replace_Element (I.Tok, T);
               if I.Dst /= 0 then
                  S.Vals (I.Dst) := Token_Sets.To_Set (I.Tok);
               end if;
            end;
         when others =>
            null;
      end case;
   end Transfer;

   procedure Check_Body (Fn : Node_Id) is
      R : constant Node := Get (Fn);
   begin
      Toks.Clear;
      Objs.Clear;
      Code.Clear;
      Labels.Clear;
      Scope_Up.Clear;
      Sym_Objects.Clear;
      Loops.Clear;
      Reg_Count := 0;
      Next_Order := 0;
      Let_Object := 0;
      Current_Scope := 0;

      Self_Fn := Type_Id (Symbols.Get (Symbols.Symbol_Id (R.Sym)).Ty);
      Self_Params := R.List;
      Objs.Append (Object_Info'(Sym => 0, Scope => 0, Order => 0,
                                Temp => False, Extended_To => 0,
                                Ty => No_Type));
      pragma Assert (Objs.Last_Index = Static_Sink);

      --  매개변수: 바깥 스코프, 값이 담은 참조는 층 0에서 온다
      Push_Scope;
      End_Label := New_Label;
      for I in 1 .. R.List.Count loop
         declare
            P   : constant Node_Id := Item (R.List, I);
            Obj : constant Natural := Object_Of (Get (P).Sym);
         begin
            if Holds_Refs (Type_Of (P)) then
               declare
                  Dst : constant Natural := New_Reg;
                  Tok : Token_Info :=
                    (Exclusive => Exclusive_Type (Type_Of (P)),
                     Mut => Mut_Type (Type_Of (P)), Node => P,
                     Kind => To_Nothing, others => <>);
               begin
                  Tok.Origins.Include ((I - 1) * 64);
                  Emit ((Op => Op_Create, Node => P, Dst => Dst,
                         Tok => New_Token (Tok), others => <>));
                  Emit ((Op => Op_Store, Node => P, Obj => Obj, Src => Dst,
                         Strong => True, others => <>));
               end;
            end if;
         end;
      end loop;
      Lower_Stmt (R.B);
      Place_Label (End_Label);
      Emit ((Op => Op_Nop, others => <>));

      declare
         N_Instr : constant Natural := Natural (Code.Length);
         N_Obj   : constant Natural := Natural (Objs.Length);
         N_Reg   : constant Natural := Reg_Count;

         Empty : constant State (N_Obj, N_Reg) :=
           (Objects => N_Obj, Regs => N_Reg, others => <>);

         type State_Array is array (1 .. N_Instr) of State (N_Obj, N_Reg);
         type State_Access is access State_Array;
         In_St  : constant State_Access := new State_Array'(others => Empty);
         Out_St : constant State_Access := new State_Array'(others => Empty);
         Reached : array (1 .. N_Instr) of Boolean := [others => False];

         function Target_Of (I : Positive) return Natural is
           (Labels (Code (I).Target));

         function Falls (I : Positive) return Boolean is
           (Code (I).Op /= Op_Jump and then I < N_Instr);

         type Bool_Array is array (Natural range <>) of Boolean;
         type Live_Set (Objects, Regs : Natural) is record
            Obj : Bool_Array (1 .. Objects) := [others => False];
            Reg : Bool_Array (1 .. Regs) := [others => False];
         end record;
         type Live_Array is array (1 .. N_Instr) of Live_Set (N_Obj, N_Reg);
         type Live_Access is access Live_Array;
         Live_In  : constant Live_Access :=
           new Live_Array'(others => (Objects => N_Obj, Regs => N_Reg,
                                      others => <>));
         Live_Out : constant Live_Access :=
           new Live_Array'(others => (Objects => N_Obj, Regs => N_Reg,
                                      others => <>));

         Reported : Natural_Sets.Set;  --  진단한 노드
         Pairs    : Natural_Sets.Set;  --  진단한 참조 짝

         procedure Report (At_Node : Node_Id; Message : String) is
         begin
            if not Reported.Contains (Natural (At_Node)) then
               Reported.Insert (Natural (At_Node));
               Diagnostics.Error (Get (At_Node).Pos, Message);
            end if;
         end Report;

         --  명령이 읽는 객체와 값
         procedure Uses
           (I : Positive; Objects : out Natural_Sets.Set;
            Regs : out Natural_Sets.Set)
         is
            C : constant Instr := Code (I);
            S : State renames In_St (I);
         begin
            Objects.Clear;
            Regs.Clear;
            if C.Src /= 0 and then C.Op /= Op_Load then
               Regs.Include (C.Src);
            end if;
            if C.Src2 /= 0 then
               Regs.Include (C.Src2);
            end if;
            for R of C.Srcs loop
               if R /= 0 then
                  Regs.Include (R);
               end if;
            end loop;
            case C.Op is
               when Op_Load =>
                  Objects.Include (C.Obj);
               when Op_Deref =>
                  for T of S.Vals (C.Src) loop
                     Objects.Union (Referents (T));
                  end loop;
               when Op_Lend =>
                  declare
                     All_L : Token_Set;
                  begin
                     Layers (S, C, All_L);
                     for T of All_L loop
                        Objects.Union (Referents (T));
                     end loop;
                  end;
               when others =>
                  null;
            end case;
         end Uses;

      begin
         --  앞으로: 각 지점의 참조
         declare
            Work    : Natural_Sets.Set := Natural_Sets.To_Set (1);
            Rounds  : Natural := 0;
         begin
            Reached (1) := True;
            while not Work.Is_Empty and then Rounds < 100_000 loop
               Rounds := Rounds + 1;
               declare
                  I : constant Positive := Work.First_Element;
                  S : State := In_St (I);
               begin
                  Work.Delete_First;
                  Transfer (Code (I), S);
                  Out_St (I) := S;
                  declare
                     Succs : Natural_Vectors.Vector;
                  begin
                     if Falls (I) then
                        Succs.Append (I + 1);
                     end if;
                     if Code (I).Op in Op_Jump | Op_Branch then
                        Succs.Append (Target_Of (I));
                     end if;
                     for Succ of Succs loop
                        if Succ in 1 .. N_Instr then
                           declare
                              Joined : constant State :=
                                Join (In_St (Succ), S);
                           begin
                              if not Reached (Succ)
                                or else Joined /= In_St (Succ)
                              then
                                 Reached (Succ) := True;
                                 In_St (Succ) := Joined;
                                 Work.Include (Succ);
                              end if;
                           end;
                        end if;
                     end loop;
                  end;
               end;
            end loop;
         end;

         --  뒤로: 이후에 쓰이는 객체와 값
         declare
            Changed : Boolean := True;
         begin
            while Changed loop
               Changed := False;
               for I in reverse 1 .. N_Instr loop
                  declare
                     C        : constant Instr := Code (I);
                     Out_Live : Live_Set (N_Obj, N_Reg);
                     In_Live  : Live_Set (N_Obj, N_Reg);
                     UO, UR   : Natural_Sets.Set;
                  begin
                     if Falls (I) then
                        Out_Live := Live_In (I + 1);
                     end if;
                     if C.Op in Op_Jump | Op_Branch
                       and then Target_Of (I) in 1 .. N_Instr
                     then
                        for K in Out_Live.Obj'Range loop
                           Out_Live.Obj (K) := Out_Live.Obj (K)
                             or else Live_In (Target_Of (I)).Obj (K);
                        end loop;
                        for K in Out_Live.Reg'Range loop
                           Out_Live.Reg (K) := Out_Live.Reg (K)
                             or else Live_In (Target_Of (I)).Reg (K);
                        end loop;
                     end if;
                     In_Live := Out_Live;
                     if C.Dst /= 0 then
                        In_Live.Reg (C.Dst) := False;
                     end if;
                     if C.Op = Op_Store and then C.Strong then
                        In_Live.Obj (C.Obj) := False;
                     end if;
                     Uses (I, UO, UR);
                     for O of UO loop
                        In_Live.Obj (O) := True;
                     end loop;
                     --  static에 들어간 참조는 이후 내내 pending이다
                     In_Live.Obj (Static_Sink) := True;
                     Out_Live.Obj (Static_Sink) := True;
                     for Rg of UR loop
                        In_Live.Reg (Rg) := True;
                     end loop;
                     if In_Live /= Live_In (I) or else Out_Live /= Live_Out (I)
                     then
                        Live_In (I) := In_Live;
                        Live_Out (I) := Out_Live;
                        Changed := True;
                     end if;
                  end;
               end loop;
            end loop;
         end;

         --  검사
         for I in 1 .. N_Instr loop
            if Reached (I) then
               declare
                  C        : constant Instr := Code (I);
                  S_In     : State renames In_St (I);
                  S_Out    : State renames Out_St (I);
                  Pending  : Token_Set;
                  UO, UR   : Natural_Sets.Set;
               begin
                  --  pending: 이 명령이 쓰는 것과 이후에 쓰일 것
                  Uses (I, UO, UR);
                  for O of UO loop
                     Pending.Union (S_In.Holds (O));
                  end loop;
                  for Rg of UR loop
                     Pending.Union (Val (S_In, Rg));
                  end loop;
                  for O in 1 .. N_Obj loop
                     if Live_Out (I).Obj (O) then
                        Pending.Union (S_Out.Holds (O));
                     end if;
                  end loop;
                  for Rg in 1 .. N_Reg loop
                     if Live_Out (I).Reg (Rg) then
                        Pending.Union (S_Out.Vals (Rg));
                     end if;
                  end loop;
                  if C.Op = Op_Access and then C.Tok /= 0 then
                     Pending.Include (C.Tok);
                  end if;

                  --  같은 지점이 앞서 만든 배타 참조가 아직 pending인데 또
                  --  만든다
                  if C.Op = Op_Create and then Toks (C.Tok).Exclusive then
                     for O in 1 .. N_Obj loop
                        if Live_Out (I).Obj (O)
                          and then S_In.Holds (O).Contains (C.Tok)
                        then
                           Report (C.Node, "an exclusive reference created"
                                   & " here on an earlier pass is still"
                                   & " pending");
                        end if;
                     end loop;
                  end if;

                  --  배타 참조가 pending이면 그것과 만나는 다른 pending
                  --  참조는 조상이나 자손이어야 한다
                  for E of Pending loop
                     if Toks (E).Exclusive then
                        for X of Pending loop
                           if X /= E and then Meet (E, X)
                             and then not Related (E, X)
                             and then not Pairs.Contains
                               (Natural'Min (E, X) * 65_536
                                + Natural'Max (E, X))
                           then
                              Pairs.Insert (Natural'Min (E, X) * 65_536
                                            + Natural'Max (E, X));
                              if C.Op = Op_Access
                                and then (E = C.Tok or else X = C.Tok)
                              then
                                 --  이 지점의 암묵 접근과의 충돌
                                 Diagnostics.Error
                                   (Get (C.Node).Pos,
                                    "this access conflicts with the "
                                    & (if E = C.Tok then "reference"
                                       else "exclusive reference")
                                    & " created at "
                                    & Where (Toks (if E = C.Tok then X
                                                   else E).Node)
                                    & ", which is still pending");
                              else
                                 Diagnostics.Error
                                   (Get (C.Node).Pos,
                                    "the exclusive reference created at "
                                    & Where (Toks (E).Node)
                                    & " and the reference created at "
                                    & Where (Toks (X).Node)
                                    & " are pending together");
                              end if;
                           end if;
                        end loop;
                     end if;
                  end loop;

                  --  배타 참조를 거친 접근이나 빌려주기: 겹치는 자손이
                  --  pending이면 안 된다
                  if C.Op in Op_Access | Op_Lend then
                     declare
                        Through : Token_Set :=
                          (if C.Op = Op_Access then Val (S_In, C.Src)
                           else Token_Sets.Empty_Set);
                     begin
                        if C.Op = Op_Lend then
                           for Rg of C.Srcs loop
                              Through.Union (Val (S_In, Rg));
                           end loop;
                        end if;
                        for E of Through loop
                           if Toks (E).Exclusive then
                              for D of Pending loop
                                 if Ancestors (D).Contains (E)
                                   and then Overlaps_Access
                                         (E => E, D => D,
                                          Access_At => C.Access_At)
                                 then
                                    Report
                                      (C.Node,
                                       "an access through an exclusive"
                                       & " reference while the reference"
                                       & " derived from it at "
                                       & Where (Toks (D).Node)
                                       & " is pending");
                                 end if;
                              end loop;
                           end if;
                        end loop;
                     end;
                  end if;

                  --  한 호출이 빌려준 참조끼리 (§8.1.1)
                  if C.Op = Op_Lend then
                     declare
                        Lent : Token_Set;
                     begin
                        for Rg of C.Srcs loop
                           Lent.Union (Val (S_In, Rg));
                        end loop;
                        for E of Lent loop
                           if Toks (E).Exclusive then
                              for X of Lent loop
                                 if X /= E and then Meet (E, X) then
                                    Report
                                      (C.Node,
                                       "an invocation lends an exclusive"
                                       & " reference together with another"
                                       & " reference to the same object");
                                 end if;
                              end loop;
                           end if;
                        end loop;
                     end;
                  end if;

                  --  수명 (§8.3)
                  if C.Op = Op_Store and then C.Src /= 0 then
                     for T of S_In.Vals (C.Src) loop
                        for O of Referents (T) loop
                           if Outlives (C.Obj, O) then
                              Report (C.Node, "a reference to "
                                      & Object_Name (O) & " is stored into "
                                      & Object_Name (C.Obj)
                                      & ", which outlives it");
                           end if;
                        end loop;
                     end loop;
                  end if;

                  if C.Op = Op_Store_Through then
                     for Ref_T of S_In.Vals (C.Src) loop
                        --  지역 객체에 저장
                        for Target of Referents (Ref_T) loop
                           for T of S_In.Vals (C.Src2) loop
                              for O of Referents (T) loop
                                 if Outlives (Target, O) then
                                    Report (C.Node, "a reference to "
                                            & Object_Name (O)
                                            & " is stored into "
                                            & Object_Name (Target)
                                            & ", which outlives it");
                                 end if;
                              end loop;
                           end loop;
                        end loop;
                        --  매개변수 층 K에서 온 참조를 거친 저장: 놓는
                        --  참조는 같은 매개변수의 더 깊은 층에서 왔거나,
                        --  그 층에서 K+1로 routes되어야 한다 (§8.1.2)
                        for Org of Origins (Ref_T) loop
                           declare
                              P : constant Natural := Org / 64;
                              K : constant Natural := Org mod 64;
                           begin
                              for T of S_In.Vals (C.Src2) loop
                                 if not Referents (T).Is_Empty then
                                    Report (C.Node, "a reference to a local"
                                            & " object is stored through a"
                                            & " parameter");
                                 end if;
                                 for F of Origins (T) loop
                                    if not (F / 64 = P and then F mod 64 > K)
                                      and then not Routes_To
                                        (Self_Fn, Layer (F / 64, F mod 64),
                                         Layer (P, K + 1))
                                    then
                                       Report
                                         (C.Node,
                                          "no route takes " & Layer_Name (F)
                                          & " to "
                                          & Layer_Name (P * 64 + K + 1));
                                    end if;
                                 end loop;
                                 if Origins (T).Is_Empty
                                   and then Referents (T).Is_Empty
                                   and then (Toks (T).Exclusive
                                             or else Toks (T).Mut)
                                   and then not Routes_To
                                     (Self_Fn, Static_End, Layer (P, K + 1))
                                 then
                                    Report
                                      (C.Node,
                                       "no route takes static to "
                                       & Layer_Name (P * 64 + K + 1));
                                 end if;
                              end loop;
                           end;
                        end loop;
                     end loop;
                  end if;

                  if C.Op = Op_Return then
                     for T of S_In.Vals (C.Src) loop
                        if not Referents (T).Is_Empty then
                           Report (C.Node, "the returned reference designates"
                                   & " an object that ends when the"
                                   & " subroutine returns");
                        end if;
                        --  반환하는 참조의 층은 return으로 가야 한다
                        for F of Origins (T) loop
                           if not Routes_To
                             (Self_Fn, Layer (F / 64, F mod 64), Return_End)
                           then
                              Report (C.Node, "no route takes "
                                      & Layer_Name (F) & " to return");
                           end if;
                        end loop;
                        if Origins (T).Is_Empty and then Referents (T).Is_Empty
                          and then not Routes_To (Self_Fn, Static_End,
                                                  Return_End)
                        then
                           Report (C.Node, "no route takes static to"
                                   & " return");
                        end if;
                     end loop;
                  end if;

                  --  호출 쪽 수명: static이나 다른 인자의 대상으로 가는
                  --  참조 (§8.3)
                  if C.Op = Op_Lend then
                     declare
                        L     : Layer_Table;
                        Count : Natural;
                        FT    : constant Type_Id := Type_Id (C.Fn);
                     begin
                        Param_Layers (S_In, C, L, Count);
                        for P in 0 .. Count - 1 loop
                           for K in 0 .. Max_Depth loop
                              if Routes_To (FT, Layer (P, K), Static_End) then
                                 for T of L (P, K) loop
                                    for O of Referents (T) loop
                                       Report (C.Node, "the invocation stores"
                                               & " a reference to "
                                               & Object_Name (O)
                                               & " where it outlives it");
                                    end loop;
                                 end loop;
                              end if;
                              if K < Max_Depth then
                                 for R of L (P, K) loop
                                    if Toks (R).Exclusive
                                      or else Toks (R).Mut
                                    then
                                       for Target of Referents (R) loop
                                          for T of Placed_At
                                            (L, Count, FT, P, K)
                                          loop
                                             for O of Referents (T) loop
                                                if Outlives (Target, O) then
                                                   Report
                                                     (C.Node,
                                                      "the invocation stores"
                                                      & " a reference to "
                                                      & Object_Name (O)
                                                      & " into "
                                                      & Object_Name (Target)
                                                      & ", which outlives it");
                                                end if;
                                             end loop;
                                          end loop;
                                       end loop;
                                    end if;
                                 end loop;
                              end if;
                           end loop;
                        end loop;
                     end;
                  end if;
               end;
            end if;
         end loop;
      end;
   end Check_Body;

end Derivation;
