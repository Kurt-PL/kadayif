with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Diagnostics;
with Idents;
with Symbols;
with Tokens;
with Types;

package body Flow is

   use AST;
   use Tokens;
   use Types;
   use type Symbols.Symbol_Kind;

   package Symbol_Sets is new Ada.Containers.Ordered_Sets (Natural);
   use type Symbol_Sets.Set;

   --  어떤 trace에서 그럴 수 있는 바인딩들. Dead면 이 지점에 이르는
   --  trace가 없다.
   type State is record
      Invalid   : Symbol_Sets.Set;  --  값을 옮겼다 (§8.7)
      Uninit    : Symbol_Sets.Set;  --  아직 초기화되지 않았다 (§4.3)
      Assigned  : Symbol_Sets.Set;  --  이미 저장했다 (단일 대입, §4.3)
      Dead      : Boolean := False;
   end record;

   function Merge (A, B : State) return State is
     (if A.Dead then B elsif B.Dead then A
      else (A.Invalid or B.Invalid, A.Uninit or B.Uninit,
            A.Assigned or B.Assigned, False));

   Dead_State : constant State := (Dead => True, others => <>);

   type Loop_Context is record
      Node      : Node_Id;
      Breaks    : State := Dead_State;
      Continues : State := Dead_State;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Context);

   Loops  : Loop_Vectors.Vector;
   Silent : Boolean := False;  --  루프의 고정점을 찾는 동안은 진단하지 않는다

   function Get (N : Node_Id) return Node is (Nodes (Positive (N)));
   function Type_Of (N : Node_Id) return Type_Id is (Type_Id (Get (N).Ty));

   --  자동 객체 바인딩을 가리키는 이름 식의 심볼, 아니면 0
   function Binding (N : Node_Id) return Natural is
      R : constant Node := Get (N);
   begin
      if R.Kind = N_Name and then R.Sym /= 0
        and then Symbols.Get (Symbols.Symbol_Id (R.Sym)).Kind
                 in Symbols.Sym_Local | Symbols.Sym_Param
      then
         return R.Sym;
      end if;
      return 0;
   end Binding;

   --  참조를 거치지 않는 필드 열의 바깥 바인딩: p.a.b → p
   function Root (N : Node_Id) return Natural is
      R : constant Node := Get (N);
   begin
      if R.Kind = N_Field and then Kind (Type_Of (R.A)) /= Ty_Ref then
         return Root (R.A);
      end if;
      return Binding (N);
   end Root;

   function Name (Sym : Natural) return String is
     ("'" & Idents.Image (Symbols.Get (Symbols.Symbol_Id (Sym)).Name) & "'");

   --  바인딩의 객체를 읽거나, 관리 참조를 만들거나, 구성 객체에
   --  저장한다: 옮기지 않았고 확실히 초기화되어 있어야 한다
   procedure Require_Valid (S : State; Sym : Natural; At_Node : Node_Id) is
   begin
      if Sym = 0 or else S.Dead or else Silent then
         return;
      elsif S.Invalid.Contains (Sym) then
         Diagnostics.Error
           (Get (At_Node).Pos,
            Name (Sym) & " is used after its value was transferred");
      elsif S.Uninit.Contains (Sym) then
         Diagnostics.Error
           (Get (At_Node).Pos,
            Name (Sym) & " is used before it is definitely initialized");
      end if;
   end Require_Valid;

   --  바인딩 Sym에 값을 통째로 저장한다
   procedure Store_Whole
     (S : in out State; Sym : Natural; At_Node : Node_Id) is
   begin
      if S.Dead then
         return;
      end if;
      --  초기식이 있는 단일 대입 바인딩은 의미 분석이 이미 거절한다
      if not Symbols.Get (Symbols.Symbol_Id (Sym)).Mutable
        and then Symbols.Get (Symbols.Symbol_Id (Sym)).Deferred
        and then S.Assigned.Contains (Sym) and then not Silent
      then
         Diagnostics.Error
           (Get (At_Node).Pos,
            Name (Sym) & " is a single-assignment binding stored into more"
            & " than once on some trace");
      end if;
      S.Assigned.Include (Sym);
      S.Uninit.Exclude (Sym);
      S.Invalid.Exclude (Sym);
   end Store_Whole;

   procedure Walk (N : Node_Id; S : in out State);

   --  contract의 두 페이로드 타입이 모두 복사 가능한가
   function Payloads_Copyable (T : Type_Id) return Boolean is
   begin
      if Kind (T) = Ty_Verdict then
         return Is_Copyable (Get (T).Pass) and then Is_Copyable (Get (T).Fail);
      end if;
      declare
         C : constant Composite_Info := Info (T);
      begin
         for V of C.Variants loop
            for F of V.Fields loop
               if not Is_Copyable (F.Ty) then
                  return False;
               end if;
            end loop;
         end loop;
      end;
      return True;
   end Payloads_Copyable;

   --  값을 내는 적재. 복사할 수 없으면 원천의 바깥 객체를 무효로 한다.
   procedure Load (N : Node_Id; S : in out State) is
      Base : constant Natural := Root (N);
   begin
      Require_Valid (S, Base, N);
      if not S.Dead and then not Is_Copyable (Type_Of (N)) then
         S.Invalid.Include (Base);
      end if;
   end Load;

   --  값을 쓰지 않고 객체만 살피는 사용: 판별자만 읽기, 매칭만 하기
   procedure Inspect (N : Node_Id; S : in out State) is
      Base : constant Natural := Root (N);
   begin
      if Base = 0 then
         Walk (N, S);
      else
         Require_Valid (S, Base, N);
      end if;
   end Inspect;

   procedure Walk_List (L : List_Id; S : in out State) is
   begin
      for I in 1 .. L.Count loop
         Walk (Item (L, I), S);
      end loop;
   end Walk_List;

   function Find (Target : Node_Id) return Positive is
   begin
      for I in reverse Loops.First_Index .. Loops.Last_Index loop
         if Loops (I).Node = Target then
            return I;
         end if;
      end loop;
      raise Program_Error;
   end Find;

   --  while과 loop: 머리의 상태가 더 넓어지지 않을 때까지 조용히
   --  돌린 뒤, 그 상태로 한 번 더 돌며 진단한다
   procedure Walk_Loop (N : Node_Id; S : in out State) is
      R       : constant Node := Get (N);
      Head    : State := S;
      Saved   : constant Boolean := Silent;
      Exit_St : State;

      procedure Once (Report : Boolean) is
         Body_St : State := Head;
         Ctx     : Loop_Context;
      begin
         Silent := Saved or else not Report;
         Ctx.Node := N;
         Loops.Append (Ctx);
         Exit_St := Dead_State;
         if R.Kind = N_While then
            Inspect (R.A, Body_St);
            Exit_St := Body_St;
            Walk (R.B, Body_St);
         else
            Walk (R.A, Body_St);
         end if;
         Ctx := Loops.Last_Element;
         Loops.Delete_Last;
         Exit_St := Merge (Exit_St, Ctx.Breaks);
         Body_St := Merge (Body_St, Ctx.Continues);
         Head := Merge (Head, Body_St);
      end Once;

   begin
      for Round in 1 .. 64 loop
         declare
            Before : constant State := Head;
         begin
            Once (Report => False);
            exit when Head = Before;
         end;
      end loop;
      Once (Report => True);
      Silent := Saved;
      S := Exit_St;
   end Walk_Loop;

   procedure Walk (N : Node_Id; S : in out State) is
   begin
      if N = No_Node or else S.Dead then
         return;
      end if;
      declare
         R : constant Node := Get (N);
      begin
         case R.Kind is
            when N_Name =>
               --  서브루틴 이름처럼 바인딩이 아닌 이름은 적재하지 않는다
               if Binding (N) /= 0 then
                  Load (N, S);
               end if;

            when N_Field =>
               if Root (N) /= 0 then
                  Load (N, S);
               elsif Kind (Type_Of (R.A)) = Ty_Ref then
                  --  참조 투명성: 참조를 옮기지 않는다
                  Inspect (R.A, S);
               else
                  Walk (R.A, S);
               end if;

            when N_Let =>
               Walk (R.B, S);
               if R.Sym /= 0 and then not S.Dead then
                  if R.B = No_Node then
                     --  지연 초기화: 아직 아무것도 저장하지 않았다
                     S.Uninit.Include (R.Sym);
                     S.Assigned.Exclude (R.Sym);
                     S.Invalid.Exclude (R.Sym);
                  else
                     S.Assigned.Exclude (R.Sym);
                     Store_Whole (S, R.Sym, N);
                  end if;
               end if;

            when N_Assign =>
               declare
                  Target : constant Natural := Binding (R.A);
               begin
                  if Target /= 0 and then R.Op = P_Eq then
                     --  바인딩에 직접 저장하면 다시 유효해진다
                     Walk (R.B, S);
                     Store_Whole (S, Target, N);
                  elsif Target /= 0 then
                     --  복합 대입: 읽고 나서 저장한다
                     Require_Valid (S, Target, R.A);
                     Walk (R.B, S);
                     Store_Whole (S, Target, N);
                  else
                     --  구성 객체에 저장하거나 복합 대입: 바깥 객체가
                     --  유효해야 한다
                     if Root (R.A) /= 0 then
                        Require_Valid (S, Root (R.A), R.A);
                     elsif Get (R.A).Kind = N_Unary then
                        --  *p = v: 참조로 대상을 가리킬 뿐 옮기지 않는다
                        Inspect (Get (R.A).A, S);
                     else
                        Walk (R.A, S);
                     end if;
                     Walk (R.B, S);
                  end if;
               end;

            when N_Unary =>
               case R.Op is
                  when P_Percent =>
                     --  비관리 참조를 만드는 것은 적재가 아니다
                     if Root (R.A) = 0 then
                        if Get (R.A).Kind = N_Unary then
                           Walk (Get (R.A).A, S);
                        else
                           Walk (R.A, S);
                        end if;
                     end if;
                  when P_Bang =>
                     --  극성 반전은 매칭하고 페이로드를 가져간다 (§7.2.1).
                     --  옮겨지는 것은 가져간 페이로드뿐이다 (§8.7).
                     if Is_Contract (Type_Of (R.A))
                       and then Payloads_Copyable (Type_Of (R.A))
                     then
                        Inspect (R.A, S);
                     else
                        Walk (R.A, S);
                     end if;
                  when P_Star =>
                     --  역참조는 참조로 대상을 가리킬 뿐 참조를 옮기지 않는다
                     Inspect (R.A, S);
                  when P_Amp | P_Dollar =>
                     --  관리 참조를 만드는 것은 적재가 아니지만, 무효인
                     --  객체에는 만들 수 없다
                     if Root (R.A) /= 0 then
                        Require_Valid (S, Root (R.A), R.A);
                     elsif Get (R.A).Kind = N_Unary
                       and then Get (R.A).Op = P_Star
                     then
                        Inspect (Get (R.A).A, S);
                     else
                        Walk (R.A, S);
                     end if;
                  when others =>
                     Walk (R.A, S);
               end case;

            when N_Cast =>
               --  판별자 추출과 참조의 캐스트는 값을 옮기지 않는다
               if Is_Variant (Type_Of (R.A))
                 or else Kind (Type_Of (R.A)) in Ty_Ref | Ty_Slice
               then
                  Inspect (R.A, S);
               else
                  Walk (R.A, S);
               end if;

            when N_Binary =>
               if R.Op in K_And | K_Or | K_Xor then
                  --  피연산자는 매칭만 한다
                  Inspect (R.A, S);
                  if R.Op = K_Xor then
                     Inspect (R.B, S);
                  else
                     declare
                        Right : State := S;
                     begin
                        Inspect (R.B, Right);
                        S := Merge (S, Right);
                     end;
                  end if;
               else
                  Walk (R.A, S);
                  Walk (R.B, S);
               end if;

            when N_Call | N_Construct | N_Anon | N_Block =>
               if R.Kind = N_Call then
                  Walk (R.A, S);
               end if;
               Walk_List (R.List, S);

            when N_Field_Init =>
               Walk (R.A, S);

            when N_Airside =>
               Walk (R.A, S);

            when N_If =>
               Inspect (R.A, S);
               declare
                  Else_St : State := S;
               begin
                  Walk (R.B, S);
                  Walk (R.C, Else_St);
                  S := Merge (S, Else_St);
               end;

            when N_While | N_Loop =>
               Walk_Loop (N, S);

            when N_Break | N_Continue =>
               if R.Sym /= 0 then
                  declare
                     I   : constant Positive := Find (Node_Id (R.Sym));
                     Ctx : Loop_Context := Loops (I);
                  begin
                     if R.Kind = N_Break then
                        Ctx.Breaks := Merge (Ctx.Breaks, S);
                     else
                        Ctx.Continues := Merge (Ctx.Continues, S);
                     end if;
                     Loops.Replace_Element (I, Ctx);
                  end;
               end if;
               S := Dead_State;

            when N_Return =>
               Walk (R.A, S);
               S := Dead_State;

            when others =>
               null;
         end case;
      end;
   end Walk;

   procedure Check_Transfers (Fn : Node_Id) is
      S : State;
   begin
      Loops.Clear;
      Silent := False;
      Walk (Get (Fn).B, S);
   end Check_Transfers;

end Flow;
