with Ada.Containers.Ordered_Maps;
with Ada.Containers.Vectors;
with Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Check;
with Diagnostics;
with ELF;
with Idents;
with Interfaces;
with KSA;
with Listing;
with MachO;
with Symbols;
with Targets;
with Tokens;
with Types;

package body Emit is

   use AST;
   use Ada.Strings.Unbounded;
   use Instruction_Set;
   use Symbols;
   use Tokens;
   use Types;
   use type Interfaces.Unsigned_64;

   function Img (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   function Get (N : Node_Id) return Node is (Nodes (Positive (N)));
   function Type_Of (N : Node_Id) return Type_Id is
     (Type_Id (Get (N).Ty));

   --  번역 한계나 미구현 요소를 만나면 생성을 멈춘다
   Stop : exception;

   procedure Unimplemented (N : Node_Id; What : String) with No_Return;

   procedure Unimplemented (N : Node_Id; What : String) is
   begin
      Diagnostics.Unimplemented (Get (N).Pos, What);
      raise Stop;
   end Unimplemented;

   ---------------------------------------------------------------------
   --  값의 분류
   --
   --  스칼라는 Temp 하나에 표준형으로 담는다. 집합체는 그 값이 있는
   --  메모리의 주소를 Temp에 담는다. 판별자만 있는 variant(페이로드가
   --  모두 크기 0)는 판별자를 스칼라로 다룬다.

   type Class is (Nothing, Scalar_Class, Aggregate_Class);

   function Scalar_Variant (T : Type_Id) return Boolean is
     (Is_Variant (T) and then Is_Int (KSA.Disc_Type (T))
      and then KSA.Size (T) = KSA.Size (KSA.Disc_Type (T)));

   function Class_Of (T : Type_Id) return Class is
     (case Kind (T) is
        when Ty_Void | Ty_Never | Ty_Error => Nothing,
        when Ty_Int | Ty_Ref | Ty_Fn => Scalar_Class,
        when Ty_Verdict | Ty_Composite =>
          (if Scalar_Variant (T) then Scalar_Class else Aggregate_Class),
        when Ty_Anon | Ty_Array | Ty_Slice => Aggregate_Class);

   function Is_Aggregate (T : Type_Id) return Boolean is
     (Class_Of (T) = Aggregate_Class);

   function Shape (N : Node_Id; T : Type_Id) return Scalar is
      R : constant Type_Rec := Types.Get (T);
   begin
      case R.Kind is
         when Ty_Int =>
            if R.Cells > 8 then
               Unimplemented (N, "integers wider than 64 bits on aarch64"
                              & " (§5.3.2)");
            end if;
            return (R.Cells, R.Signed);
         when Ty_Ref | Ty_Fn =>
            return Word;
         when Ty_Verdict | Ty_Composite =>
            if Scalar_Variant (T) then
               return Shape (N, KSA.Disc_Type (T));
            end if;
         when others =>
            null;
      end case;
      Unimplemented (N, "scalar values of type '" & Image (T) & "'");
   end Shape;

   --  contract의 한쪽 변형: 색인과 판별자 값과 페이로드 (§5.6, §7.2)
   function Side_Variant (T : Type_Id; Success : Boolean) return Positive is
   begin
      if Kind (T) = Ty_Verdict then
         return (if Success then 1 else 2);
      end if;
      declare
         C : constant Composite_Info := Info (T);
      begin
         for I in C.Variants.First_Index .. C.Variants.Last_Index loop
            if (C.Variants (I).Wild = C.Inverted) = Success then
               return I;
            end if;
         end loop;
      end;
      return 1;
   end Side_Variant;

   function Variant_Value (T : Type_Id; Index : Positive)
                           return Long_Long_Integer is
     (if Kind (T) = Ty_Verdict then (if Index = 1 then 1 else 0)
      else Types.Variant (T, Index).Value);

   function Payload_Type (T : Type_Id; Index : Positive) return Type_Id is
     (if Kind (T) = Ty_Verdict
      then (if Index = 1 then Types.Get (T).Pass else Types.Get (T).Fail)
      else Types.Variant (T, Index).Fields.First_Element.Ty);

   function Bits (V : Long_Long_Integer) return Interfaces.Unsigned_64 is
     (if V >= 0 then Interfaces.Unsigned_64 (V)
      else Interfaces.Unsigned_64'Last - Interfaces.Unsigned_64 (-(V + 1)));

   ---------------------------------------------------------------------
   --  생성 상태

   type Loop_Labels is record
      Node               : Node_Id;
      Continue_L, Exit_L : Label;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Labels);
   package Slot_Maps is new Ada.Containers.Ordered_Maps (Node_Id, Natural);

   Loops        : Loop_Vectors.Vector;
   Frame_Top    : Natural := 0;
   String_Count : Natural := 1;
   Node_Temps   : Slot_Maps.Map;  --  집합체를 만드는 식의 임시 자리
   Arg_Copies   : Slot_Maps.Map;  --  주소로 넘기는 집합체 인자의 복사본
   Result_Slot  : Natural := 0;   --  x8로 받은 반환 자리의 주소를 둘 곳

   function Allocate_Slot (Size, Align : Natural) return Natural is
   begin
      Frame_Top := KSA.Round_Up (Frame_Top + Size, Natural'Max (1, Align));
      return Frame_Top;
   end Allocate_Slot;

   --  집합체 자리는 8바이트 단위로 잡아 워드 단위 적재·저장을 허락한다
   function Object_Slot (T : Type_Id) return Natural is
     (if Is_Aggregate (T)
      then Allocate_Slot (KSA.Round_Up (KSA.Size (T), 8),
                          Natural'Max (8, KSA.Align (T)))
      else Allocate_Slot (KSA.Size (T), KSA.Align (T)));

   ---------------------------------------------------------------------

   procedure Generate
     (Unit       : AST.Node_Id;
      M          : in out Instruction_Set.ISA'Class;
      Convention : Calling.Convention'Class;
      Obj        : in out Sections.Object;
      OK         : out Boolean)
   is
      use type Targets.Format_Kind;

      Mach_O : constant Boolean := M.Format = Targets.Format_MachO;

      function Asm_Symbol (Name : String) return String is
        (if Mach_O then MachO.Symbol (Name) else ELF.Symbol (Name));

      function Data_Label (Name : String) return String is
        (if Mach_O then MachO.Private_Symbol (Name)
         else ELF.Private_Symbol (Name));

      function Link_Symbol (S : Symbol_Id) return String is
        (Asm_Symbol (To_String (Symbols.Get (S).Link_Name)));

      procedure Check_Temp (N : Node_Id; R : Temp) is
      begin
         if Natural (R) >= M.Max_Temps then
            Diagnostics.Error
              (Get (N).Pos, "translation limit: expression needs more than"
               & M.Max_Temps'Image & " registers");
            raise Stop;
         end if;
      end Check_Temp;

      function Slot_Of (N : Node_Id) return Natural is
        (Symbols.Get (Symbol_Id (Get (N).Sym)).Slot);

      procedure Bind_Slot (Sym : Natural; T : Type_Id) is
         S : Symbol := Symbols.Get (Symbol_Id (Sym));
      begin
         S.Slot := Object_Slot (T);
         Symbols.Table.Replace_Element (Positive (Sym), S);
      end Bind_Slot;

      --  함수 본문의 let과 집합체 임시값에 프레임 자리를 준다
      procedure Allocate_Frame (N : Node_Id) is
      begin
         if N = No_Node then
            return;
         end if;
         declare
            R : constant Node := Get (N);
         begin
            case R.Kind is
               when Type_Node =>
                  return;
               when N_Let =>
                  Bind_Slot (R.Sym, Type_Of (N));
               when N_Construct | N_Anon | N_Wild_Construct | N_Call =>
                  if Is_Aggregate (Type_Of (N)) then
                     Node_Temps.Include
                       (N, Allocate_Slot
                          (KSA.Round_Up (Natural'Max (KSA.Size (Type_Of (N)),
                                                      16), 8),
                           Natural'Max (8, KSA.Align (Type_Of (N)))));
                  end if;
               when N_If =>
                  if Kind (R.B) /= N_Block and then Is_Aggregate (Type_Of (N))
                  then
                     Node_Temps.Include (N, Object_Slot (Type_Of (N)));
                  end if;
               when N_Unary =>
                  if R.Op = P_Bang and then Is_Aggregate (Type_Of (N)) then
                     Node_Temps.Include (N, Object_Slot (Type_Of (N)));
                  end if;
               when others =>
                  null;
            end case;

            if R.Kind = N_Call then
               for I in 1 .. R.List.Count loop
                  declare
                     Arg : constant Node_Id := Item (R.List, I);
                  begin
                     if Is_Aggregate (Type_Of (Arg))
                       and then KSA.Size (Type_Of (Arg)) > 16
                     then
                        Arg_Copies.Include (Arg, Object_Slot (Type_Of (Arg)));
                     end if;
                  end;
               end loop;
            end if;

            Allocate_Frame (R.A);
            Allocate_Frame (R.B);
            Allocate_Frame (R.C);
            for I in 1 .. R.List.Count loop
               Allocate_Frame (Item (R.List, I));
            end loop;
         end;
      end Allocate_Frame;

      function Find_Loop (Target : Node_Id) return Loop_Labels is
      begin
         for L of Loops loop
            if L.Node = Target then
               return L;
            end if;
         end loop;
         raise Program_Error;
      end Find_Loop;

      procedure Value (N : Node_Id; R : Temp);
      procedure Effect (N : Node_Id);
      procedure Branch
        (N : Node_Id; Target : Label; When_Pass : Boolean; R : Temp := 0);

      function Comparison (Op : Token_Kind; Signed : Boolean)
                           return Condition is
        (case Op is
           when P_Eq_Eq => Eq,
           when P_Ne    => Ne,
           when P_Lt    => (if Signed then Lt else Lo),
           when P_Le    => (if Signed then Le else Ls),
           when P_Gt    => (if Signed then Gt else Hi),
           when others  => (if Signed then Ge else Hs));

      function Arith_Of (Op : Token_Kind) return Arith_Op is
        (case Op is
           when P_Plus | P_Plus_Eq       => Add,
           when P_Minus | P_Minus_Eq     => Sub,
           when P_Star | P_Star_Eq       => Mul,
           when P_Slash | P_Slash_Eq     => Div,
           when P_Percent | P_Percent_Eq => Remainder,
           when P_Amp | P_Amp_Eq         => Bit_And,
           when P_Pipe | P_Pipe_Eq       => Bit_Or,
           when others                   => Bit_Xor);

      --  E의 값을 Dst + Offset에 둔다 (스칼라는 저장, 집합체는 복사)
      procedure Store_Value
        (E : Node_Id; Dst : Temp; Offset : Natural; R : Temp)
      is
         T : constant Type_Id := Type_Of (E);
      begin
         case Class_Of (T) is
            when Nothing =>
               Effect (E);
            when Scalar_Class =>
               Check_Temp (E, R);
               Value (E, R);
               M.Store_Field (R, Dst, Offset, Shape (E, T));
            when Aggregate_Class =>
               Check_Temp (E, R + 1);
               Value (E, R);
               M.Add_Immediate (R + 1, Dst, Offset);
               M.Copy_Memory (R + 1, R, KSA.Size (T));
         end case;
      end Store_Value;

      --  객체 식의 주소. 집합체 값이면 그 값이 있는 곳의 주소.
      procedure Address (N : Node_Id; R : Temp) is
         Rec : constant Node := Get (N);
      begin
         Check_Temp (N, R);
         case Rec.Kind is
            when N_Name =>
               M.Frame_Address (R, Slot_Of (N));
            when N_Unary =>
               if Rec.Op = P_Star then
                  Value (Rec.A, R);
               else
                  Value (N, R);
               end if;
            when N_Field =>
               declare
                  Base_T : constant Type_Id := Type_Of (Rec.A);
                  Target : constant Type_Id :=
                    (if Kind (Base_T) = Ty_Ref then Types.Get (Base_T).Target
                     else Base_T);
                  Offset : constant Natural :=
                    KSA.Field_Offset (Target, Rec.Sym);
               begin
                  if Kind (Base_T) = Ty_Ref then
                     --  참조 투명성: 참조의 값이 곧 객체의 주소
                     Value (Rec.A, R);
                  else
                     Address (Rec.A, R);
                  end if;
                  if Offset > 0 then
                     M.Add_Immediate (R, R, Offset);
                  end if;
               end;
            when others =>
               if Is_Aggregate (Type_Of (N)) then
                  Value (N, R);
               else
                  Unimplemented (N, "addresses of this expression");
               end if;
         end case;
      end Address;

      --  variant 값의 판별자를 R에 (void 판별자는 0)
      procedure Discriminant (N : Node_Id; R : Temp) is
         T : constant Type_Id := Type_Of (N);
      begin
         Value (N, R);
         if Is_Aggregate (T) then
            if KSA.Disc_Type (T) = Void then
               M.Load_Immediate (R, 0);
            else
               M.Load_Field (R, R, 0, Shape (N, KSA.Disc_Type (T)));
            end if;
         end if;
      end Discriminant;

      --  판별자 R이 성공 쪽인지 보고 Target으로 분기
      procedure Branch_On_Side
        (T : Type_Id; R : Temp; When_Pass : Boolean; Target : Label;
         At_Node : Node_Id)
      is
         --  contract는 성공 쪽이 wild가 아닌 변형이고 contract!는 실패
         --  쪽이 그렇다: 그 변형의 값과 같은지로 판정한다
         Inverted : constant Boolean :=
           Kind (T) = Ty_Composite and then Info (T).Inverted;
         Fixed    : constant Positive := Side_Variant (T, not Inverted);
         Value    : constant Long_Long_Integer := Variant_Value (T, Fixed);
         Equal    : constant Boolean := When_Pass /= Inverted;
      begin
         if Value in 0 .. 4095 then
            M.Test_And_Branch (R, Natural (Value), Equal, Target);
         else
            Check_Temp (At_Node, R + 1);
            M.Load_Immediate (R + 1, Bits (Value));
            M.Compare_And_Branch (R, R + 1, (if Equal then Eq else Ne),
                                  Target);
         end if;
      end Branch_On_Side;

      --  contract가 성공 쪽이면 1, 아니면 0
      procedure Success_Flag (N : Node_Id; R : Temp) is
         Fail_L : constant Label := M.New_Label;
         Done_L : constant Label := M.New_Label;
      begin
         Branch (N, Fail_L, When_Pass => False, R => R);
         M.Load_Immediate (R, 1);
         M.Jump (Done_L);
         M.Place (Fail_L);
         M.Load_Immediate (R, 0);
         M.Place (Done_L);
      end Success_Flag;

      --  호출. 결과는 Want_Result일 때 R에 남는다 (집합체면 그 주소).
      procedure Invoke (N : Node_Id; R : Temp; Want_Result : Boolean) is
         Rec    : constant Node := Get (N);
         Callee : constant Symbol_Id := Symbol_Id (Get (Rec.A).Sym);
         Fn     : constant Type_Rec := Types.Get (Type_Of (Rec.A));
         Count  : constant Natural := Rec.List.Count;
         Args   : Calling.Arg_Array (1 .. Count);
         Locs   : Calling.Location_Array (1 .. Count);
         Stack  : Natural;
         Pushed : Natural := 0;
         Ret_Regs     : Natural;
         Ret_Indirect : Boolean;

         function Arg_Type (I : Positive) return Type_Id is
           (Type_Of (Item (Rec.List, I)));

         --  인자 I(값 또는 주소가 Src에)를 제자리에. Spare는 쓸 수 있는
         --  Temp.
         procedure Place_Argument (I : Positive; Src, Spare : Temp) is
            Arg : constant Node_Id := Item (Rec.List, I);
            T   : constant Type_Id := Arg_Type (I);
            L   : constant Calling.Location := Locs (I);
            Ptr : Temp := Src;
         begin
            if Is_Aggregate (T) and then L.By_Reference then
               --  복사본의 주소를 스칼라처럼 넘긴다
               Check_Temp (Arg, Spare);
               M.Frame_Address (Spare, Arg_Copies (Arg));
               M.Copy_Memory (Spare, Src, KSA.Size (T));
               Ptr := Spare;
            elsif Is_Aggregate (T) then
               Check_Temp (Arg, Spare);
               case L.Kind is
                  when Calling.In_Register =>
                     for K in 0 .. L.Count - 1 loop
                        M.Load_Bytes
                          (Spare, Src, 8 * K,
                           Natural'Min (8, KSA.Size (T) - 8 * K));
                        M.Move_To_Argument (L.Index + K, Spare);
                     end loop;
                  when Calling.On_Stack =>
                     M.Stack_Address (Spare, L.Offset);
                     M.Copy_Memory (Spare, Src, KSA.Size (T));
               end case;
               return;
            elsif Class_Of (T) = Nothing then
               return;
            end if;
            case L.Kind is
               when Calling.On_Stack =>
                  M.Store_Outgoing
                    (Ptr, L.Offset,
                     (if Args (I).Variadic or else L.By_Reference then Word
                      else Shape (Arg, T)));
               when Calling.In_Register =>
                  M.Move_To_Argument (L.Index, Ptr);
            end case;
         end Place_Argument;

      begin
         --  살아 있는 임시값을 보존하면 인자는 Temp 0부터 쓸 수 있다
         for T in 0 .. Integer (R) - 1 loop
            M.Save_Temp (Temp (T));
         end loop;
         for I in 1 .. Count loop
            Args (I) := (Size      => KSA.Size (Arg_Type (I)),
                         Variadic  => I > Natural (Fn.Params.Length),
                         Aggregate => Is_Aggregate (Arg_Type (I)));
            if Args (I).Variadic and then Args (I).Aggregate then
               Unimplemented (Item (Rec.List, I),
                              "variadic arguments of composite types");
            end if;
            if Class_Of (Arg_Type (I)) = Scalar_Class then
               Args (I).Size := Shape (Item (Rec.List, I), Arg_Type (I)).Size;
            end if;
         end loop;
         Convention.Lay_Out (Args, Locs, Stack);
         Convention.Return_Location
           (KSA.Size (Fn.Ret), Is_Aggregate (Fn.Ret), Ret_Regs,
            Ret_Indirect);

         if Count < M.Max_Temps then
            --  인자마다 Temp 하나, 남는 하나는 옮길 때 쓴다
            for I in 1 .. Count loop
               Value (Item (Rec.List, I), Temp (I - 1));
            end loop;
            M.Reserve_Outgoing (Stack);
            for I in 1 .. Count loop
               Place_Argument (I, Temp (I - 1), Temp (Count));
            end loop;
         else
            --  Temp가 모자라면 평가하는 대로 스택에 밀어 두었다가 옮긴다.
            --  인자 I는 sp + Stack + 16 * (Count - I)에 있다.
            for I in 1 .. Count loop
               Value (Item (Rec.List, I), 0);
               M.Save_Temp (0);
            end loop;
            M.Reserve_Outgoing (Stack);
            for I in 1 .. Count loop
               M.Load_Stack (0, Stack + 16 * (Count - I));
               Place_Argument (I, 0, 1);
            end loop;
            Pushed := 16 * Count;
         end if;

         if Ret_Indirect then
            --  반환값을 쓸 자리를 x8로 알린다
            M.Frame_Address (0, Node_Temps (N));
            M.Move_To_Argument (8, 0);
         end if;
         M.Call (Link_Symbol (Callee));
         M.Release_Outgoing (Stack + Pushed);

         if Is_Aggregate (Fn.Ret) then
            M.Frame_Address (R, Node_Temps (N));
            if not Ret_Indirect then
               Check_Temp (N, R + 1);
               for K in 0 .. Ret_Regs - 1 loop
                  M.Move_From_Argument (R + 1, K);
                  M.Store_Field (R + 1, R, 8 * K, Word);
               end loop;
            end if;
         elsif Want_Result and then Class_Of (Fn.Ret) = Scalar_Class then
            M.Move_From_Result (R);
            M.Normalize (R, Shape (N, Fn.Ret));
         end if;
         for T in reverse 0 .. Integer (R) - 1 loop
            M.Restore_Temp (Temp (T));
         end loop;
      end Invoke;

      procedure Literal (N : Node_Id; R : Temp) is
         use Ada.Numerics.Big_Numbers.Big_Integers;
         V : Big_Integer := Check.Int_Value (N);
      begin
         if V < 0 then
            V := V + 2 ** 64;
         end if;
         M.Load_Immediate
           (R, Interfaces.Unsigned_64'Value (To_String (V)));
      end Literal;

      procedure String_Literal (N : Node_Id; R : Temp) is
         Name : constant String := Data_Label ("kstr" & Img (String_Count));
      begin
         String_Count := String_Count + 1;
         Sections.Define (Obj, Name, Sections.Const,
                          Sections.Size (Obj, Sections.Const), False);
         for C of To_String (Get (N).Text) loop
            Sections.Append (Obj, Sections.Const, Character'Pos (C));
         end loop;
         M.Data_Address (R, Name);
      end String_Literal;

      --  composite construction (§6.2.3): 0으로 채우고, 판별자를 쓰고,
      --  식을 원문 순서로, 그다음 생략한 필드의 기본값을 선언 순서로
      procedure Construct (N : Node_Id; R : Temp) is
         Rec     : constant Node := Get (N);
         T       : constant Type_Id := Type_Of (N);
         Variant : constant Natural := Rec.Sym;
         Done    : array (1 .. 64) of Boolean := [others => False];

         function Offset_Of (Index : Positive) return Natural is
           (if Variant = 0 then KSA.Field_Offset (T, Index)
            else KSA.Variant_Field_Offset (T, Variant, Index));

         function Field_Count return Natural is
           (if Kind (T) = Ty_Verdict then 1
            elsif Variant = 0 then Natural (Info (T).Fields.Length)
            else Natural (Types.Variant (T, Variant).Fields.Length));

         function Default_Of (Index : Positive) return Natural is
           (if Kind (T) = Ty_Verdict then 0
            elsif Variant = 0 then Types.Field (T, Index).Default
            else Types.Variant (T, Variant).Fields (Index).Default);

      begin
         if Scalar_Variant (T) then
            --  판별자뿐: 페이로드 식은 효과만 남긴다
            for I in 1 .. Rec.List.Count loop
               Effect (Item (Rec.List, I));
            end loop;
            M.Load_Immediate (R, Bits (Variant_Value (T, Variant)));
            return;
         end if;

         Check_Temp (N, R + 1);
         M.Frame_Address (R, Node_Temps (N));
         M.Zero_Memory (R, KSA.Size (T));
         if Variant /= 0 and then KSA.Disc_Type (T) /= Void then
            M.Load_Immediate (R + 1, Bits (Variant_Value (T, Variant)));
            M.Store_Field (R + 1, R, 0, Shape (N, KSA.Disc_Type (T)));
         end if;

         for I in 1 .. Rec.List.Count loop
            declare
               It    : constant Node_Id := Item (Rec.List, I);
               Index : constant Positive :=
                 (if Kind (It) = N_Field_Init then Get (It).Sym else I);
               E     : constant Node_Id :=
                 (if Kind (It) = N_Field_Init then Get (It).A else It);
            begin
               Done (Index) := True;
               Store_Value (E, R, Offset_Of (Index), R + 1);
            end;
         end loop;

         for I in 1 .. Field_Count loop
            if not Done (I) and then Default_Of (I) /= 0 then
               Store_Value (Node_Id (Default_Of (I)), R, Offset_Of (I),
                            R + 1);
            end if;
         end loop;
      end Construct;

      procedure Construct_Anon (N : Node_Id; R : Temp) is
         Rec : constant Node := Get (N);
         T   : constant Type_Id := Type_Of (N);
      begin
         Check_Temp (N, R + 1);
         M.Frame_Address (R, Node_Temps (N));
         M.Zero_Memory (R, KSA.Size (T));
         for I in 1 .. Rec.List.Count loop
            Store_Value (Item (Rec.List, I), R, KSA.Field_Offset (T, I),
                         R + 1);
         end loop;
      end Construct_Anon;

      --  극성 반전 (§7.2.1): 반대쪽 변형으로 페이로드를 옮긴다
      procedure Invert (N : Node_Id; R : Temp) is
         Src_T  : constant Type_Id := Type_Of (Get (N).A);
         Dst_T  : constant Type_Id := Type_Of (N);
         Fail_L : constant Label := M.New_Label;
         Done_L : constant Label := M.New_Label;

         --  원천의 Success 쪽을 결과의 반대쪽으로
         procedure Move_Side (Success : Boolean) is
            From : constant Positive := Side_Variant (Src_T, Success);
            To   : constant Positive := Side_Variant (Dst_T, not Success);
            Size : constant Natural := KSA.Size (Payload_Type (Src_T, From));
         begin
            if Scalar_Variant (Dst_T) then
               M.Load_Immediate (R, Bits (Variant_Value (Dst_T, To)));
               return;
            end if;
            M.Frame_Address (R + 2, Node_Temps (N));
            M.Zero_Memory (R + 2, KSA.Size (Dst_T));
            M.Load_Immediate (R + 1, Bits (Variant_Value (Dst_T, To)));
            M.Store_Field (R + 1, R + 2, 0, Shape (N, KSA.Disc_Type (Dst_T)));
            if Size > 0 then
               M.Add_Immediate
                 (R + 1, R, KSA.Variant_Field_Offset (Src_T, From, 1));
               M.Add_Immediate
                 (R + 2, R + 2, KSA.Variant_Field_Offset (Dst_T, To, 1));
               M.Copy_Memory (R + 2, R + 1, Size);
            end if;
         end Move_Side;

      begin
         Check_Temp (N, R + 2);
         Value (Get (N).A, R);
         if Scalar_Variant (Src_T) then
            Branch_On_Side (Src_T, R, False, Fail_L, N);
         else
            M.Load_Field (R + 1, R, 0, Shape (N, KSA.Disc_Type (Src_T)));
            Branch_On_Side (Src_T, R + 1, False, Fail_L, N);
         end if;
         Move_Side (Success => True);
         M.Jump (Done_L);
         M.Place (Fail_L);
         Move_Side (Success => False);
         M.Place (Done_L);
         if not Scalar_Variant (Dst_T) then
            M.Frame_Address (R, Node_Temps (N));
         end if;
      end Invert;

      --  판별자 추출 (§6.9.6): wild(V)인 변형이면 V
      procedure Extract_Discriminant (N : Node_Id; R : Temp) is
         Src : constant Type_Id := Type_Of (Get (N).A);
         T   : constant Type_Id := Type_Of (N);
      begin
         Discriminant (Get (N).A, R);
         if Kind (Src) = Ty_Verdict then
            --  Fail은 wild(0): 1이 아니면 0
            Check_Temp (N, R + 1);
            M.Load_Immediate (R + 1, 1);
            M.Compare_And_Set (R, R, R + 1, Eq);
         elsif KSA.Disc_Type (Src) /= Void then
            declare
               C : constant Composite_Info := Info (Src);
            begin
               for W of C.Variants loop
                  if W.Wild and then W.Canonical then
                     Check_Temp (N, R + 1);
                     declare
                        Done_L : constant Label := M.New_Label;
                     begin
                        for V of C.Variants loop
                           if not V.Wild then
                              M.Load_Immediate (R + 1, Bits (V.Value));
                              M.Compare_And_Branch (R, R + 1, Eq, Done_L);
                           end if;
                        end loop;
                        M.Load_Immediate (R, Bits (W.Value));
                        M.Place (Done_L);
                     end;
                  end if;
               end loop;
            end;
         end if;
         if Is_Int (T) then
            M.Normalize (R, Shape (N, T));
         end if;
      end Extract_Discriminant;

      procedure Value (N : Node_Id; R : Temp) is
         Rec : constant Node := Get (N);
         T   : constant Type_Id := Type_Of (N);
      begin
         Check_Temp (N, R);
         case Rec.Kind is
            when N_Int_Lit | N_Char_Lit =>
               Literal (N, R);

            when N_String_Lit =>
               String_Literal (N, R);

            when N_Name =>
               if Is_Aggregate (T) then
                  M.Frame_Address (R, Slot_Of (N));
               elsif Class_Of (T) = Scalar_Class then
                  M.Load_Frame (R, Slot_Of (N), Shape (N, T));
               end if;

            when N_Call =>
               Invoke (N, R, Want_Result => True);

            when N_Construct =>
               if Class_Of (T) /= Nothing then
                  Construct (N, R);
               else
                  Effect (N);
               end if;

            when N_Anon =>
               Construct_Anon (N, R);

            when N_Wild_Construct =>
               declare
                  V : constant Long_Long_Integer :=
                    Long_Long_Integer'Value (To_String (Rec.Text));
               begin
                  if Scalar_Variant (T) then
                     M.Load_Immediate (R, Bits (V));
                  else
                     Check_Temp (N, R + 1);
                     M.Frame_Address (R, Node_Temps (N));
                     M.Zero_Memory (R, KSA.Size (T));
                     if KSA.Disc_Type (T) /= Void then
                        M.Load_Immediate (R + 1, Bits (V));
                        M.Store_Field
                          (R + 1, R, 0, Shape (N, KSA.Disc_Type (T)));
                     end if;
                  end if;
               end;

            when N_Unary =>
               case Rec.Op is
                  when P_Minus =>
                     Value (Rec.A, R);
                     M.Unary (Neg, R, R);
                     M.Normalize (R, Shape (N, T));
                  when P_Plus =>
                     Value (Rec.A, R);
                  when P_Bang =>
                     if Is_Contract (T) then
                        Invert (N, R);
                     else
                        Value (Rec.A, R);
                        M.Unary (Bit_Not, R, R);
                        M.Normalize (R, Shape (N, T));
                     end if;
                  when P_Star =>
                     Value (Rec.A, R);
                     if Class_Of (T) = Scalar_Class then
                        M.Load_Field (R, R, 0, Shape (N, T));
                     end if;
                  when P_Percent =>
                     Address (Rec.A, R);
                  when others =>
                     Unimplemented (N, "this unary operator");
               end case;

            when N_Binary =>
               case Rec.Op is
                  when P_Eq_Eq | P_Ne | P_Lt | P_Gt | P_Le | P_Ge =>
                     Value (Rec.A, R);
                     Check_Temp (N, R + 1);
                     Value (Rec.B, R + 1);
                     M.Compare_And_Set
                       (R, R, R + 1,
                        Comparison (Rec.Op, Is_Signed (Type_Of (Rec.A))));
                  when K_And | K_Or =>
                     Success_Flag (N, R);
                  when K_Xor =>
                     --  두 피연산자 모두 평가하고 성공 여부를 비교
                     Check_Temp (N, R + 1);
                     Success_Flag (Rec.A, R);
                     Success_Flag (Rec.B, R + 1);
                     M.Arith (Bit_Xor, R, R, R + 1, (1, False));
                  when others =>
                     Value (Rec.A, R);
                     Check_Temp (N, R + 1);
                     Value (Rec.B, R + 1);
                     M.Arith (Arith_Of (Rec.Op), R, R, R + 1, Shape (N, T));
                     M.Normalize (R, Shape (N, T));
               end case;

            when N_Cast =>
               if Is_Variant (Type_Of (Rec.A)) then
                  Extract_Discriminant (N, R);
               else
                  Value (Rec.A, R);
                  if Is_Int (T) then
                     M.Normalize (R, Shape (N, T));
                  end if;
               end if;

            when N_Field =>
               declare
                  Base_T : constant Type_Id := Type_Of (Rec.A);
                  Target : constant Type_Id :=
                    (if Kind (Base_T) = Ty_Ref then Types.Get (Base_T).Target
                     else Base_T);
               begin
                  if Kind (Target) = Ty_Array then
                     if Idents.Image (Rec.Name) = "len" then
                        M.Load_Immediate
                          (R, Interfaces.Unsigned_64
                                (Types.Get (Target).Length));
                     elsif Kind (Base_T) = Ty_Ref then
                        --  참조를 거친 투영: 배열의 주소가 첫 원소의 주소
                        Value (Rec.A, R);
                     else
                        Address (Rec.A, R);
                     end if;
                  else
                     Address (N, R);
                     if Class_Of (T) = Scalar_Class then
                        M.Load_Field (R, R, 0, Shape (N, T));
                     end if;
                  end if;
               end;

            when N_If =>
               declare
                  Else_L : constant Label := M.New_Label;
                  Done_L : constant Label := M.New_Label;

                  procedure Arm (E : Node_Id) is
                  begin
                     Value (E, R);
                     if Is_Aggregate (T) then
                        Check_Temp (N, R + 1);
                        M.Frame_Address (R + 1, Node_Temps (N));
                        M.Copy_Memory (R + 1, R, KSA.Size (T));
                     end if;
                  end Arm;
               begin
                  Branch (Rec.A, Else_L, When_Pass => False, R => R);
                  Arm (Rec.B);
                  M.Jump (Done_L);
                  M.Place (Else_L);
                  Arm (Rec.C);
                  M.Place (Done_L);
                  if Is_Aggregate (T) then
                     M.Frame_Address (R, Node_Temps (N));
                  end if;
               end;

            when N_Return | N_Break | N_Continue | N_Block | N_Airside
               | N_While | N_Loop | N_Assign =>
               Effect (N);

            when others =>
               Unimplemented (N, "values of this expression");
         end case;
      end Value;

      procedure Branch
        (N : Node_Id; Target : Label; When_Pass : Boolean; R : Temp := 0)
      is
         Rec : constant Node := Get (N);
      begin
         if Rec.Kind = N_Binary
           and then Rec.Op in P_Eq_Eq | P_Ne | P_Lt | P_Gt | P_Le | P_Ge
         then
            declare
               C : constant Condition :=
                 Comparison (Rec.Op, Is_Signed (Type_Of (Rec.A)));
            begin
               Value (Rec.A, R);
               Check_Temp (N, R + 1);
               Value (Rec.B, R + 1);
               M.Compare_And_Branch
                 (R, R + 1, (if When_Pass then C else Negate (C)), Target);
            end;
         elsif Rec.Kind = N_Binary and then Rec.Op in K_And | K_Or then
            --  단락 평가 (§7.2.2)
            if (Rec.Op = K_And) = When_Pass then
               declare
                  Skip : constant Label := M.New_Label;
               begin
                  Branch (Rec.A, Skip, not When_Pass, R);
                  Branch (Rec.B, Target, When_Pass, R);
                  M.Place (Skip);
               end;
            else
               Branch (Rec.A, Target, When_Pass, R);
               Branch (Rec.B, Target, When_Pass, R);
            end if;
         elsif Rec.Kind = N_Unary and then Rec.Op = P_Bang
           and then Is_Contract (Type_Of (N))
         then
            --  반전한 값의 성패는 원래 값의 반대
            Branch (Rec.A, Target, not When_Pass, R);
         else
            Discriminant (N, R);
            Branch_On_Side (Type_Of (N), R, When_Pass, Target, N);
         end if;
      end Branch;

      procedure Assign (N : Node_Id) is
         Rec   : constant Node := Get (N);
         Place : constant Node := Get (Rec.A);
         T     : constant Type_Id := Type_Of (Rec.A);
      begin
         if Is_Aggregate (T) then
            --  객체를 정하고, 오른쪽을 평가하고, 복사한다 (§6.8.1)
            Address (Rec.A, 0);
            Value (Rec.B, 1);
            M.Copy_Memory (0, 1, KSA.Size (T));
         elsif Class_Of (T) = Nothing then
            Effect (Rec.B);
         elsif Place.Kind = N_Name then
            declare
               S : constant Scalar := Shape (Rec.A, T);
            begin
               if Rec.Op = P_Eq then
                  Value (Rec.B, 0);
               else
                  M.Load_Frame (0, Slot_Of (Rec.A), S);
                  Value (Rec.B, 1);
                  M.Arith (Arith_Of (Rec.Op), 0, 0, 1, S);
                  M.Normalize (0, S);
               end if;
               M.Store_Frame (0, Slot_Of (Rec.A), S);
            end;
         else
            declare
               S : constant Scalar := Shape (Rec.A, T);
            begin
               Address (Rec.A, 0);
               if Rec.Op = P_Eq then
                  Value (Rec.B, 1);
               else
                  M.Load_Field (1, 0, 0, S);
                  Check_Temp (N, 2);
                  Value (Rec.B, 2);
                  M.Arith (Arith_Of (Rec.Op), 1, 1, 2, S);
                  M.Normalize (1, S);
               end if;
               M.Store_Field (1, 0, 0, S);
            end;
         end if;
      end Assign;

      procedure Effect (N : Node_Id) is
         Rec : constant Node := Get (N);
      begin
         case Rec.Kind is
            when N_Assign =>
               Assign (N);

            when N_Call =>
               Invoke (N, 0, Want_Result => False);

            when N_Block =>
               for I in 1 .. Rec.List.Count loop
                  declare
                     Item_N : constant Node_Id := Item (Rec.List, I);
                     T      : constant Type_Id := Type_Of (Item_N);
                  begin
                     if Kind (Item_N) /= N_Let then
                        Effect (Item_N);
                     elsif Is_Aggregate (T) then
                        Value (Get (Item_N).B, 0);
                        M.Frame_Address (1, Slot_Of (Item_N));
                        M.Copy_Memory (1, 0, KSA.Size (T));
                     elsif Class_Of (T) = Scalar_Class then
                        Value (Get (Item_N).B, 0);
                        M.Store_Frame
                          (0, Slot_Of (Item_N), Shape (Item_N, T));
                     else
                        Effect (Get (Item_N).B);
                     end if;
                  end;
               end loop;

            when N_Airside =>
               Effect (Rec.A);

            when N_If =>
               declare
                  Else_L : constant Label := M.New_Label;
                  Done_L : constant Label := M.New_Label;
               begin
                  Branch (Rec.A, Else_L, When_Pass => False);
                  Effect (Rec.B);
                  if Rec.C /= No_Node then
                     M.Jump (Done_L);
                     M.Place (Else_L);
                     Effect (Rec.C);
                     M.Place (Done_L);
                  else
                     M.Place (Else_L);
                  end if;
               end;

            when N_While | N_Loop =>
               declare
                  L : constant Loop_Labels := (N, M.New_Label, M.New_Label);
               begin
                  Loops.Append (L);
                  M.Place (L.Continue_L);
                  if Rec.Kind = N_While then
                     Branch (Rec.A, L.Exit_L, When_Pass => False);
                     Effect (Rec.B);
                  else
                     Effect (Rec.A);
                  end if;
                  M.Jump (L.Continue_L);
                  M.Place (L.Exit_L);
                  Loops.Delete_Last;
               end;

            when N_Break =>
               M.Jump (Find_Loop (Node_Id (Rec.Sym)).Exit_L);
            when N_Continue =>
               M.Jump (Find_Loop (Node_Id (Rec.Sym)).Continue_L);

            when N_Return =>
               if Rec.A /= No_Node then
                  declare
                     T        : constant Type_Id := Type_Of (Rec.A);
                     Regs     : Natural;
                     Indirect : Boolean;
                  begin
                     Convention.Return_Location
                       (KSA.Size (T), Is_Aggregate (T), Regs, Indirect);
                     if Is_Aggregate (T) then
                        Value (Rec.A, 0);
                        if Indirect then
                           M.Load_Frame (1, Result_Slot, Word);
                           M.Copy_Memory (1, 0, KSA.Size (T));
                        else
                           for K in 0 .. Regs - 1 loop
                              M.Load_Bytes
                                (1, 0, 8 * K,
                                 Natural'Min (8, KSA.Size (T) - 8 * K));
                              M.Move_To_Argument (K, 1);
                           end loop;
                        end if;
                     elsif Class_Of (T) = Scalar_Class then
                        Value (Rec.A, 0);
                        M.Move_To_Result (0);
                     else
                        Effect (Rec.A);
                     end if;
                  end;
               end if;
               M.Jump_To_Return;

            when N_Int_Lit | N_Char_Lit | N_String_Lit | N_Name =>
               null;

            when N_Construct =>
               if Class_Of (Type_Of (N)) = Nothing then
                  for I in 1 .. Rec.List.Count loop
                     declare
                        It : constant Node_Id := Item (Rec.List, I);
                     begin
                        Effect (if Kind (It) = N_Field_Init then Get (It).A
                                else It);
                     end;
                  end loop;
               else
                  Value (N, 0);
               end if;

            when others =>
               Value (N, 0);
         end case;
      end Effect;

      procedure Function_Body (N : Node_Id) is
         Rec      : constant Node := Get (N);
         Sym      : Symbol := Symbols.Get (Symbol_Id (Rec.Sym));
         Count    : constant Natural := Rec.List.Count;
         Args     : Calling.Arg_Array (1 .. Count);
         Locs     : Calling.Location_Array (1 .. Count);
         Stack    : Natural;
         Regs     : Natural;
         Indirect : Boolean;
         Ret      : Type_Id;
      begin
         if Length (Sym.Link_Name) = 0 then
            --  외부 이름이 없는 정의의 이름은 구현 정의 (§4.2.2)
            Sym.Link_Name := To_Unbounded_String
              ("kf_" & Idents.Image (Rec.Name));
            Symbols.Table.Replace_Element (Positive (Rec.Sym), Sym);
         end if;

         Ret := Types.Get (Type_Id (Sym.Ty)).Ret;
         Convention.Return_Location
           (KSA.Size (Ret), Is_Aggregate (Ret), Regs, Indirect);

         Frame_Top := 0;
         Node_Temps.Clear;
         Arg_Copies.Clear;
         for I in 1 .. Count loop
            declare
               P : constant Node_Id := Item (Rec.List, I);
               T : constant Type_Id := Type_Of (P);
            begin
               Bind_Slot (Get (P).Sym, T);
               Args (I) := (Size      => KSA.Size (T),
                            Variadic  => False,
                            Aggregate => Is_Aggregate (T));
               if Class_Of (T) = Scalar_Class then
                  Args (I).Size := Shape (P, T).Size;
               end if;
            end;
         end loop;
         if Indirect then
            Result_Slot := Allocate_Slot (8, 8);
         end if;
         Allocate_Frame (Rec.B);
         Convention.Lay_Out (Args, Locs, Stack);

         M.Begin_Function
           (Link_Symbol (Symbol_Id (Rec.Sym)),
            Global     => Rec.Flags (F_Extern) or else Rec.Flags (F_Pub),
            Frame_Size => KSA.Round_Up (Frame_Top, 16));
         if Indirect then
            M.Store_Incoming (8, Result_Slot, Word);
         end if;

         for I in 1 .. Count loop
            declare
               P    : constant Node_Id := Item (Rec.List, I);
               T    : constant Type_Id := Type_Of (P);
               L    : constant Calling.Location := Locs (I);
               Slot : constant Natural := Slot_Of (P);
            begin
               if Is_Aggregate (T) and then not L.By_Reference then
                  case L.Kind is
                     when Calling.In_Register =>
                        --  워드 K는 객체의 8K번째 셀부터
                        for K in 0 .. L.Count - 1 loop
                           M.Store_Incoming (L.Index + K, Slot - 8 * K, Word);
                        end loop;
                     when Calling.On_Stack =>
                        M.Incoming_Address (0, L.Offset);
                        M.Frame_Address (1, Slot);
                        M.Copy_Memory (1, 0, KSA.Size (T));
                  end case;
               elsif Is_Aggregate (T) then
                  --  복사본의 주소가 왔다
                  case L.Kind is
                     when Calling.In_Register =>
                        M.Move_From_Argument (0, L.Index);
                     when Calling.On_Stack =>
                        M.Load_Incoming (0, L.Offset, Word);
                  end case;
                  M.Frame_Address (1, Slot);
                  M.Copy_Memory (1, 0, KSA.Size (T));
               elsif Class_Of (T) = Scalar_Class then
                  case L.Kind is
                     when Calling.In_Register =>
                        M.Store_Incoming (L.Index, Slot, Shape (P, T));
                     when Calling.On_Stack =>
                        M.Load_Incoming (0, L.Offset, Shape (P, T));
                        M.Store_Frame (0, Slot, Shape (P, T));
                  end case;
               end if;
            end;
         end loop;
         Effect (Rec.B);
         M.End_Function;
      end Function_Body;

      U : constant Node := Get (Unit);
   begin
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) = N_Fn then
            Function_Body (Item (U.List, I));
         end if;
      end loop;
      OK := True;
   exception
      when Stop =>
         OK := False;
   end Generate;

   function Text
     (M : Instruction_Set.ISA'Class; Obj : Sections.Object) return String
   is
      use type Targets.Format_Kind;
      use type Sections.Section_Kind;
      Mach_O : constant Boolean := M.Format = Targets.Format_MachO;
      Bytes  : Sections.Byte_Vectors.Vector renames
        Obj.Contents (Sections.Const);
   begin
      Listing.Clear;
      Listing.Put_Line (if Mach_O then MachO.Text_Section
                        else ELF.Text_Section);
      M.Write_Text;
      if Bytes.Is_Empty then
         return Listing.Contents;
      end if;

      Listing.Put_Line (if Mach_O then MachO.Const_Section
                        else ELF.Const_Section);
      for I in Obj.Symbols.First_Index .. Obj.Symbols.Last_Index loop
         declare
            S    : constant Sections.Symbol := Obj.Symbols (I);
            Stop : Natural := Natural (Bytes.Length);
            Line : Unbounded_String;
         begin
            if S.Defined and then S.Section = Sections.Const then
               --  다음 데이터 심볼까지가 이 심볼의 바이트
               for J in I + 1 .. Obj.Symbols.Last_Index loop
                  if Obj.Symbols (J).Defined
                    and then Obj.Symbols (J).Section = Sections.Const
                  then
                     Stop := Obj.Symbols (J).Offset;
                     exit;
                  end if;
               end loop;
               Listing.Put_Line (To_String (S.Name) & ":");
               for K in S.Offset .. Stop - 1 loop
                  Append (Line, (if Length (Line) = 0 then "" else ", ")
                          & Img (Natural (Bytes.Element (K))));
               end loop;
               if Length (Line) > 0 then
                  Listing.Instr (".byte " & To_String (Line));
               end if;
            end if;
         end;
      end loop;
      return Listing.Contents;
   end Text;

end Emit;
