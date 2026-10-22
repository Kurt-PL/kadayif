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

   --  값 레지스터로 다룰 수 있는 타입의 모양
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
         when Ty_Verdict =>
            if KSA.Size (T) /= 1 then
               Unimplemented (N, "contract values with payloads (§5.6)");
            end if;
            return (1, False);
         when others =>
            Unimplemented (N, "values of type '" & Image (T) & "'");
      end case;
   end Shape;

   ---------------------------------------------------------------------
   --  생성 상태

   type String_Data is record
      Label : Unbounded_String;
      Bytes : Unbounded_String;
   end record;
   package Data_Vectors is new Ada.Containers.Vectors (Positive, String_Data);

   type Loop_Labels is record
      Node             : Node_Id;
      Continue_L, Exit_L : Label;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Labels);

   Data      : Data_Vectors.Vector;
   Loops     : Loop_Vectors.Vector;
   Frame_Top : Natural := 0;

   ---------------------------------------------------------------------

   function Generate
     (Unit       : AST.Node_Id;
      M          : in out Instruction_Set.ISA'Class;
      Convention : Calling.Convention'Class) return String
   is
      use type Targets.Format_Kind;

      Mach_O : constant Boolean := M.Format = Targets.Format_MachO;

      function Asm_Symbol (Name : String) return String is
        (if Mach_O then MachO.Symbol (Name) else ELF.Symbol (Name));

      function Data_Label (Name : String) return String is
        (if Mach_O then MachO.Local_Label (Name) else ELF.Local_Label (Name));

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

      --  자동 객체 하나에 프레임 자리를 준다 (§2.2.7)
      procedure Allocate (Sym : Natural; T : Type_Id) is
         S : Symbol := Symbols.Get (Symbol_Id (Sym));
      begin
         Frame_Top := KSA.Round_Up
           (Frame_Top + KSA.Size (T), Natural'Max (1, KSA.Align (T)));
         S.Slot := Frame_Top;
         Symbols.Table.Replace_Element (Positive (Sym), S);
      end Allocate;

      procedure Allocate_Lets (N : Node_Id) is
      begin
         if N = No_Node then
            return;
         end if;
         declare
            R : constant Node := Get (N);
         begin
            case R.Kind is
               when N_Let =>
                  Allocate (R.Sym, Type_Of (N));
                  Allocate_Lets (R.B);
               when N_Block =>
                  for I in 1 .. R.List.Count loop
                     Allocate_Lets (Item (R.List, I));
                  end loop;
               when N_If =>
                  Allocate_Lets (R.A);
                  Allocate_Lets (R.B);
                  Allocate_Lets (R.C);
               when N_While | N_Loop | N_Airside =>
                  Allocate_Lets (R.A);
                  Allocate_Lets (R.B);
               when others =>
                  null;
            end case;
         end;
      end Allocate_Lets;

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

      --  객체 식의 주소
      procedure Address (N : Node_Id; R : Temp) is
         Rec : constant Node := Get (N);
      begin
         Check_Temp (N, R);
         if Rec.Kind = N_Name then
            M.Frame_Address (R, Slot_Of (N));
         elsif Rec.Kind = N_Unary and then Rec.Op = P_Star then
            Value (Rec.A, R);
         else
            Unimplemented (N, "addresses of this expression");
         end if;
      end Address;

      --  호출. 결과는 Want_Result일 때 R에 남는다.
      procedure Invoke (N : Node_Id; R : Temp; Want_Result : Boolean) is
         Rec    : constant Node := Get (N);
         Callee : constant Symbol_Id := Symbol_Id (Get (Rec.A).Sym);
         Fn     : constant Type_Rec := Types.Get (Type_Of (Rec.A));
         Count  : constant Natural := Rec.List.Count;
         Args   : Calling.Arg_Array (1 .. Count);
         Locs   : Calling.Location_Array (1 .. Count);
         Shapes : array (1 .. Count) of Scalar;
         Stack  : Natural;
      begin
         --  살아 있는 임시값을 보존하면 인자는 Temp 0부터 쓸 수 있다
         for T in 0 .. Integer (R) - 1 loop
            M.Save_Temp (Temp (T));
         end loop;
         for I in 1 .. Count loop
            declare
               Arg : constant Node_Id := Item (Rec.List, I);
            begin
               Shapes (I) := Shape (Arg, Type_Of (Arg));
               Args (I) := (Size     => Shapes (I).Size,
                            Variadic => I > Natural (Fn.Params.Length));
               Check_Temp (Arg, Temp (I - 1));
               Value (Arg, Temp (I - 1));
            end;
         end loop;
         Convention.Lay_Out (Args, Locs, Stack);
         M.Reserve_Outgoing (Stack);
         for I in 1 .. Count loop
            case Locs (I).Kind is
               when Calling.On_Stack =>
                  M.Store_Outgoing
                    (Temp (I - 1), Locs (I).Offset,
                     (if Args (I).Variadic then Word else Shapes (I)));
               when Calling.In_Register =>
                  M.Move_To_Argument (Locs (I).Index, Temp (I - 1));
            end case;
         end loop;
         M.Call (Link_Symbol (Callee));
         M.Release_Outgoing (Stack);
         if Want_Result then
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
         Name : constant String :=
           Data_Label ("kstr" & Img (Natural (Data.Length) + 1));
      begin
         Data.Append (String_Data'(To_Unbounded_String (Name), Get (N).Text));
         M.Data_Address (R, Name);
      end String_Literal;

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
               M.Load_Frame (R, Slot_Of (N), Shape (N, T));

            when N_Call =>
               Invoke (N, R, Want_Result => True);

            when N_Unary =>
               case Rec.Op is
                  when P_Minus =>
                     Value (Rec.A, R);
                     M.Unary (Neg, R, R);
                     M.Normalize (R, Shape (N, T));
                  when P_Plus =>
                     Value (Rec.A, R);
                  when P_Bang =>
                     Value (Rec.A, R);
                     if Kind (T) = Ty_Verdict then
                        --  극성 반전: Pass(1) ↔ Fail
                        Check_Temp (N, R + 1);
                        M.Load_Immediate (R + 1, 1);
                        M.Compare_And_Set (R, R, R + 1, Ne);
                     else
                        M.Unary (Bit_Not, R, R);
                        M.Normalize (R, Shape (N, T));
                     end if;
                  when P_Star =>
                     Value (Rec.A, R);
                     M.Load_Indirect (R, R, Shape (N, T));
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
                     declare
                        Fail_L : constant Label := M.New_Label;
                        Done_L : constant Label := M.New_Label;
                     begin
                        Branch (N, Fail_L, When_Pass => False, R => R);
                        M.Load_Immediate (R, 1);
                        M.Jump (Done_L);
                        M.Place (Fail_L);
                        M.Load_Immediate (R, 0);
                        M.Place (Done_L);
                     end;
                  when K_Xor =>
                     --  두 피연산자 모두 평가하고 성공 여부를 비교
                     Check_Temp (N, R + 2);
                     Value (Rec.A, R);
                     M.Load_Immediate (R + 1, 1);
                     M.Compare_And_Set (R, R, R + 1, Eq);
                     Value (Rec.B, R + 1);
                     M.Load_Immediate (R + 2, 1);
                     M.Compare_And_Set (R + 1, R + 1, R + 2, Eq);
                     M.Arith (Bit_Xor, R, R, R + 1, (1, False));
                  when others =>
                     Value (Rec.A, R);
                     Check_Temp (N, R + 1);
                     Value (Rec.B, R + 1);
                     M.Arith (Arith_Of (Rec.Op), R, R, R + 1, Shape (N, T));
                     M.Normalize (R, Shape (N, T));
               end case;

            when N_Cast =>
               Value (Rec.A, R);
               if Is_Int (T) then
                  M.Normalize (R, Shape (N, T));
               end if;

            when N_Field =>
               if Idents.Image (Rec.Name) = "len" then
                  M.Load_Immediate
                    (R, Interfaces.Unsigned_64
                          (Types.Get
                             (if Kind (Type_Of (Rec.A)) = Ty_Ref
                              then Types.Get (Type_Of (Rec.A)).Target
                              else Type_Of (Rec.A)).Length));
               elsif Kind (Type_Of (Rec.A)) = Ty_Ref then
                  --  참조를 거친 투영: 배열의 주소가 곧 첫 원소의 주소
                  Value (Rec.A, R);
               else
                  Address (Rec.A, R);
               end if;

            when N_If =>
               declare
                  Else_L : constant Label := M.New_Label;
                  Done_L : constant Label := M.New_Label;
               begin
                  Branch (Rec.A, Else_L, When_Pass => False, R => R);
                  Value (Rec.B, R);
                  M.Jump (Done_L);
                  M.Place (Else_L);
                  Value (Rec.C, R);
                  M.Place (Done_L);
               end;

            when N_Return | N_Break | N_Continue =>
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
           and then Kind (Type_Of (N)) = Ty_Verdict
         then
            Branch (Rec.A, Target, not When_Pass, R);
         else
            --  Pass는 판별자 값 1 (§5.6)
            Value (N, R);
            M.Test_And_Branch (R, 1, Equal => When_Pass, Target => Target);
         end if;
      end Branch;

      procedure Assign (N : Node_Id) is
         Rec   : constant Node := Get (N);
         Place : constant Node := Get (Rec.A);
         S     : constant Scalar := Shape (Rec.A, Type_Of (Rec.A));
      begin
         if Place.Kind = N_Name then
            if Rec.Op = P_Eq then
               Value (Rec.B, 0);
            else
               M.Load_Frame (0, Slot_Of (Rec.A), S);
               Value (Rec.B, 1);
               M.Arith (Arith_Of (Rec.Op), 0, 0, 1, S);
               M.Normalize (0, S);
            end if;
            M.Store_Frame (0, Slot_Of (Rec.A), S);
         else
            --  객체를 먼저 정하고, 오른쪽을 평가하고, 저장한다 (§6.8.1)
            Value (Place.A, 0);
            if Rec.Op = P_Eq then
               Value (Rec.B, 1);
            else
               M.Load_Indirect (1, 0, S);
               Check_Temp (N, 2);
               Value (Rec.B, 2);
               M.Arith (Arith_Of (Rec.Op), 1, 1, 2, S);
               M.Normalize (1, S);
            end if;
            M.Store_Indirect (1, 0, S);
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
                  begin
                     if Kind (Item_N) = N_Let then
                        Value (Get (Item_N).B, 0);
                        M.Store_Frame
                          (0, Slot_Of (Item_N),
                           Shape (Item_N, Type_Of (Item_N)));
                     else
                        Effect (Item_N);
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
                  Value (Rec.A, 0);
                  M.Move_To_Result (0);
               end if;
               M.Jump_To_Return;

            when N_Int_Lit | N_Char_Lit | N_String_Lit | N_Name =>
               null;

            when others =>
               Value (N, 0);
         end case;
      end Effect;

      procedure Function_Body (N : Node_Id) is
         Rec    : constant Node := Get (N);
         Sym    : Symbol := Symbols.Get (Symbol_Id (Rec.Sym));
         Count  : constant Natural := Rec.List.Count;
         Args   : Calling.Arg_Array (1 .. Count);
         Locs   : Calling.Location_Array (1 .. Count);
         Stack  : Natural;
      begin
         if Length (Sym.Link_Name) = 0 then
            --  외부 이름이 없는 정의의 이름은 구현 정의 (§4.2.2)
            Sym.Link_Name := To_Unbounded_String
              ("kf_" & Idents.Image (Rec.Name));
            Symbols.Table.Replace_Element (Positive (Rec.Sym), Sym);
         end if;

         Frame_Top := 0;
         for I in 1 .. Count loop
            declare
               P : constant Node_Id := Item (Rec.List, I);
            begin
               Allocate (Get (P).Sym, Type_Of (P));
               Args (I) := (Shape (P, Type_Of (P)).Size, False);
            end;
         end loop;
         Allocate_Lets (Rec.B);
         Convention.Lay_Out (Args, Locs, Stack);

         M.Begin_Function
           (Link_Symbol (Symbol_Id (Rec.Sym)),
            Global     => Rec.Flags (F_Extern) or else Rec.Flags (F_Pub),
            Frame_Size => KSA.Round_Up (Frame_Top, 16));
         for I in 1 .. Count loop
            declare
               P : constant Node_Id := Item (Rec.List, I);
               S : constant Scalar := Shape (P, Type_Of (P));
            begin
               case Locs (I).Kind is
                  when Calling.In_Register =>
                     M.Store_Incoming (Locs (I).Index, Slot_Of (P), S);
                  when Calling.On_Stack =>
                     M.Load_Incoming (0, Locs (I).Offset, S);
                     M.Store_Frame (0, Slot_Of (P), S);
               end case;
            end;
         end loop;
         Effect (Rec.B);
         M.End_Function;
      end Function_Body;

      U : constant Node := Get (Unit);
   begin
      Listing.Clear;
      Data.Clear;
      Listing.Put_Line (if Mach_O then MachO.Text_Section
                        else ELF.Text_Section);
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) = N_Fn then
            Function_Body (Item (U.List, I));
         end if;
      end loop;

      if not Data.Is_Empty then
         Listing.Put_Line (if Mach_O then MachO.Const_Section
                           else ELF.Const_Section);
         for D of Data loop
            Listing.Put_Line (To_String (D.Label) & ":");
            if Length (D.Bytes) > 0 then
               declare
                  Line : Unbounded_String;
               begin
                  for C of To_String (D.Bytes) loop
                     Append (Line, (if Length (Line) = 0 then "" else ", ")
                             & Img (Character'Pos (C)));
                  end loop;
                  Listing.Instr (".byte " & To_String (Line));
               end;
            end if;
         end loop;
      end if;
      return Listing.Contents;
   exception
      when Stop =>
         return "";
   end Generate;

end Emit;
