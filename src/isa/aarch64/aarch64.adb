with Ada.Strings.Fixed;
with ELF;
with Listing;
with MachO;

package body AArch64 is

   use Interfaces;
   use Targets;

   function Img (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   function X (R : Temp) return String is ("x" & Img (9 + Integer (R)));
   function W (R : Temp) return String is ("w" & Img (9 + Integer (R)));

   procedure I (S : String) renames Listing.Instr;

   function Label_Name (M : Machine; L : Label) return String is
     (if M.Fmt = Format_MachO then MachO.Local_Label ("k" & Img (Integer (L)))
      else ELF.Local_Label ("k" & Img (Integer (L))));

   function Create (Format : Targets.Format_Kind) return Machine is
   begin
      return M : Machine do
         M.Fmt := Format;
      end return;
   end Create;

   overriding function Format (M : Machine) return Targets.Format_Kind is
     (M.Fmt);

   --  x16 ← x29 - Offset
   procedure Frame_Pointer_Minus (Offset : Natural) is
   begin
      if Offset < 4096 then
         I ("sub x16, x29, #" & Img (Offset));
      else
         I ("mov x16, #" & Img (Offset mod 65536));
         if Offset >= 65536 then
            I ("movk x16, #" & Img (Offset / 65536) & ", lsl #16");
         end if;
         I ("sub x16, x29, x16");
      end if;
   end Frame_Pointer_Minus;

   overriding procedure Begin_Function
     (M : in out Machine; Symbol : String; Global : Boolean;
      Frame_Size : Natural)
   is
   begin
      M.Return_Label := M.New_Label;
      if Global then
         Listing.Put_Line (".globl " & Symbol);
      end if;
      Listing.Put_Line (".p2align 2");
      Listing.Put_Line (Symbol & ":");
      I ("stp x29, x30, [sp, #-16]!");
      I ("mov x29, sp");
      if Frame_Size > 0 then
         if Frame_Size < 4096 then
            I ("sub sp, sp, #" & Img (Frame_Size));
         else
            Frame_Pointer_Minus (Frame_Size);
            I ("mov sp, x16");
         end if;
      end if;
   end Begin_Function;

   overriding procedure End_Function (M : in out Machine) is
   begin
      M.Place (M.Return_Label);
      I ("mov sp, x29");
      I ("ldp x29, x30, [sp], #16");
      I ("ret");
      Listing.Put_Line ("");
   end End_Function;

   overriding procedure Jump_To_Return (M : in out Machine) is
   begin
      M.Jump (M.Return_Label);
   end Jump_To_Return;

   overriding function New_Label (M : in out Machine) return Label is
   begin
      M.Next_Label := M.Next_Label + 1;
      return Label (M.Next_Label - 1);
   end New_Label;

   overriding procedure Place (M : in out Machine; L : Label) is
   begin
      Listing.Put_Line (Label_Name (M, L) & ":");
   end Place;

   overriding procedure Jump (M : in out Machine; L : Label) is
   begin
      I ("b " & Label_Name (M, L));
   end Jump;

   overriding procedure Load_Immediate
     (M : in out Machine; Dst : Temp; Value : Interfaces.Unsigned_64)
   is
      pragma Unreferenced (M);
      First : Boolean := True;
   begin
      if Value < 65536 then
         I ("mov " & X (Dst) & ", #" & Img (Integer (Value)));
         return;
      end if;
      for Chunk in 0 .. 3 loop
         declare
            Part : constant Unsigned_64 :=
              Shift_Right (Value, 16 * Chunk) and 16#FFFF#;
         begin
            if Part /= 0 then
               I ((if First then "movz " else "movk ") & X (Dst) & ", #"
                  & Img (Integer (Part)) & ", lsl #" & Img (16 * Chunk));
               First := False;
            end if;
         end;
      end loop;
   end Load_Immediate;

   overriding procedure Move (M : in out Machine; Dst, Src : Temp) is
      pragma Unreferenced (M);
   begin
      if Dst /= Src then
         I ("mov " & X (Dst) & ", " & X (Src));
      end if;
   end Move;

   --  크기와 부호에 맞는 적재 명령과 대상 레지스터 이름
   function Load_Op (Ty : Scalar; Unscaled : Boolean) return String is
      U : constant String := (if Unscaled then "ldur" else "ldr");
   begin
      case Ty.Size is
         when 1 => return U & (if Ty.Signed then "sb" else "b");
         when 2 => return U & (if Ty.Signed then "sh" else "h");
         when 4 => return U & (if Ty.Signed then "sw" else "");
         when others => return U;
      end case;
   end Load_Op;

   function Load_Reg (Ty : Scalar; Reg : Natural) return String is
     ((if Ty.Size < 8 and then not Ty.Signed then "w" else "x") & Img (Reg));

   function Store_Op (Ty : Scalar; Unscaled : Boolean) return String is
      U : constant String := (if Unscaled then "stur" else "str");
   begin
      case Ty.Size is
         when 1 => return U & "b";
         when 2 => return U & "h";
         when others => return U;
      end case;
   end Store_Op;

   function Store_Reg (Ty : Scalar; Reg : Natural) return String is
     ((if Ty.Size < 8 then "w" else "x") & Img (Reg));

   --  물리 레지스터 Reg와 프레임 슬롯 사이의 적재·저장
   procedure Frame_Access
     (Reg : Natural; Offset : Natural; Ty : Scalar; Store : Boolean)
   is
      Op  : constant String :=
        (if Store then Store_Op (Ty, Offset <= 256)
         else Load_Op (Ty, Offset <= 256));
      Rn  : constant String :=
        (if Store then Store_Reg (Ty, Reg) else Load_Reg (Ty, Reg));
   begin
      if Offset <= 256 then
         I (Op & " " & Rn & ", [x29, #-" & Img (Offset) & "]");
      else
         Frame_Pointer_Minus (Offset);
         I (Op & " " & Rn & ", [x16]");
      end if;
   end Frame_Access;

   overriding procedure Load_Frame
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      Frame_Access (9 + Natural (Dst), Offset, Ty, Store => False);
   end Load_Frame;

   overriding procedure Store_Frame
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      Frame_Access (9 + Natural (Src), Offset, Ty, Store => True);
   end Store_Frame;

   overriding procedure Frame_Address
     (M : in out Machine; Dst : Temp; Offset : Natural)
   is
      pragma Unreferenced (M);
   begin
      Frame_Pointer_Minus (Offset);
      I ("mov " & X (Dst) & ", x16");
   end Frame_Address;

   overriding procedure Load_Indirect
     (M : in out Machine; Dst, Addr : Temp; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      I (Load_Op (Ty, False) & " " & Load_Reg (Ty, 9 + Natural (Dst))
         & ", [" & X (Addr) & "]");
   end Load_Indirect;

   overriding procedure Store_Indirect
     (M : in out Machine; Src, Addr : Temp; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      I (Store_Op (Ty, False) & " " & Store_Reg (Ty, 9 + Natural (Src))
         & ", [" & X (Addr) & "]");
   end Store_Indirect;

   overriding procedure Data_Address
     (M : in out Machine; Dst : Temp; Symbol : String)
   is
   begin
      if M.Fmt = Format_MachO then
         I ("adrp " & X (Dst) & ", " & Symbol & "@PAGE");
         I ("add " & X (Dst) & ", " & X (Dst) & ", " & Symbol & "@PAGEOFF");
      else
         I ("adrp " & X (Dst) & ", " & Symbol);
         I ("add " & X (Dst) & ", " & X (Dst) & ", :lo12:" & Symbol);
      end if;
   end Data_Address;

   overriding procedure Arith
     (M : in out Machine; Op : Arith_Op; Dst, Left, Right : Temp;
      Ty : Scalar)
   is
      pragma Unreferenced (M);
      Operands : constant String :=
        X (Dst) & ", " & X (Left) & ", " & X (Right);
      Divide : constant String := (if Ty.Signed then "sdiv" else "udiv");
   begin
      case Op is
         when Add       => I ("add " & Operands);
         when Sub       => I ("sub " & Operands);
         when Mul       => I ("mul " & Operands);
         --  0으로 나누면 0, MIN / -1은 MIN: §6.5.1이 요구하는 결과를
         --  AArch64의 나눗셈이 그대로 낸다
         when Div       => I (Divide & " " & Operands);
         when Remainder =>
            I (Divide & " x16, " & X (Left) & ", " & X (Right));
            I ("msub " & X (Dst) & ", x16, " & X (Right) & ", " & X (Left));
         when Bit_And   => I ("and " & Operands);
         when Bit_Or    => I ("orr " & Operands);
         when Bit_Xor   => I ("eor " & Operands);
      end case;
   end Arith;

   overriding procedure Unary
     (M : in out Machine; Op : Unary_Op; Dst, Src : Temp)
   is
      pragma Unreferenced (M);
   begin
      case Op is
         when Neg     => I ("neg " & X (Dst) & ", " & X (Src));
         when Bit_Not => I ("mvn " & X (Dst) & ", " & X (Src));
      end case;
   end Unary;

   overriding procedure Normalize
     (M : in out Machine; R : Temp; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      case Ty.Size is
         when 1 =>
            I (if Ty.Signed then "sxtb " & X (R) & ", " & W (R)
               else "and " & X (R) & ", " & X (R) & ", #0xff");
         when 2 =>
            I (if Ty.Signed then "sxth " & X (R) & ", " & W (R)
               else "and " & X (R) & ", " & X (R) & ", #0xffff");
         when 4 =>
            I (if Ty.Signed then "sxtw " & X (R) & ", " & W (R)
               else "mov " & W (R) & ", " & W (R));
         when others =>
            null;
      end case;
   end Normalize;

   function Cond_Name (C : Condition) return String is
     (case C is
        when Eq => "eq", when Ne => "ne", when Lt => "lt", when Le => "le",
        when Gt => "gt", when Ge => "ge", when Lo => "lo", when Ls => "ls",
        when Hi => "hi", when Hs => "hs");

   overriding procedure Compare_And_Set
     (M : in out Machine; Dst, Left, Right : Temp; C : Condition)
   is
      pragma Unreferenced (M);
   begin
      I ("cmp " & X (Left) & ", " & X (Right));
      I ("cset " & X (Dst) & ", " & Cond_Name (C));
   end Compare_And_Set;

   overriding procedure Compare_And_Branch
     (M : in out Machine; Left, Right : Temp; C : Condition;
      Target : Label)
   is
   begin
      I ("cmp " & X (Left) & ", " & X (Right));
      I ("b." & Cond_Name (C) & " " & Label_Name (M, Target));
   end Compare_And_Branch;

   overriding procedure Test_And_Branch
     (M : in out Machine; R : Temp; Value : Natural; Equal : Boolean;
      Target : Label)
   is
   begin
      I ("cmp " & X (R) & ", #" & Img (Value));
      I ((if Equal then "b.eq " else "b.ne ") & Label_Name (M, Target));
   end Test_And_Branch;

   overriding procedure Save_Temp (M : in out Machine; R : Temp) is
      pragma Unreferenced (M);
   begin
      I ("str " & X (R) & ", [sp, #-16]!");
   end Save_Temp;

   overriding procedure Restore_Temp (M : in out Machine; R : Temp) is
      pragma Unreferenced (M);
   begin
      I ("ldr " & X (R) & ", [sp], #16");
   end Restore_Temp;

   overriding procedure Reserve_Outgoing (M : in out Machine; Size : Natural)
   is
      pragma Unreferenced (M);
   begin
      if Size > 0 then
         I ("sub sp, sp, #" & Img (Size));
      end if;
   end Reserve_Outgoing;

   overriding procedure Release_Outgoing (M : in out Machine; Size : Natural)
   is
      pragma Unreferenced (M);
   begin
      if Size > 0 then
         I ("add sp, sp, #" & Img (Size));
      end if;
   end Release_Outgoing;

   overriding procedure Store_Outgoing
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      I (Store_Op (Ty, False) & " " & Store_Reg (Ty, 9 + Natural (Src))
         & ", [sp, #" & Img (Offset) & "]");
   end Store_Outgoing;

   overriding procedure Move_To_Argument
     (M : in out Machine; Index : Natural; Src : Temp)
   is
      pragma Unreferenced (M);
   begin
      I ("mov x" & Img (Index) & ", " & X (Src));
   end Move_To_Argument;

   overriding procedure Call (M : in out Machine; Symbol : String) is
      pragma Unreferenced (M);
   begin
      I ("bl " & Symbol);
   end Call;

   overriding procedure Move_From_Result (M : in out Machine; Dst : Temp) is
      pragma Unreferenced (M);
   begin
      I ("mov " & X (Dst) & ", x0");
   end Move_From_Result;

   overriding procedure Move_To_Result (M : in out Machine; Src : Temp) is
      pragma Unreferenced (M);
   begin
      I ("mov x0, " & X (Src));
   end Move_To_Result;

   overriding procedure Store_Incoming
     (M : in out Machine; Index : Natural; Offset : Natural; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      Frame_Access (Index, Offset, Ty, Store => True);
   end Store_Incoming;

   overriding procedure Load_Incoming
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar)
   is
      pragma Unreferenced (M);
   begin
      --  호출자의 스택 인자는 저장된 x29, x30 바로 위에 있다
      I (Load_Op (Ty, False) & " " & Load_Reg (Ty, 9 + Natural (Dst))
         & ", [x29, #" & Img (16 + Offset) & "]");
   end Load_Incoming;

end AArch64;
