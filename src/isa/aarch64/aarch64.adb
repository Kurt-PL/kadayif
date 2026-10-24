with Ada.Containers.Ordered_Maps;
with Ada.Strings.Fixed;
with AArch64.Encode;
with ELF;
with Listing;
with MachO;

package body AArch64 is

   use Ada.Strings.Unbounded;
   use Interfaces;
   use Targets;
   use type Sections.Section_Kind;

   package E renames AArch64.Encode;

   subtype Word is E.Word;
   subtype Reg is E.Reg;

   Scratch : constant Reg := 16;
   FP      : constant Reg := 29;
   LR      : constant Reg := 30;
   SP      : constant Reg := E.SP_Or_ZR;
   ZR      : constant Reg := E.SP_Or_ZR;

   function Img (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   function Phys (T : Temp) return Reg is (9 + Reg (T));
   function X (N : Reg) return String is ("x" & Img (N));
   function W (N : Reg) return String is ("w" & Img (N));
   function X (T : Temp) return String is (X (Phys (T)));

   function Label_Name (M : Machine; L : Label) return String is
     (if M.Fmt = Format_MachO then MachO.Local_Label ("k" & Img (Integer (L)))
      else ELF.Local_Label ("k" & Img (Integer (L))));

   procedure Put
     (M      : in out Machine;
      Text   : String;
      Code   : Word := 0;
      Kind   : Entry_Kind := Plain;
      Target : Label := 1;
      Symbol : String := "";
      Global : Boolean := False) is
   begin
      M.Entries.Append
        (Entry_Rec'(Kind, To_Unbounded_String (Text), Code, Target,
                    To_Unbounded_String (Symbol), Global));
   end Put;

   function Create (Format : Targets.Format_Kind) return Machine is
   begin
      return M : Machine do
         M.Fmt := Format;
      end return;
   end Create;

   overriding function Format (M : Machine) return Targets.Format_Kind is
     (M.Fmt);

   --  x16 ← x29 - Offset
   procedure Frame_Pointer_Minus (M : in out Machine; Offset : Natural) is
   begin
      if Offset < 4096 then
         Put (M, "sub x16, x29, #" & Img (Offset),
              E.Sub_Imm (Scratch, FP, Offset));
      else
         Put (M, "mov x16, #" & Img (Offset mod 65536),
              E.Movz (Scratch, Offset mod 65536, 0));
         if Offset >= 65536 then
            Put (M, "movk x16, #" & Img (Offset / 65536) & ", lsl #16",
                 E.Movk (Scratch, Offset / 65536, 16));
         end if;
         Put (M, "sub x16, x29, x16",
              E.Reg_Reg (E.Op_Sub, Scratch, FP, Scratch));
      end if;
   end Frame_Pointer_Minus;

   overriding procedure Begin_Function
     (M : in out Machine; Symbol : String; Global : Boolean;
      Frame_Size : Natural)
   is
   begin
      M.Return_Label := M.New_Label;
      if Global then
         Put (M, ".globl " & Symbol, Kind => Directive);
      end if;
      Put (M, ".p2align 2", Kind => Directive);
      Put (M, Symbol & ":", Kind => Define_Symbol, Symbol => Symbol,
           Global => Global);
      Put (M, "stp x29, x30, [sp, #-16]!", E.Stp_Pre (FP, LR, SP, -16));
      Put (M, "mov x29, sp", E.Add_Imm (FP, SP, 0));
      if Frame_Size > 0 then
         if Frame_Size < 4096 then
            Put (M, "sub sp, sp, #" & Img (Frame_Size),
                 E.Sub_Imm (SP, SP, Frame_Size));
         else
            Frame_Pointer_Minus (M, Frame_Size);
            Put (M, "mov sp, x16", E.Add_Imm (SP, Scratch, 0));
         end if;
      end if;
   end Begin_Function;

   overriding procedure End_Function (M : in out Machine) is
   begin
      M.Place (M.Return_Label);
      Put (M, "mov sp, x29", E.Add_Imm (SP, FP, 0));
      Put (M, "ldp x29, x30, [sp], #16", E.Ldp_Post (FP, LR, SP, 16));
      Put (M, "ret", E.Ret);
      Put (M, "", Kind => Directive);
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
      Put (M, Label_Name (M, L) & ":", Kind => Define_Label, Target => L);
   end Place;

   overriding procedure Jump (M : in out Machine; L : Label) is
   begin
      Put (M, "b " & Label_Name (M, L), E.B (0), Label_Branch, L);
   end Jump;

   overriding procedure Load_Immediate
     (M : in out Machine; Dst : Temp; Value : Interfaces.Unsigned_64)
   is
      First : Boolean := True;
   begin
      if Value < 65536 then
         Put (M, "mov " & X (Dst) & ", #" & Img (Integer (Value)),
              E.Movz (Phys (Dst), Natural (Value), 0));
         return;
      end if;
      for Chunk in 0 .. 3 loop
         declare
            Part : constant Natural := Natural
              (Shift_Right (Value, 16 * Chunk) and 16#FFFF#);
         begin
            if Part /= 0 then
               Put (M, (if First then "movz " else "movk ") & X (Dst) & ", #"
                    & Img (Part) & ", lsl #" & Img (16 * Chunk),
                    (if First then E.Movz (Phys (Dst), Part, 16 * Chunk)
                     else E.Movk (Phys (Dst), Part, 16 * Chunk)));
               First := False;
            end if;
         end;
      end loop;
   end Load_Immediate;

   overriding procedure Move (M : in out Machine; Dst, Src : Temp) is
   begin
      if Dst /= Src then
         Put (M, "mov " & X (Dst) & ", " & X (Src),
              E.Reg_Reg (E.Op_Orr, Phys (Dst), ZR, Phys (Src)));
      end if;
   end Move;

   ---------------------------------------------------------------------
   --  적재와 저장

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

   --  부호 없는 좁은 적재는 w 레지스터로(상위 비트가 0이 된다)
   function Load_Reg (Ty : Scalar; N : Reg) return String is
     (if Ty.Size < 8 and then not Ty.Signed then W (N) else X (N));

   function Store_Op (Ty : Scalar; Unscaled : Boolean) return String is
      U : constant String := (if Unscaled then "stur" else "str");
   begin
      case Ty.Size is
         when 1 => return U & "b";
         when 2 => return U & "h";
         when others => return U;
      end case;
   end Store_Op;

   function Store_Reg (Ty : Scalar; N : Reg) return String is
     (if Ty.Size < 8 then W (N) else X (N));

   function Data_Reg (Ty : Scalar; N : Reg; Store : Boolean) return String is
     (if Store then Store_Reg (Ty, N) else Load_Reg (Ty, N));

   --  [Base, #Offset] (부호 없는 배율 오프셋)
   procedure Access_Unsigned
     (M : in out Machine; N : Reg; Base : Reg; Offset : Natural;
      Ty : Scalar; Store : Boolean)
   is
      Base_Name : constant String := (if Base = SP then "sp" else X (Base));
   begin
      Put (M,
           (if Store then Store_Op (Ty, False) else Load_Op (Ty, False))
           & " " & Data_Reg (Ty, N, Store) & ", [" & Base_Name
           & (if Offset = 0 then "]" else ", #" & Img (Offset) & "]"),
           E.Load_Store_Unsigned (Store, Ty.Size, Ty.Signed, N, Base,
                                  Offset));
   end Access_Unsigned;

   --  물리 레지스터 N과 프레임 슬롯 사이의 적재·저장
   procedure Frame_Access
     (M : in out Machine; N : Reg; Offset : Natural; Ty : Scalar;
      Store : Boolean)
   is
   begin
      if Offset <= 256 then
         Put (M,
              (if Store then Store_Op (Ty, True) else Load_Op (Ty, True))
              & " " & Data_Reg (Ty, N, Store) & ", [x29, #-"
              & Img (Offset) & "]",
              E.Load_Store_Unscaled (Store, Ty.Size, Ty.Signed, N, FP,
                                     -Offset));
      else
         Frame_Pointer_Minus (M, Offset);
         Access_Unsigned (M, N, Scratch, 0, Ty, Store);
      end if;
   end Frame_Access;

   overriding procedure Load_Frame
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar) is
   begin
      Frame_Access (M, Phys (Dst), Offset, Ty, Store => False);
   end Load_Frame;

   overriding procedure Store_Frame
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar) is
   begin
      Frame_Access (M, Phys (Src), Offset, Ty, Store => True);
   end Store_Frame;

   overriding procedure Frame_Address
     (M : in out Machine; Dst : Temp; Offset : Natural) is
   begin
      Frame_Pointer_Minus (M, Offset);
      Put (M, "mov " & X (Dst) & ", x16",
           E.Reg_Reg (E.Op_Orr, Phys (Dst), ZR, Scratch));
   end Frame_Address;

   --  x16 ← Base + Value
   procedure Base_Plus (M : in out Machine; Base : Reg; Value : Natural) is
      Base_Name : constant String := (if Base = SP then "sp" else X (Base));
   begin
      if Value < 4096 then
         Put (M, "add x16, " & Base_Name & ", #" & Img (Value),
              E.Add_Imm (Scratch, Base, Value));
      else
         Put (M, "mov x16, #" & Img (Value mod 65536),
              E.Movz (Scratch, Value mod 65536, 0));
         if Value >= 65536 then
            Put (M, "movk x16, #" & Img (Value / 65536) & ", lsl #16",
                 E.Movk (Scratch, Value / 65536, 16));
         end if;
         Put (M, "add x16, " & Base_Name & ", x16",
              E.Reg_Reg (E.Op_Add, Scratch, Base, Scratch));
      end if;
   end Base_Plus;

   --  물리 레지스터 N과 [Base + Offset] 사이의 적재·저장
   procedure Access_At
     (M : in out Machine; N : Reg; Base : Reg; Offset : Natural;
      Ty : Scalar; Store : Boolean)
   is
      Base_Name : constant String := (if Base = SP then "sp" else X (Base));
   begin
      if Offset mod Ty.Size = 0 and then Offset / Ty.Size <= 4095 then
         Access_Unsigned (M, N, Base, Offset, Ty, Store);
      elsif Offset <= 255 then
         Put (M,
              (if Store then Store_Op (Ty, True) else Load_Op (Ty, True))
              & " " & Data_Reg (Ty, N, Store) & ", [" & Base_Name & ", #"
              & Img (Offset) & "]",
              E.Load_Store_Unscaled (Store, Ty.Size, Ty.Signed, N, Base,
                                     Offset));
      else
         Base_Plus (M, Base, Offset);
         Access_Unsigned (M, N, Scratch, 0, Ty, Store);
      end if;
   end Access_At;

   overriding procedure Load_Field
     (M : in out Machine; Dst, Addr : Temp; Offset : Natural; Ty : Scalar)
   is
   begin
      Access_At (M, Phys (Dst), Phys (Addr), Offset, Ty, Store => False);
   end Load_Field;

   overriding procedure Store_Field
     (M : in out Machine; Src, Addr : Temp; Offset : Natural; Ty : Scalar)
   is
   begin
      Access_At (M, Phys (Src), Phys (Addr), Offset, Ty, Store => True);
   end Store_Field;

   --  Size바이트를 1, 2, 4, 8바이트 조각으로: 낮은 주소부터
   function Piece (Remaining : Positive) return Positive is
     (if Remaining >= 8 then 8 elsif Remaining >= 4 then 4
      elsif Remaining >= 2 then 2 else 1);

   overriding procedure Load_Bytes
     (M : in out Machine; Dst, Addr : Temp; Offset : Natural;
      Size : Positive)
   is
      Done : Natural := 0;
   begin
      while Done < Size loop
         declare
            P : constant Positive := Piece (Size - Done);
         begin
            if Done = 0 then
               Access_At (M, Phys (Dst), Phys (Addr), Offset, (P, False),
                          Store => False);
            else
               Access_At (M, 17, Phys (Addr), Offset + Done, (P, False),
                          Store => False);
               Put (M, "orr " & X (Dst) & ", " & X (Dst) & ", x17, lsl #"
                    & Img (8 * Done),
                    E.Orr_Shifted (Phys (Dst), Phys (Dst), 17, 8 * Done));
            end if;
            Done := Done + P;
         end;
      end loop;
   end Load_Bytes;

   overriding procedure Store_Bytes
     (M : in out Machine; Src, Addr : Temp; Offset : Natural;
      Size : Positive)
   is
      Done : Natural := 0;
   begin
      while Done < Size loop
         declare
            P : constant Positive := Piece (Size - Done);
         begin
            if Done = 0 then
               Access_At (M, Phys (Src), Phys (Addr), Offset, (P, False),
                          Store => True);
            else
               Put (M, "lsr x17, " & X (Src) & ", #" & Img (8 * Done),
                    E.Lsr_Imm (17, Phys (Src), 8 * Done));
               Access_At (M, 17, Phys (Addr), Offset + Done, (P, False),
                          Store => True);
            end if;
            Done := Done + P;
         end;
      end loop;
   end Store_Bytes;

   overriding procedure Copy_Memory
     (M : in out Machine; Dst, Src : Temp; Size : Natural)
   is
      Done : Natural := 0;
   begin
      while Done < Size loop
         declare
            P : constant Positive := Piece (Size - Done);
         begin
            Access_At (M, 17, Phys (Src), Done, (P, False), Store => False);
            Access_At (M, 17, Phys (Dst), Done, (P, False), Store => True);
            Done := Done + P;
         end;
      end loop;
   end Copy_Memory;

   overriding procedure Zero_Memory
     (M : in out Machine; Dst : Temp; Size : Natural)
   is
      Done : Natural := 0;
   begin
      while Done < Size loop
         declare
            P : constant Positive := Piece (Size - Done);
         begin
            Access_At (M, ZR, Phys (Dst), Done, (P, False), Store => True);
            Done := Done + P;
         end;
      end loop;
   end Zero_Memory;

   overriding procedure Add_Immediate
     (M : in out Machine; Dst, Src : Temp; Value : Natural) is
   begin
      if Value < 4096 then
         Put (M, "add " & X (Dst) & ", " & X (Src) & ", #" & Img (Value),
              E.Add_Imm (Phys (Dst), Phys (Src), Value));
      else
         Base_Plus (M, Phys (Src), Value);
         Put (M, "mov " & X (Dst) & ", x16",
              E.Reg_Reg (E.Op_Orr, Phys (Dst), ZR, Scratch));
      end if;
   end Add_Immediate;

   overriding procedure Data_Address
     (M : in out Machine; Dst : Temp; Symbol : String) is
   begin
      if M.Fmt = Format_MachO then
         Put (M, "adrp " & X (Dst) & ", " & Symbol & "@PAGE",
              E.Adrp (Phys (Dst)), Symbol_Page, Symbol => Symbol);
         Put (M, "add " & X (Dst) & ", " & X (Dst) & ", " & Symbol
              & "@PAGEOFF",
              E.Add_Imm (Phys (Dst), Phys (Dst), 0), Symbol_Offset,
              Symbol => Symbol);
      else
         Put (M, "adrp " & X (Dst) & ", " & Symbol,
              E.Adrp (Phys (Dst)), Symbol_Page, Symbol => Symbol);
         Put (M, "add " & X (Dst) & ", " & X (Dst) & ", :lo12:" & Symbol,
              E.Add_Imm (Phys (Dst), Phys (Dst), 0), Symbol_Offset,
              Symbol => Symbol);
      end if;
   end Data_Address;

   ---------------------------------------------------------------------
   --  연산

   overriding procedure Arith
     (M : in out Machine; Op : Arith_Op; Dst, Left, Right : Temp;
      Ty : Scalar)
   is
      Operands : constant String :=
        X (Dst) & ", " & X (Left) & ", " & X (Right);
      Divide   : constant String := (if Ty.Signed then "sdiv" else "udiv");

      procedure Rr (Name : String; Op : E.Reg_Op) is
      begin
         Put (M, Name & " " & Operands,
              E.Reg_Reg (Op, Phys (Dst), Phys (Left), Phys (Right)));
      end Rr;

   begin
      case Op is
         when Add => Rr ("add", E.Op_Add);
         when Sub => Rr ("sub", E.Op_Sub);
         when Mul =>
            Put (M, "mul " & Operands,
                 E.Madd (Phys (Dst), Phys (Left), Phys (Right), ZR));
         --  0으로 나누면 0, MIN / -1은 MIN: §6.5.1이 요구하는 결과를
         --  AArch64의 나눗셈이 그대로 낸다
         when Div =>
            Put (M, Divide & " " & Operands,
                 E.Div (Phys (Dst), Phys (Left), Phys (Right), Ty.Signed));
         when Remainder =>
            Put (M, Divide & " x16, " & X (Left) & ", " & X (Right),
                 E.Div (Scratch, Phys (Left), Phys (Right), Ty.Signed));
            Put (M, "msub " & X (Dst) & ", x16, " & X (Right) & ", "
                 & X (Left),
                 E.Msub (Phys (Dst), Scratch, Phys (Right), Phys (Left)));
         when Bit_And => Rr ("and", E.Op_And);
         when Bit_Or  => Rr ("orr", E.Op_Orr);
         when Bit_Xor => Rr ("eor", E.Op_Eor);
      end case;
   end Arith;

   overriding procedure Unary
     (M : in out Machine; Op : Unary_Op; Dst, Src : Temp) is
   begin
      case Op is
         when Neg =>
            Put (M, "neg " & X (Dst) & ", " & X (Src),
                 E.Reg_Reg (E.Op_Sub, Phys (Dst), ZR, Phys (Src)));
         when Bit_Not =>
            Put (M, "mvn " & X (Dst) & ", " & X (Src),
                 E.Reg_Reg (E.Op_Orn, Phys (Dst), ZR, Phys (Src)));
      end case;
   end Unary;

   overriding procedure Normalize
     (M : in out Machine; R : Temp; Ty : Scalar)
   is
      N : constant Reg := Phys (R);
   begin
      case Ty.Size is
         when 1 | 2 =>
            if Ty.Signed then
               Put (M, (if Ty.Size = 1 then "sxtb " else "sxth ") & X (N)
                    & ", " & W (N), E.Sign_Extend (N, N, 8 * Ty.Size));
            else
               Put (M, "and " & X (N) & ", " & X (N) & ", #"
                    & (if Ty.Size = 1 then "0xff" else "0xffff"),
                    E.And_Low_Mask (N, N, 8 * Ty.Size));
            end if;
         when 4 =>
            if Ty.Signed then
               Put (M, "sxtw " & X (N) & ", " & W (N),
                    E.Sign_Extend (N, N, 32));
            else
               Put (M, "mov " & W (N) & ", " & W (N),
                    E.Reg_Reg (E.Op_Orr, N, ZR, N, Sf => False));
            end if;
         when others =>
            null;
      end case;
   end Normalize;

   function Cond_Name (C : Condition) return String is
     (case C is
        when Eq => "eq", when Ne => "ne", when Lt => "lt", when Le => "le",
        when Gt => "gt", when Ge => "ge", when Lo => "lo", when Ls => "ls",
        when Hi => "hi", when Hs => "hs");

   function Cond_Code (C : Condition) return Natural is
     (case C is
        when Eq => 0, when Ne => 1, when Hs => 2, when Lo => 3,
        when Hi => 8, when Ls => 9, when Ge => 10, when Lt => 11,
        when Gt => 12, when Le => 13);

   procedure Compare (M : in out Machine; Left, Right : Temp) is
   begin
      Put (M, "cmp " & X (Left) & ", " & X (Right),
           E.Reg_Reg (E.Op_Subs, ZR, Phys (Left), Phys (Right)));
   end Compare;

   procedure Branch_On (M : in out Machine; C : Condition; Target : Label) is
   begin
      Put (M, "b." & Cond_Name (C) & " " & Label_Name (M, Target),
           E.B_Cond (Cond_Code (C), 0), Label_Branch, Target);
   end Branch_On;

   overriding procedure Compare_And_Set
     (M : in out Machine; Dst, Left, Right : Temp; C : Condition) is
   begin
      Compare (M, Left, Right);
      Put (M, "cset " & X (Dst) & ", " & Cond_Name (C),
           E.Cset (Phys (Dst), Cond_Code (C)));
   end Compare_And_Set;

   overriding procedure Compare_And_Branch
     (M : in out Machine; Left, Right : Temp; C : Condition;
      Target : Label) is
   begin
      Compare (M, Left, Right);
      Branch_On (M, C, Target);
   end Compare_And_Branch;

   overriding procedure Test_And_Branch
     (M : in out Machine; R : Temp; Value : Natural; Equal : Boolean;
      Target : Label) is
   begin
      Put (M, "cmp " & X (R) & ", #" & Img (Value),
           E.Subs_Imm (ZR, Phys (R), Value));
      Branch_On (M, (if Equal then Eq else Ne), Target);
   end Test_And_Branch;

   ---------------------------------------------------------------------
   --  호출

   overriding procedure Save_Temp (M : in out Machine; R : Temp) is
   begin
      Put (M, "str " & X (R) & ", [sp, #-16]!", E.Str_Pre (Phys (R), SP, -16));
   end Save_Temp;

   overriding procedure Restore_Temp (M : in out Machine; R : Temp) is
   begin
      Put (M, "ldr " & X (R) & ", [sp], #16", E.Ldr_Post (Phys (R), SP, 16));
   end Restore_Temp;

   overriding procedure Reserve_Outgoing (M : in out Machine; Size : Natural)
   is
   begin
      if Size > 0 then
         Put (M, "sub sp, sp, #" & Img (Size), E.Sub_Imm (SP, SP, Size));
      end if;
   end Reserve_Outgoing;

   overriding procedure Release_Outgoing (M : in out Machine; Size : Natural)
   is
   begin
      if Size > 0 then
         Put (M, "add sp, sp, #" & Img (Size), E.Add_Imm (SP, SP, Size));
      end if;
   end Release_Outgoing;

   overriding procedure Store_Outgoing
     (M : in out Machine; Src : Temp; Offset : Natural; Ty : Scalar) is
   begin
      Access_Unsigned (M, Phys (Src), SP, Offset, Ty, Store => True);
   end Store_Outgoing;

   overriding procedure Move_To_Argument
     (M : in out Machine; Index : Natural; Src : Temp) is
   begin
      Put (M, "mov " & X (Reg (Index)) & ", " & X (Src),
           E.Reg_Reg (E.Op_Orr, Reg (Index), ZR, Phys (Src)));
   end Move_To_Argument;

   overriding procedure Load_Stack
     (M : in out Machine; Dst : Temp; Offset : Natural) is
   begin
      Access_Unsigned
        (M, Phys (Dst), SP, Offset, Instruction_Set.Word, Store => False);
   end Load_Stack;

   overriding procedure Move_From_Argument
     (M : in out Machine; Dst : Temp; Index : Natural) is
   begin
      Put (M, "mov " & X (Dst) & ", " & X (Reg (Index)),
           E.Reg_Reg (E.Op_Orr, Phys (Dst), ZR, Reg (Index)));
   end Move_From_Argument;

   overriding procedure Stack_Address
     (M : in out Machine; Dst : Temp; Offset : Natural) is
   begin
      Put (M, "add " & X (Dst) & ", sp, #" & Img (Offset),
           E.Add_Imm (Phys (Dst), SP, Offset));
   end Stack_Address;

   overriding procedure Incoming_Address
     (M : in out Machine; Dst : Temp; Offset : Natural) is
   begin
      Put (M, "add " & X (Dst) & ", x29, #" & Img (16 + Offset),
           E.Add_Imm (Phys (Dst), FP, 16 + Offset));
   end Incoming_Address;

   overriding procedure Call (M : in out Machine; Symbol : String) is
   begin
      Put (M, "bl " & Symbol, E.BL (0), Symbol_Call, Symbol => Symbol);
   end Call;

   overriding procedure Move_From_Result (M : in out Machine; Dst : Temp) is
   begin
      Put (M, "mov " & X (Dst) & ", x0",
           E.Reg_Reg (E.Op_Orr, Phys (Dst), ZR, 0));
   end Move_From_Result;

   overriding procedure Move_To_Result (M : in out Machine; Src : Temp) is
   begin
      Put (M, "mov x0, " & X (Src), E.Reg_Reg (E.Op_Orr, 0, ZR, Phys (Src)));
   end Move_To_Result;

   overriding procedure Store_Incoming
     (M : in out Machine; Index : Natural; Offset : Natural; Ty : Scalar) is
   begin
      Frame_Access (M, Reg (Index), Offset, Ty, Store => True);
   end Store_Incoming;

   overriding procedure Load_Incoming
     (M : in out Machine; Dst : Temp; Offset : Natural; Ty : Scalar) is
   begin
      --  호출자의 스택 인자는 저장된 x29, x30 바로 위에 있다
      Access_Unsigned (M, Phys (Dst), FP, 16 + Offset, Ty, Store => False);
   end Load_Incoming;

   ---------------------------------------------------------------------
   --  출력

   overriding procedure Write_Text (M : Machine) is
   begin
      for En of M.Entries loop
         case En.Kind is
            when Directive | Define_Label | Define_Symbol =>
               Listing.Put_Line (To_String (En.Text));
            when others =>
               Listing.Instr (To_String (En.Text));
         end case;
      end loop;
   end Write_Text;

   overriding procedure Write_Code
     (M : Machine; Obj : in out Sections.Object)
   is
      package Label_Maps is new Ada.Containers.Ordered_Maps (Label, Natural);
      Labels : Label_Maps.Map;
      Base   : constant Natural := Sections.Size (Obj, Sections.Text);
      Here   : Natural := Base;

      function Is_Code (K : Entry_Kind) return Boolean is
        (K not in Define_Label | Define_Symbol | Directive);

      procedure Relocate (Kind : Sections.Reloc_Kind; Name : String) is
      begin
         Obj.Relocs.Append
           (Sections.Relocation'
              (Sections.Text, Here, Kind, Sections.Lookup (Obj, Name)));
      end Relocate;

   begin
      --  1차: 레이블과 심볼의 위치
      for En of M.Entries loop
         case En.Kind is
            when Define_Label =>
               Labels.Include (En.Target, Here);
            when Define_Symbol =>
               Sections.Define
                 (Obj, To_String (En.Symbol), Sections.Text, Here, En.Global);
            when others =>
               if Is_Code (En.Kind) then
                  Here := Here + 4;
               end if;
         end case;
      end loop;

      --  2차: 기계어. 같은 섹션 안에서 정의된 대상은 바로 풀고,
      --  나머지는 재배치로 남긴다.
      Here := Base;
      for En of M.Entries loop
         if Is_Code (En.Kind) then
            declare
               Code : Word := En.Code;
               Name : constant String := To_String (En.Symbol);
            begin
               case En.Kind is
                  when Label_Branch =>
                     Code := E.Patch_Branch
                       (Code, (Labels (En.Target) - Here) / 4);
                  when Symbol_Call =>
                     declare
                        S : constant Sections.Symbol :=
                          Obj.Symbols (Sections.Lookup (Obj, Name));
                     begin
                        if S.Defined and then S.Section = Sections.Text then
                           Code := E.Patch_Branch
                             (Code, (S.Offset - Here) / 4);
                        else
                           Relocate (Sections.Branch26, Name);
                        end if;
                     end;
                  when Symbol_Page =>
                     Relocate (Sections.Page21, Name);
                  when Symbol_Offset =>
                     Relocate (Sections.Page_Off12, Name);
                  when others =>
                     null;
               end case;
               Sections.Append_Word (Obj, Sections.Text, Code);
               Here := Here + 4;
            end;
         end if;
      end loop;
   end Write_Code;

end AArch64;
