--  AArch64 명령 → 기계어 (Arm A64 인코딩)
--
--  레지스터 번호 31은 명령에 따라 sp 또는 zr이다. 재배치나 레이블이
--  채울 즉치값 칸은 0으로 둔다.
with Interfaces;

package AArch64.Encode is

   subtype Word is Interfaces.Unsigned_32;
   subtype Reg is Natural range 0 .. 31;

   SP_Or_ZR : constant Reg := 31;

   --  즉치값 칸의 범위. 넘치면 조용히 잘리는 대신 Constraint_Error.
   subtype Imm12 is Natural range 0 .. 4095;
   subtype Imm16 is Natural range 0 .. 65535;
   subtype Imm9 is Integer range -256 .. 255;
   subtype Pair_Offset is Integer range -512 .. 504;
   subtype Branch26_Range is Integer range -2 ** 25 .. 2 ** 25 - 1;
   subtype Branch19_Range is Integer range -2 ** 18 .. 2 ** 18 - 1;

   --  산술: Sf는 64비트 여부
   function Add_Imm (Rd, Rn : Reg; Imm : Imm12; Sf : Boolean := True)
                     return Word;
   function Sub_Imm (Rd, Rn : Reg; Imm : Imm12; Sf : Boolean := True)
                     return Word;
   function Subs_Imm (Rd, Rn : Reg; Imm : Imm12) return Word;

   type Reg_Op is (Op_Add, Op_Sub, Op_Subs, Op_And, Op_Orr, Op_Eor, Op_Orn);
   function Reg_Reg (Op : Reg_Op; Rd, Rn, Rm : Reg; Sf : Boolean := True)
                     return Word;

   --  orr Xd, Xn, Xm, lsl #Shift
   function Orr_Shifted (Rd, Rn, Rm : Reg; Shift : Natural) return Word;
   --  lsr Xd, Xn, #Shift (ubfm Xd, Xn, #Shift, #63)
   function Lsr_Imm (Rd, Rn : Reg; Shift : Natural) return Word;

   function Madd (Rd, Rn, Rm, Ra : Reg) return Word;
   function Msub (Rd, Rn, Rm, Ra : Reg) return Word;
   function Div (Rd, Rn, Rm : Reg; Signed : Boolean) return Word;

   --  and Xd, Xn, #(2^Width - 1)
   function And_Low_Mask (Rd, Rn : Reg; Width : Positive) return Word;
   --  sxtb/sxth/sxtw Xd, Wn: 하위 Width비트 부호 확장
   function Sign_Extend (Rd, Rn : Reg; Width : Positive) return Word;

   function Movz (Rd : Reg; Value : Imm16; Shift : Natural) return Word;
   function Movk (Rd : Reg; Value : Imm16; Shift : Natural) return Word;
   function Adrp (Rd : Reg) return Word;

   --  cond: eq ne hs lo mi pl vs vc hi ls ge lt gt le 순서의 번호
   function Cset (Rd : Reg; Cond : Natural) return Word;

   function B (Offset_Words : Branch26_Range) return Word;
   function BL (Offset_Words : Branch26_Range) return Word;
   function B_Cond (Cond : Natural; Offset_Words : Branch19_Range)
                    return Word;
   function Ret return Word;

   --  적재·저장. Size는 바이트 수, Signed는 64비트로 부호 확장하는 적재.
   function Load_Store_Unscaled
     (Store : Boolean; Size : Positive; Signed : Boolean;
      Rt, Rn : Reg; Offset : Imm9) return Word;
   function Load_Store_Unsigned
     (Store : Boolean; Size : Positive; Signed : Boolean;
      Rt, Rn : Reg; Offset : Natural) return Word;
   --  Offset은 Size의 배수이고 Offset / Size는 Imm12 안이어야 한다

   function Str_Pre (Rt, Rn : Reg; Offset : Imm9) return Word;
   function Ldr_Post (Rt, Rn : Reg; Offset : Imm9) return Word;
   function Stp_Pre (Rt, Rt2, Rn : Reg; Offset : Pair_Offset) return Word;
   function Ldp_Post (Rt, Rt2, Rn : Reg; Offset : Pair_Offset) return Word;

   --  B_Cond나 B·BL의 즉치값 칸을 채운다
   function Patch_Branch (Insn : Word; Offset_Words : Integer) return Word;

   --  링커의 재배치 적용: adrp의 페이지 차(4KiB 단위)와 add의 12비트
   --  즉치값
   function Patch_Page (Insn : Word; Delta_Pages : Integer) return Word;
   function Patch_Imm12 (Insn : Word; Imm : Imm12) return Word;

   --  br Xn
   function Br (Rn : Reg) return Word;

end AArch64.Encode;
