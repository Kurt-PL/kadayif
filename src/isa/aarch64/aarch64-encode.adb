package body AArch64.Encode is

   use Interfaces;

   function W (N : Natural) return Word is (Word (N));

   --  Bits비트 2의 보수
   function Field (Value : Integer; Bits : Positive) return Word is
     (Word (Value mod 2 ** Bits));

   function Sf_Bit (Sf : Boolean) return Word is
     (if Sf then 16#8000_0000# else 0);

   function Operands (Rd, Rn : Reg) return Word is
     (Shift_Left (W (Rn), 5) or W (Rd));

   function Add_Imm (Rd, Rn : Reg; Imm : Imm12; Sf : Boolean := True)
                     return Word is
     (Sf_Bit (Sf) or 16#1100_0000# or Shift_Left (W (Imm), 10)
      or Operands (Rd, Rn));

   function Sub_Imm (Rd, Rn : Reg; Imm : Imm12; Sf : Boolean := True)
                     return Word is
     (Sf_Bit (Sf) or 16#5100_0000# or Shift_Left (W (Imm), 10)
      or Operands (Rd, Rn));

   function Subs_Imm (Rd, Rn : Reg; Imm : Imm12) return Word is
     (16#F100_0000# or Shift_Left (W (Imm), 10) or Operands (Rd, Rn));

   function Reg_Reg (Op : Reg_Op; Rd, Rn, Rm : Reg; Sf : Boolean := True)
                     return Word
   is
      Base : constant Word :=
        (case Op is
           when Op_Add  => 16#0B00_0000#,
           when Op_Sub  => 16#4B00_0000#,
           when Op_Subs => 16#6B00_0000#,
           when Op_And  => 16#0A00_0000#,
           when Op_Orr  => 16#2A00_0000#,
           when Op_Eor  => 16#4A00_0000#,
           when Op_Orn  => 16#2A20_0000#);
   begin
      return Sf_Bit (Sf) or Base or Shift_Left (W (Rm), 16)
        or Operands (Rd, Rn);
   end Reg_Reg;

   function Orr_Shifted (Rd, Rn, Rm : Reg; Shift : Natural) return Word is
     (Reg_Reg (Op_Orr, Rd, Rn, Rm) or Shift_Left (W (Shift), 10));

   function Lsr_Imm (Rd, Rn : Reg; Shift : Natural) return Word is
     (16#D340_FC00# or Shift_Left (W (Shift), 16) or Operands (Rd, Rn));

   function Madd (Rd, Rn, Rm, Ra : Reg) return Word is
     (16#9B00_0000# or Shift_Left (W (Rm), 16) or Shift_Left (W (Ra), 10)
      or Operands (Rd, Rn));

   function Msub (Rd, Rn, Rm, Ra : Reg) return Word is
     (16#9B00_8000# or Shift_Left (W (Rm), 16) or Shift_Left (W (Ra), 10)
      or Operands (Rd, Rn));

   function Div (Rd, Rn, Rm : Reg; Signed : Boolean) return Word is
     ((if Signed then 16#9AC0_0C00# else 16#9AC0_0800#)
      or Shift_Left (W (Rm), 16) or Operands (Rd, Rn));

   --  64비트 비트마스크 즉치값: N=1, immr=0, imms=Width-1
   function And_Low_Mask (Rd, Rn : Reg; Width : Positive) return Word is
     (16#9240_0000# or Shift_Left (W (Width - 1), 10) or Operands (Rd, Rn));

   --  sbfm Xd, Xn, #0, #(Width-1)
   function Sign_Extend (Rd, Rn : Reg; Width : Positive) return Word is
     (16#9340_0000# or Shift_Left (W (Width - 1), 10) or Operands (Rd, Rn));

   function Movz (Rd : Reg; Value : Imm16; Shift : Natural) return Word is
     (16#D280_0000# or Shift_Left (W (Shift / 16), 21)
      or Shift_Left (W (Value), 5) or W (Rd));

   function Movk (Rd : Reg; Value : Imm16; Shift : Natural) return Word is
     (16#F280_0000# or Shift_Left (W (Shift / 16), 21)
      or Shift_Left (W (Value), 5) or W (Rd));

   function Adrp (Rd : Reg) return Word is (16#9000_0000# or W (Rd));

   --  cset Xd, cond = csinc Xd, xzr, xzr, invert(cond)
   function Cset (Rd : Reg; Cond : Natural) return Word is
     (16#9A9F_07E0# or Shift_Left (W (Cond) xor 1, 12) or W (Rd));

   function B (Offset_Words : Branch26_Range) return Word is
     (16#1400_0000# or Field (Offset_Words, 26));

   function BL (Offset_Words : Branch26_Range) return Word is
     (16#9400_0000# or Field (Offset_Words, 26));

   function B_Cond (Cond : Natural; Offset_Words : Branch19_Range)
                    return Word is
     (16#5400_0000# or Shift_Left (Field (Offset_Words, 19), 5) or W (Cond));

   function Ret return Word is (16#D65F_03C0#);

   --  크기별 기본 부호: size(31:30)와 opc(23:22)
   function Size_Bits (Size : Positive) return Word is
     (case Size is
        when 1 => 16#0000_0000#,
        when 2 => 16#4000_0000#,
        when 4 => 16#8000_0000#,
        when others => 16#C000_0000#);

   --  64비트 적재에는 부호 확장이 없다: ldrs*는 8바이트보다 좁을 때만
   function Opc_Bits (Store, Signed : Boolean; Size : Positive) return Word is
     (if Store then 0
      elsif Signed and then Size < 8 then 16#0080_0000#
      else 16#0040_0000#);

   function Load_Store_Unscaled
     (Store : Boolean; Size : Positive; Signed : Boolean;
      Rt, Rn : Reg; Offset : Imm9) return Word is
     (16#3800_0000# or Size_Bits (Size) or Opc_Bits (Store, Signed, Size)
      or Shift_Left (Field (Offset, 9), 12) or Operands (Rt, Rn));

   function Load_Store_Unsigned
     (Store : Boolean; Size : Positive; Signed : Boolean;
      Rt, Rn : Reg; Offset : Natural) return Word
   is
      Scaled : constant Imm12 := Offset / Size;
   begin
      if Offset mod Size /= 0 then
         raise Constraint_Error with "misaligned scaled offset";
      end if;
      return 16#3900_0000# or Size_Bits (Size)
        or Opc_Bits (Store, Signed, Size)
        or Shift_Left (W (Scaled), 10) or Operands (Rt, Rn);
   end Load_Store_Unsigned;

   function Str_Pre (Rt, Rn : Reg; Offset : Imm9) return Word is
     (16#F800_0C00# or Shift_Left (Field (Offset, 9), 12)
      or Operands (Rt, Rn));

   function Ldr_Post (Rt, Rn : Reg; Offset : Imm9) return Word is
     (16#F840_0400# or Shift_Left (Field (Offset, 9), 12)
      or Operands (Rt, Rn));

   function Stp_Pre (Rt, Rt2, Rn : Reg; Offset : Pair_Offset) return Word is
     (16#A980_0000# or Shift_Left (Field (Offset / 8, 7), 15)
      or Shift_Left (W (Rt2), 10) or Operands (Rt, Rn));

   function Ldp_Post (Rt, Rt2, Rn : Reg; Offset : Pair_Offset) return Word is
     (16#A8C0_0000# or Shift_Left (Field (Offset / 8, 7), 15)
      or Shift_Left (W (Rt2), 10) or Operands (Rt, Rn));

   function Patch_Branch (Insn : Word; Offset_Words : Integer) return Word is
   begin
      if (Insn and 16#FF00_0000#) = 16#5400_0000# then
         declare
            Checked : constant Branch19_Range := Offset_Words;
         begin
            return (Insn and 16#FF00_001F#)
              or Shift_Left (Field (Checked, 19), 5);
         end;
      end if;
      declare
         Checked : constant Branch26_Range := Offset_Words;
      begin
         return (Insn and 16#FC00_0000#) or Field (Checked, 26);
      end;
   end Patch_Branch;

   function Patch_Page (Insn : Word; Delta_Pages : Integer) return Word is
      subtype Page_Range is Integer range -2 ** 20 .. 2 ** 20 - 1;
      Checked : constant Page_Range := Delta_Pages;
      Bits    : constant Word := Field (Checked, 21);
   begin
      --  immlo는 29–30비트, immhi는 5–23비트
      return (Insn and 16#9F00_001F#)
        or Shift_Left (Bits and 3, 29)
        or Shift_Left (Shift_Right (Bits, 2), 5);
   end Patch_Page;

   function Patch_Imm12 (Insn : Word; Imm : Imm12) return Word is
     ((Insn and 16#FFC0_03FF#) or Shift_Left (W (Imm), 10));

   function Br (Rn : Reg) return Word is
     (16#D61F_0000# or Shift_Left (W (Rn), 5));

end AArch64.Encode;
