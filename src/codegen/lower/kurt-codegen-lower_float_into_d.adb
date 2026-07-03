--  Floating-point expression lowering (subunit of Kurt.Codegen).
--  Computes the value of a float-typed expression E into FP register
--  v<D_Reg> — addressed as d<D_Reg> (f64) or s<D_Reg> (f32). Mirrors
--  Lower_Expr_Into_Reg for the integer side. Bootstrap scope: f32 / f64
--  literals, bindings, fields, and the base arithmetic operators
--  + - * / (§6.4.4). Float remainder `%`, casts, and the FP call ABI are
--  handled elsewhere / deferred.

separate (Kurt.Codegen)
procedure Lower_Float_Into_D
  (F     : IO.File_Type;
   E     : Expr_Access;
   D_Reg : Natural;
   ST    : in out Lower_State)
is
   --  Width of E's float type: f32 (4 bytes) uses the s-view, else d-view.
   function FReg (Reg : Natural; T : Type_Access) return String is
     ((if Sizeof (T) = 4 then "s" else "d") & Img (Reg));

   Ty : constant Type_Access := Type_Of_Expr (E, ST);
   R  : constant String := FReg (D_Reg, Ty);
begin
   case E.Kind is
      when E_Float_Lit =>
         if E.Float_Special /= 0 then
            --  §3.5.2 `0nan` (quiet NaN, sign 0, zero payload) / `0inf`
            --  (positive infinity). Emitted directly as the IEEE bit
            --  pattern of the target width — the value never exists as a
            --  Long_Float (validity checks reject non-finite data).
            declare
               use Interfaces;
               Bits : constant Unsigned_64 :=
                 (if Sizeof (Ty) = 4
                  then (if E.Float_Special = 1
                        then 16#7FC0_0000# else 16#7F80_0000#)
                  else (if E.Float_Special = 1
                        then 16#7FF8_0000_0000_0000#
                        else 16#7FF0_0000_0000_0000#));
            begin
               Lower_Bits_64 (F, 12, Bits);
               if Sizeof (Ty) = 4 then
                  IO.Put_Line (F, "    fmov    s" & Img (D_Reg) & ", w12");
               else
                  IO.Put_Line (F, "    fmov    d" & Img (D_Reg) & ", x12");
               end if;
            end;
         else
            Lower_Float_Const (F, D_Reg, E.Float_V, Sizeof (Ty));
         end if;

      when E_Int_Lit =>
         --  An integer literal in a float context (§3.4.1): its value is
         --  representable at translation time, so emit it as a constant.
         Lower_Float_Const (F, D_Reg, Long_Float (E.Int_V), Sizeof (Ty));

      when E_Path =>
         if Natural (E.Segments.Length) = 1 then
            declare
               Name : constant String :=
                 SU.To_String (E.Segments.Last_Element);
               Idx  : constant Natural := Find_Binding (ST, Name);
            begin
               if Idx = 0 then
                  raise Program_Error with
                    "codegen: unknown float binding '" & Name & "'";
               end if;
               IO.Put_Line
                 (F, "    ldr     " & R & ", [x29, #"
                     & Img (ST.Bindings.Element (Idx).Offset) & "]");
            end;
         else
            raise Program_Error with
              "codegen: unsupported float path form";
         end if;

      when E_Field =>
         --  Float field of a struct/tuple binding living in its slot.
         if E.F_Recv.Kind = E_Path
           and then Natural (E.F_Recv.Segments.Length) = 1
         then
            declare
               B   : constant Binding := ST.Bindings.Element
                 (Find_Binding
                    (ST, SU.To_String (E.F_Recv.Segments.Last_Element)));
               FN  : constant String := SU.To_String (E.F_Name);
               Off : Natural;
            begin
               if B.Ty /= null and then B.Ty.Kind = T_Tuple then
                  Off := B.Offset + Kurt.Layout.Tuple_Field_Offset
                    (B.Ty, Natural'Value (FN));
               else
                  Off := B.Offset + Kurt.Layout.Field_Offset
                    (SU.To_String (B.Ty.Name), FN);
               end if;
               IO.Put_Line (F, "    ldr     " & R & ", [x29, #"
                               & Img (Off) & "]");
            end;
         else
            raise Program_Error with
              "codegen: unsupported float field access";
         end if;

      when E_Binary =>
         --  §6.4.4 base arithmetic. Evaluate lhs into d<D_Reg>, spill it
         --  across the rhs evaluation, then combine.
         declare
            R1 : constant String := FReg (D_Reg + 1, Ty);
            R2 : constant String := FReg (D_Reg + 2, Ty);
            Mn : constant String :=
              (case E.B_Op is
                  when B_Add  => "fadd",
                  when B_Sub  => "fsub",
                  when B_Mul  => "fmul",
                  when B_Div  => "fdiv",
                  when B_Mod  => "frem",   --  handled specially below
                  when others => "");
         begin
            if Mn = "" then
               raise Program_Error with
                 "codegen: operator not defined for floating-point types "
                 & "(only + - * / % in the bootstrap)";
            end if;
            Lower_Float_Into_D (F, E.B_Lhs, D_Reg, ST);
            IO.Put_Line (F, "    sub     sp, sp, #16");
            IO.Put_Line (F, "    str     " & R & ", [sp]");
            Lower_Float_Into_D (F, E.B_Rhs, D_Reg + 1, ST);
            IO.Put_Line (F, "    ldr     " & R & ", [sp]");
            IO.Put_Line (F, "    add     sp, sp, #16");
            if E.B_Op = B_Mod then
               --  §6.4.4 IEEE remainder: a - rne(a/b)*b. `frintn` rounds to
               --  nearest, ties to even; `fmsub` forms a - q*b. a % 0 -> NaN
               --  (b=0 => a/b = ±Inf, q = Inf, a - Inf*0 = NaN).
               IO.Put_Line (F, "    fdiv    " & R2 & ", " & R & ", " & R1);
               IO.Put_Line (F, "    frintn  " & R2 & ", " & R2);
               IO.Put_Line (F, "    fmsub   " & R & ", " & R2 & ", "
                               & R1 & ", " & R);
            else
               IO.Put_Line (F, "    " & Mn & "    " & R & ", " & R
                               & ", " & R1);
            end if;
         end;

      when E_Unary =>
         --  §6.3.1 float negation flips the sign bit (`fneg`).
         Lower_Float_Into_D (F, E.U_Operand, D_Reg, ST);
         IO.Put_Line (F, "    fneg    " & R & ", " & R);

      when E_Cast =>
         --  Result is a float (§6.8.3 int→float, §6.8.5 float→float,
         --  §6.8.11 reinterpret).
         declare
            Src   : constant Type_Access := Type_Of_Expr (E.Cast_Inner, ST);
            Src_F : constant Boolean := Is_Float (Src);
            Dst_W : constant Boolean := Sizeof (Ty) = 8;        --  d vs s
         begin
            if E.Cast_Bang then
               if Src_F then
                  --  Same-size float reinterpret == identity bits.
                  Lower_Float_Into_D (F, E.Cast_Inner, D_Reg, ST);
               else
                  --  int bits -> FP register (fmov).
                  Lower_Expr_Into_Reg (F, E.Cast_Inner, 12, ST);
                  IO.Put_Line (F, "    fmov    " & R & ", "
                                  & (if Dst_W then "x12" else "w12"));
               end if;
            elsif Src_F then
               --  float -> float precision change (fcvt). Same size = no-op.
               Lower_Float_Into_D (F, E.Cast_Inner, D_Reg, ST);
               if Sizeof (Src) /= Sizeof (Ty) then
                  IO.Put_Line (F, "    fcvt    " & R & ", "
                                  & (if Sizeof (Src) = 8 then "d" else "s")
                                  & Img (D_Reg));
               end if;
            else
               --  integer -> float (§6.8.3): nearest representable.
               Lower_Expr_Into_Reg (F, E.Cast_Inner, 12, ST);
               IO.Put_Line
                 (F, "    " & (if Is_Signed_Int (Src) then "scvtf" else "ucvtf")
                     & "   " & R & ", "
                     & (if Sizeof (Src) = 8 then "x12" else "w12"));
            end if;
         end;

      when others =>
         raise Program_Error with
           "codegen: unsupported floating-point expression form";
   end case;
end Lower_Float_Into_D;
