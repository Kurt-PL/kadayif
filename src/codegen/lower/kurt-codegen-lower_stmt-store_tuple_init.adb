separate (Kurt.Codegen.Lower_Stmt)
   procedure Store_Tuple_Init
     (Off : Natural; Tup : Type_Access; Init : Expr_Access)
   is
   begin
      if Init.Kind = E_Tuple_Lit then
         for I in Init.TL_Elems.First_Index .. Init.TL_Elems.Last_Index loop
            declare
               Idx : constant Natural := I - Init.TL_Elems.First_Index;
            begin
               Lower_Expr_Into_Reg (F, Init.TL_Elems.Element (I), 9, ST);
               Store_Sized
                 (Off + Kurt.Layout.Tuple_Field_Offset (Tup, Idx),
                  Sizeof (Kurt.Layout.Tuple_Field_Type (Tup, Idx)));
            end;
         end loop;
      elsif Init.Kind = E_Binary
        and then (Init.B_Op = B_Wide_Add or else Init.B_Op = B_Wide_Mul)
      then
         Lower_Widening (Off, Init, Kurt.Layout.Tuple_Field_Offset (Tup, 1));
      elsif Sizeof (Tup) <= 8 then
         --  A ≤8-byte tuple produced by some other value-yielding
         --  expression (e.g. §7.2.3 `contract e else fallback` extracting
         --  a tuple success payload): Lower_Expr_Into_Reg packs it whole
         --  into a single register; copy that register out verbatim.
         Lower_Expr_Into_Reg (F, Init, 9, ST);
         Store_Sized (Off, Sizeof (Tup));
      else
         raise Program_Error with
           "codegen: unsupported tuple initialiser";
      end if;
   end Store_Tuple_Init;
