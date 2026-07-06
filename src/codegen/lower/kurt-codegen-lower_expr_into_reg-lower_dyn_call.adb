separate (Kurt.Codegen.Lower_Expr_Into_Reg)
   procedure Lower_Dyn_Call (E : Expr_Access) is
      Recv  : constant Expr_Access := E.C_Callee.F_Recv;
      RT    : constant Type_Access := Type_Of_Expr (Recv, ST);
      Trait : constant String := SU.To_String (RT.Target.Trait_Name);
      Field : constant Integer :=
        Method_Field_Index (Trait, SU.To_String (E.C_Callee.F_Name));
      N     : constant Natural := Natural (E.C_Args.Length);
      Total : constant Natural := ((N * 8 + 15) / 16) * 16;
      Bi    : constant Natural :=
        (if Recv.Kind = E_Path
            and then Natural (Recv.Segments.Length) = 1
         then Find_Binding (ST, SU.To_String (Recv.Segments.Last_Element))
         else 0);
   begin
      if Bi = 0 then
         raise Program_Error with
           "codegen: dynamic-dispatch receiver must be a `&dyn` binding";
      end if;
      if Field < 0 then
         raise Program_Error with
           "codegen: method not found in trait '" & Trait & "'";
      end if;
      declare
         Off : constant Cell_Count := ST.Bindings.Element (Bi).Offset;
      begin
         --  Evaluate the explicit (non-self) arguments into scratch slots.
         if Total > 0 then
            IO.Put_Line (F, "    sub     sp, sp, #" & Img (Total));
         end if;
         for K in 0 .. N - 1 loop
            Lower_Expr_Into_Reg
              (F, E.C_Args.Element (E.C_Args.First_Index + K), 9, ST);
            IO.Put_Line (F, "    str     x9, [sp, #" & Img (K * 8) & "]");
         end loop;
         --  self pointer -> x0, explicit args -> x1..
         IO.Put_Line (F, "    ldr     x0, [x29, #" & Img (Off) & "]");
         for K in 0 .. N - 1 loop
            IO.Put_Line (F, "    ldr     x" & Img (K + 1)
                            & ", [sp, #" & Img (K * 8) & "]");
         end loop;
         --  dispatch table -> x9, method pointer at field*8 -> x9, blr.
         IO.Put_Line (F, "    ldr     x9, [x29, #" & Img (Off + 8) & "]");
         IO.Put_Line (F, "    ldr     x9, [x9, #" & Img (Field * 8) & "]");
         IO.Put_Line (F, "    blr     x9");
         if Total > 0 then
            IO.Put_Line (F, "    add     sp, sp, #" & Img (Total));
         end if;
         if Target_Reg /= 0 then
            IO.Put_Line (F, "    mov     " & Xreg & ", x0");
         end if;
      end;
   end Lower_Dyn_Call;
