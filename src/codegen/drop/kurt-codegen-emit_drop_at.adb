separate (Kurt.Codegen)
   procedure Emit_Drop_At
     (F : IO.File_Type; Self_Off, Off : Natural;
      T : Kurt.Parser.Type_Access)
   is
   begin
      if T = null or else not Kurt.Layout.Satisfies_Destruct (T) then
         return;
      end if;
      case T.Kind is
         when Kurt.Parser.T_Named =>
            IO.Put_Line (F, "    ldr     x9, [x29, #" & Img (Self_Off) & "]");
            IO.Put_Line (F, "    add     x0, x9, #" & Img (Off));
            IO.Put_Line (F, "    bl      _"
                            & SU.To_String (T.Name) & "$drop");
         when Kurt.Parser.T_Array =>
            --  §8.11.1 array elements destroyed in reverse index order.
            for K in reverse 0 .. T.Len - 1 loop
               Emit_Drop_At (F, Self_Off,
                             Off + K * Kurt.Layout.Size_Of (T.Elem), T.Elem);
            end loop;
         when Kurt.Parser.T_Tuple =>
            for K in T.Elems.First_Index .. T.Elems.Last_Index loop
               Emit_Drop_At
                 (F, Self_Off,
                  Off + Kurt.Layout.Tuple_Field_Offset
                          (T, K - T.Elems.First_Index),
                  T.Elems.Element (K));
            end loop;
         when others =>
            null;
      end case;
   end Emit_Drop_At;
