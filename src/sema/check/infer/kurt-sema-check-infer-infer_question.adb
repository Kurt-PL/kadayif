separate (Kurt.Sema.Check.Infer)
   function Infer_Question return Type_Access is
   begin
            --  §6.2.4: `e?` requires e and the enclosing fn return to
            --  both satisfy `contract`. Failure payload types shall
            --  match. The expression's type is e's success payload.
            declare
               IT : constant Type_Access := Infer (E.Q_Inner, null);
               EN : constant String :=
                 (if IT /= null and then IT.Kind = T_Named
                  then SU.To_String (IT.Name) else "");
               Ret_EN : constant String :=
                 (if Cur_Ret /= null and then Cur_Ret.Kind = T_Named
                  then SU.To_String (Cur_Ret.Name) else "");
            begin
               if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN) then
                  Error ("`?` operand must satisfy `contract`, got '"
                         & Image (IT) & "'");
                  E.Sem_Ty := IT;
                  return E.Sem_Ty;
               end if;
               if Ret_EN = ""
                 or else not Kurt.Layout.Is_Contract_Enum (Ret_EN)
               then
                  Error ("`?` requires the enclosing subroutine to "
                         & "return a `contract` type; got '"
                         & Image (Cur_Ret) & "'");
               elsif not Same_Type (Kurt.Layout.Variant_Field_Type
                       (IT, Kurt.Layout.Contract_Fail_Variant (EN), 1),
                     Kurt.Layout.Variant_Field_Type
                       (Cur_Ret,
                        Kurt.Layout.Contract_Fail_Variant (Ret_EN), 1))
               then
                  Error ("`?` failure payload type of '" & Image (IT)
                         & "' does not match the enclosing return "
                         & "type '" & Image (Cur_Ret) & "' (spec 7.2.4)");
               end if;
               E.Sem_Ty := Kurt.Layout.Variant_Field_Type
                 (IT, Kurt.Layout.Contract_Success_Variant (EN), 1);
               return E.Sem_Ty;
            end;

   end Infer_Question;
