separate (Kurt.Sema.Check)
   procedure Check_Stmt (S : Stmt_Access) is
      procedure Check_If is separate;
      procedure Check_While is separate;
      procedure Check_Assign is separate;
      procedure Check_Let is separate;
   begin
      case S.Kind is
         when S_Return =>
            if S.R_Val = null then
               --  §5.1 bare `return;` is well-formed only in a subroutine
               --  whose return type is `void`.
               if Cur_Ret /= null and then not Is_Void_Type (Cur_Ret) then
                  Error ("bare `return;` in a subroutine returning '"
                         & Image (Cur_Ret) & "'; a value is required "
                         & "(spec 5.1)");
               end if;
               return;
            end if;
            declare
               RT : constant Type_Access := Infer (S.R_Val, Cur_Ret);
            begin
               if not Assignable (Cur_Ret, RT) then
                  Error ("return type mismatch: subroutine returns '"
                         & Image (Cur_Ret) & "' but expression is '"
                         & Image (RT) & "'");
               end if;
               --  §8.4.3: a returned landside reference shall not outlive
               --  its referent (no reference to a local / value parameter).
               if Cur_Ret /= null and then Cur_Ret.Kind = T_Ref
                 and then Cur_Ret.Sigil /= R_Raw
               then
                  Check_Return_Escape (S.R_Val);
               end if;
               --  §8.8.2: returning a `destruct`-typed binding transfers it.
               Maybe_Move (S.R_Val);
            end;

         when S_Expr =>
            declare
               ET : constant Type_Access := Infer (S.E_Val, null);
               pragma Unreferenced (ET);
            begin
               null;
            end;

         when S_Let | S_Mut =>
            Check_Let;
         when S_Assign =>
            Check_Assign;
         when S_Fence =>
            null;   --  §8.5.3: fences carry no static obligations here

         when S_While =>
            Check_While;
         when S_If =>
            Check_If;
         when S_Airside_Block =>
            In_Airside := In_Airside + 1;
            Check_Block (S.A_Stmts);
            In_Airside := In_Airside - 1;

         when S_Extract =>
            --  §7: `let v <- e else err { ... }`. e is a contract value;
            --  v binds the success payload for the rest of the block,
            --  err binds the failure payload inside the else block.
            declare
               ET : constant Type_Access := Infer (S.X_Expr, null);
               EN : constant String :=
                 (if ET /= null and then ET.Kind = T_Named
                  then SU.To_String (ET.Name) else "");
               Saved : Natural;
            begin
               if EN = "" or else not Kurt.Layout.Is_Contract_Enum (EN)
               then
                  Error ("`<-` requires a contract value; got '"
                         & Image (ET) & "'");
                  Check_Block (S.X_Else);
               else
                  Saved := Natural (Scope.Length);
                  if SU.Length (S.X_Err) > 0 then
                     Scope.Append
                       ((Name => S.X_Err,
                         Ty   => Kurt.Layout.Variant_Field_Type
                                   (ET,
                                    Kurt.Layout.Contract_Fail_Variant (EN),
                                    1), others => <>));
                  end if;
                  Check_Block (S.X_Else);
                  while Natural (Scope.Length) > Saved loop
                     Scope.Delete_Last;
                  end loop;
                  --  §7.2.3: the `else` block shall either diverge or
                  --  yield a fallback value via `express`; otherwise
                  --  the extracted binding would continue uninitialized
                  --  on the failure path.
                  if not Stmts_Diverge (S.X_Else) then
                     Error ("the `else` of `<-` must diverge (return/"
                            & "break/continue/@trap) or yield a value "
                            & "via `express` (spec 7.2.3)");
                  end if;
                  declare
                     Succ_Ty : constant Type_Access :=
                       Kurt.Layout.Variant_Field_Type
                         (ET, Kurt.Layout.Contract_Success_Variant (EN), 1);
                  begin
                     if S.X_Is_Place then
                        --  §7.2.3 copy the success payload into the place,
                        --  which shall be an existing `mut` binding.
                        declare
                           PN : constant String := SU.To_String (S.X_Bind);
                           PT : constant Type_Access := Lookup_Scope (PN);
                           Is_Local : Boolean;
                           Mutable  : constant Boolean :=
                             Lookup_Scope_Mut (PN, Is_Local);
                        begin
                           if PT = null then
                              Error ("extract-assignment target '" & PN
                                     & "' is not a binding");
                           elsif not Mutable then
                              Error ("extract-assignment target '" & PN
                                     & "' must be `mut` (spec 7.2.3)");
                           elsif not Assignable (PT, Succ_Ty) then
                              Error ("extract-assignment type mismatch: "
                                     & "place is '" & Image (PT)
                                     & "' but success payload is '"
                                     & Image (Succ_Ty) & "'");
                           end if;
                        end;
                     else
                        --  Success binding stays in scope for the rest.
                        Scope.Append
                          ((Name => S.X_Bind, Ty => Succ_Ty, others => <>));
                     end if;
                  end;
               end if;
            end;

         when S_Break =>
            --  §7.7/§7.9: break may carry a value and/or a target label.
            if In_Loop = 0 then
               Error ("`break` shall appear only within a loop (spec 7.7)");
            end if;
            Check_Loop_Label (S.Brk_Label);
            if S.Brk_Val /= null then
               declare
                  T : constant Type_Access := Infer (S.Brk_Val, null);
                  pragma Unreferenced (T);
               begin null; end;
            end if;
         when S_Continue =>
            --  §7.9: optional target label.
            if In_Loop = 0 then
               Error ("`continue` shall appear only within a loop "
                      & "(spec 7.7)");
            end if;
            Check_Loop_Label (S.Cont_Label);
         when S_Express =>
            --  §7.8: the expressed value is typed against the innermost
            --  enclosing block expression's expected type (steering
            --  literals like a `let` annotation); outside a block
            --  expression it is inferred freely.
            declare
               T : constant Type_Access :=
                 Infer (S.Xp_Val, Express_Expected);
               pragma Unreferenced (T);
            begin null; end;

         when S_Trap =>
            --  §7.10/§7.11: `@trap;` is a diverging expression; it
            --  produces no value and imposes no type obligation.
            null;
         when S_Asm =>
            --  §6.11 inline assembly is opaque to the type system, but its
            --  `in`/`io` operand expressions are ordinary Kurt expressions
            --  (inferred so codegen has their types) and each `out`/`io`
            --  target shall be an existing binding (a place).
            --  §6.11: `asm` is permitted only inside an airside region.
            if In_Airside = 0 then
               Error ("inline `asm` is permitted only inside an `airside` "
                      & "block or `airside fn` body (spec 6.11)");
            end if;
            for I in S.Asm_In_Exprs.First_Index ..
                     S.Asm_In_Exprs.Last_Index loop
               declare
                  T : constant Type_Access :=
                    Infer (S.Asm_In_Exprs.Element (I), null);
                  pragma Unreferenced (T);
               begin null; end;
            end loop;
            for I in S.Asm_Out_Names.First_Index ..
                     S.Asm_Out_Names.Last_Index loop
               if Lookup_Scope
                    (SU.To_String (S.Asm_Out_Names.Element (I))) = null
               then
                  Error ("asm `out` target '"
                         & SU.To_String (S.Asm_Out_Names.Element (I))
                         & "' is not a binding");
               end if;
            end loop;
            --  §6.11: overlap between a (resource-mode) operand target and
            --  a `clobber` entry, and duplicate resource targets, shall not
            --  appear. Logical/positional targets (`'…`) get impl-chosen
            --  registers and cannot textually overlap a named clobber.
            declare
               function In_Clobbers (R : String) return Boolean is
               begin
                  for K in S.Asm_Clobbers.First_Index ..
                           S.Asm_Clobbers.Last_Index loop
                     if SU.To_String (S.Asm_Clobbers.Element (K)) = R then
                        return True;
                     end if;
                  end loop;
                  return False;
               end In_Clobbers;

               procedure Check_Target (R : String) is
               begin
                  if R'Length > 0 and then R (R'First) /= '''
                    and then In_Clobbers (R)
                  then
                     Error ("asm operand target '" & R & "' overlaps a "
                            & "`clobber` entry (spec 6.11)");
                  end if;
               end Check_Target;
            begin
               for I in S.Asm_In_Regs.First_Index ..
                        S.Asm_In_Regs.Last_Index loop
                  Check_Target (SU.To_String (S.Asm_In_Regs.Element (I)));
               end loop;
               for I in S.Asm_Out_Regs.First_Index ..
                        S.Asm_Out_Regs.Last_Index loop
                  Check_Target (SU.To_String (S.Asm_Out_Regs.Element (I)));
               end loop;
            end;
      end case;
   end Check_Stmt;
