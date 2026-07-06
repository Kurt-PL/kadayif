separate (Kurt.Sema.Check)
   procedure Check_Stmt (S : Stmt_Access) is
      --  Bootstrap restriction shared by the binding-form statements
      --  (`let`-else / `if let` / `while let`): their payload clauses
      --  accept plain binds and `binding = field` renames only. Nested
      --  sub-patterns (`{ res::Yes { v } }`, `{ .{ a, b } }`,
      --  `{ f # 0..=9 }`) are supported in `match`; here they would bind
      --  silently wrong, so reject them cleanly.
      procedure Reject_Sub_Patterns
        (P : Kurt.Parser.Pattern; Ctx : String)
      is
      begin
         for K in P.Sub_Pats.First_Index .. P.Sub_Pats.Last_Index loop
            if P.Sub_Pats.Element (K) /= null then
               Error ("nested / `#` sub-patterns are not yet supported in "
                      & Ctx & " (bootstrap; use `match`)");
               return;
            end if;
         end loop;
      end Reject_Sub_Patterns;

      procedure Check_If is separate;
      procedure Check_While is separate;
      procedure Check_Assign is separate;
      procedure Check_Let is separate;
   begin
      case S.Kind is
         when S_Return =>
            --  §7.6: a `-> never` subroutine's body shall not contain a
            --  `return` statement at all -- it can never produce control
            --  back to a caller.
            if Cur_Is_Never then
               Error ("`return` shall not appear in the body of a "
                      & "'-> never' subroutine (spec 7.6)");
            end if;
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
               --  §8.9: `return *r;` copies out through the dereference.
               Check_No_Destruct_Load (S.R_Val);
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
            --  §6.9: `airside { ... }` is a block expression even in
            --  statement position (its value is simply discarded), so it
            --  is a legal target for a bare `express` (§7.8).
            In_Airside    := In_Airside + 1;
            In_Expr_Block := In_Expr_Block + 1;
            Check_Block (S.A_Stmts);
            In_Expr_Block := In_Expr_Block - 1;
            In_Airside    := In_Airside - 1;

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
            if SU.Length (S.Xp_Label) > 0 then
               --  §7.9: `express 'l` shall name an enclosing labelled
               --  BLOCK. A label naming a loop, or naming nothing in
               --  scope, shall not appear. Innermost-first: an inner
               --  label shadows an outer one of the same name.
               declare
                  Resolved : Boolean := False;
               begin
                  for I in reverse Label_Stack.First_Index ..
                           Label_Stack.Last_Index
                  loop
                     if SU.To_String (Label_Stack.Element (I).Name)
                          = SU.To_String (S.Xp_Label)
                     then
                        if not Label_Stack.Element (I).Is_Block then
                           Error ("`express` names ''"
                                  & SU.To_String (S.Xp_Label)
                                  & "' which labels a loop; `express` "
                                  & "shall name a labelled block "
                                  & "(spec 7.9)");
                        end if;
                        Resolved := True;
                        exit;
                     end if;
                  end loop;
                  if not Resolved then
                     Error ("`express` names label ''"
                            & SU.To_String (S.Xp_Label)
                            & "' which names no enclosing labelled "
                            & "block (spec 7.8/7.9)");
                  end if;
               end;
            elsif In_Expr_Block = 0 then
               --  §7.8: a bare `express` appearing in a subroutine body
               --  outside any block expression shall not appear — there
               --  is no block for it to target.
               Error ("`express` shall appear only inside a block "
                      & "expression; in a subroutine body use `return` "
                      & "(spec 7.8)");
            end if;
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
