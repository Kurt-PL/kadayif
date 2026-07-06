--  Statement lowering (subunit of Kurt.Codegen).
--  Sees all of the parent body's declarations and recurses into
--  Lower_Expr_Into_Reg / Lower_Stmt freely.

with Ada.Characters.Handling;

separate (Kurt.Codegen)
procedure Lower_Stmt
  (F  : IO.File_Type;
   S  : Stmt_Access;
   ST : in out Lower_State)
is
   --  §7.9: resolve the loop targeted by a `break`/`continue`. An empty
   --  label denotes the innermost loop; a non-empty label selects the
   --  nearest enclosing loop with that source name.
   function Target_Loop
     (ST : Lower_State; Label : SU.Unbounded_String) return Loop_Labels is separate;


   --  Store the value currently in x9/w9 to [x29, Off] using the width
   --  implied by Sz cells.
   procedure Store_Sized (Off : Cell_Count; Sz : Cell_Count) is
      Loc : constant String := ", [x29, #" & Img (Off) & "]";
   begin
      if Sz >= 8 then
         IO.Put_Line (F, "    str     x9" & Loc);
      elsif Sz = 4 then
         IO.Put_Line (F, "    str     w9" & Loc);
      elsif Sz = 2 then
         IO.Put_Line (F, "    strh    w9" & Loc);
      elsif Sz = 1 then
         IO.Put_Line (F, "    strb    w9" & Loc);
      end if;  --  Sz = 0 (void): nothing to store
   end Store_Sized;

   procedure Zero_Fill (Off : Cell_Count; Sz : Cell_Count) is separate;

   --  §6.4.3 widening `a +@ b` / `a *@ b`: materialise the .{low, high}
   --  tuple at Off+0 (low) and Off+W (high). Operand type T is W bytes.
   procedure Lower_Widening
     (Off : Cell_Count; E : Expr_Access; W_Off : Cell_Count)
   is separate;

   --  Materialise a tuple-typed initialiser into the frame slot at Off.
   procedure Store_Tuple_Init
     (Off : Cell_Count; Tup : Type_Access; Init : Expr_Access)
   is separate;

   --  §8.4 lower a brace-delimited statement list as a lexical scope: the
   --  block's `with destruct` locals are destroyed (LIFO) at its textual
   --  end — before any enclosing-scope object — and then leave scope so the
   --  fn epilogue does not destroy them again. An early `return` inside the
   --  block runs its own inline drops (it never reaches this textual end).
   procedure Lower_Scoped (Stmts : Stmt_Vectors.Vector) is
      Entry_Len : constant Natural := Natural (ST.Bindings.Length);
   begin
      for I in Stmts.First_Index .. Stmts.Last_Index loop
         Lower_Stmt (F, Stmts.Element (I), ST);
         --  §7.11: a diverging statement transfers control away from this
         --  point, so any statement still to come in this block sits at a
         --  programme point translation-time evaluation proves unreachable.
         --  Insert the implicit `@trap` the spec requires there, mirroring
         --  `@trap`'s own lowering (handler dispatch, then the default
         --  undefined-instruction divergence). Covers the statement kinds
         --  that always diverge (S_Return/S_Break/S_Continue/S_Express/
         --  S_Trap) plus a bare `-> never` call statement (S_Expr).
         if I /= Stmts.Last_Index
           and then (Stmts.Element (I).Kind in
                       S_Return | S_Break | S_Continue | S_Express | S_Trap
                     or else (Stmts.Element (I).Kind = S_Expr
                              and then Is_Never_Expr
                                         (Stmts.Element (I).E_Val)))
         then
            if Unit_Has_Trap_Handler then
               IO.Put_Line (F, "    bl      _kurt_trap_handler");
            end if;
            IO.Put_Line (F, "    udf     #0         // implicit @trap (§7.11)");
         end if;
      end loop;
      Emit_Binding_Drops (F, ST, Keep => Entry_Len, Preserve_Ret => False);
      while Natural (ST.Bindings.Length) > Entry_Len loop
         ST.Bindings.Delete_Last;
      end loop;
   end Lower_Scoped;
   procedure Lower_If is separate;
   procedure Lower_While is separate;
   procedure Lower_Assign is separate;
   procedure Lower_Let is separate;
begin
   case S.Kind is
      when S_Return =>
         --  AAPCS64 aggregate returns: ≤8B in x0 (the scalar path below),
         --  9–16B in x0+x1, >16B copied through the incoming x8 pointer.
         case Classify_Agg (ST.Ret_Ty) is
            when Two_Regs | Indirect =>
               if S.R_Val = null or else S.R_Val.Kind /= E_Path
                 or else Natural (S.R_Val.Segments.Length) /= 1
                 or else Find_Binding
                   (ST, SU.To_String (S.R_Val.Segments.Last_Element)) = 0
               then
                  raise Program_Error with
                    "codegen: a wide aggregate return value must be a "
                    & "binding (bootstrap)";
               end if;
               declare
                  B : constant Binding := ST.Bindings.Element
                    (Find_Binding
                       (ST, SU.To_String (S.R_Val.Segments.Last_Element)));
               begin
                  if Classify_Agg (ST.Ret_Ty) = Two_Regs then
                     IO.Put_Line (F, "    ldr     x0, [x29, #"
                                     & Img (B.Offset) & "]");
                     IO.Put_Line (F, "    ldr     x1, [x29, #"
                                     & Img (B.Offset + 8) & "]");
                  else
                     IO.Put_Line (F, "    ldr     x10, [x29, #"
                                     & Img (ST.Sret_Off) & "]");
                     Emit_Mem_Copy (F, "x29", B.Offset, "x10", 0,
                                    Sizeof (ST.Ret_Ty));
                  end if;
               end;
            when Not_Agg | One_Reg =>
               --  §5.1 bare `return;` (void): no value to place in x0.
               if S.R_Val /= null then
                  Lower_Expr_Into_Reg (F, S.R_Val, 0, ST);
               end if;
         end case;
         --  §8.8.2: returning a binding transfers it (skip its drop).
         Note_Move (F, ST, S.R_Val);
         --  §8.4 destroy every binding live at this return point — exactly
         --  the in-scope set, since bindings declared after are not yet in
         --  ST.Bindings and inner-block locals declared before still are.
         --  The return value (x0/x1) is preserved across the drops; then
         --  branch to the bare epilogue (which performs no further drops).
         Emit_Binding_Drops (F, ST, Keep => 0, Preserve_Ret => True);
         IO.Put_Line (F, "    b       "
                         & SU.To_String (ST.Epilogue_Lbl) & "_bare");

      when S_Expr =>
         --  Evaluate for effect into a scratch register; result ignored.
         Lower_Expr_Into_Reg (F, S.E_Val, 9, ST);

      when S_Airside_Block =>
         Lower_Scoped (S.A_Stmts);

      when S_Let | S_Mut =>
         Lower_Let;
      when S_Assign =>
         Lower_Assign;
      when S_While =>
         Lower_While;
      when S_If =>
         Lower_If;
      when S_Break =>
         if ST.Loops.Is_Empty then
            raise Program_Error with "codegen: 'break' outside a loop";
         end if;
         if S.Brk_Val /= null then
            --  §7.7 value form: evaluate the break value; when the targeted
            --  loop is used as an expression, park it in that loop's result
            --  slot (which survives the binding drops below) — otherwise the
            --  value has no destination and is evaluated only for effect.
            Lower_Expr_Into_Reg (F, S.Brk_Val, 9, ST);
            declare
               R_Off : constant Long_Long_Integer :=
                 Target_Loop (ST, S.Brk_Label).Result_Off;
            begin
               if R_Off >= 0 then
                  IO.Put_Line (F, "    str     x9, [x29, #"
                                  & Img (R_Off) & "]");
               end if;
            end;
         end if;
         --  §8.4 destroy every body local live at this jump, across all
         --  scopes down to the targeted loop's body (it leaves the loop).
         Emit_Binding_Drops
           (F, ST, Keep => Target_Loop (ST, S.Brk_Label).Body_Entry,
            Preserve_Ret => False);
         IO.Put_Line (F, "    b       "
                         & SU.To_String
                             (Target_Loop (ST, S.Brk_Label).Break_Lbl));

      when S_Continue =>
         if ST.Loops.Is_Empty then
            raise Program_Error with "codegen: 'continue' outside a loop";
         end if;
         --  §8.4 destroy the body locals live at this jump before re-testing
         --  the condition (the current iteration's scope ends here).
         Emit_Binding_Drops
           (F, ST, Keep => Target_Loop (ST, S.Cont_Label).Body_Entry,
            Preserve_Ret => False);
         IO.Put_Line (F, "    b       "
                         & SU.To_String
                             (Target_Loop (ST, S.Cont_Label).Cont_Lbl));

      when S_Express =>
         --  §7.8/§7.9 block exit-with-value: store the value into the
         --  targeted express block's result slot — the innermost one, or
         --  the nearest enclosing block labelled `'l` for `express 'l`
         --  (an inner label shadows an outer one) — destroy the bindings
         --  declared since that block's entry (§7.8 dynamic semantics),
         --  and branch to its end label, an early exit wherever the
         --  `express` sits. Outside any block expression (e.g. a
         --  statement-position `airside { ... }` scope) the value is
         --  evaluated for effect.
         Lower_Expr_Into_Reg (F, S.Xp_Val, 9, ST);
         declare
            TI : Natural := 0;
         begin
            if SU.Length (S.Xp_Label) = 0 then
               if not ST.Expr_Blocks.Is_Empty then
                  TI := ST.Expr_Blocks.Last_Index;
               end if;
            else
               for I in reverse ST.Expr_Blocks.First_Index ..
                        ST.Expr_Blocks.Last_Index
               loop
                  if SU.To_String (ST.Expr_Blocks.Element (I).Name)
                       = SU.To_String (S.Xp_Label)
                  then
                     TI := I;
                     exit;
                  end if;
               end loop;
               if TI = 0 then
                  raise Program_Error with
                    "codegen: express to unknown block label '"
                    & SU.To_String (S.Xp_Label) & "'";
               end if;
            end if;
            if TI /= 0 then
               declare
                  T : constant Express_Target := ST.Expr_Blocks.Element (TI);
               begin
                  IO.Put_Line (F, "    str     x9, [x29, #"
                                  & Img (T.Result_Off) & "]");
                  Emit_Binding_Drops
                    (F, ST, Keep => T.Body_Entry, Preserve_Ret => False);
                  IO.Put_Line (F, "    b       "
                                  & SU.To_String (T.End_Lbl));
               end;
            end if;
         end;

      when S_Fence =>
         --  §8.5.3 ordering fences. The bootstrap emits in program order
         --  and performs no reordering, so a @volatile (translation) fence
         --  needs no instruction. @guard additionally constrains the
         --  execution environment: emit a full barrier for every form
         --  (`dmb ish` is stronger than the directional forms require,
         --  which is conforming).
         if S.Fn_Guard then
            IO.Put_Line (F, "    dmb     ish"
              & (case S.Fn_Form is
                    when FF_Full  => "     // @guard",
                    when FF_Start => "     // @guard.start",
                    when FF_End   => "     // @guard.end"));
         else
            IO.Put_Line (F, "    // @volatile"
              & (case S.Fn_Form is
                    when FF_Full  => "",
                    when FF_Start => ".start",
                    when FF_End   => ".end")
              & " translation fence (no instruction)");
         end if;

      when S_Trap =>
         --  §7.10: `@trap;` diverges. With a handler declared, branch into
         --  it; `@trap` is reentrant, so the handler may itself `@trap;`
         --  (another `bl` re-invokes it). The handler shall diverge, but
         --  should it fall through, the default divergence below still
         --  terminates. Default divergence is the implementation-defined
         --  behaviour: an undefined-instruction trap. It is self-contained
         --  (no external symbol or stack discipline), cannot return, and
         --  does not unwind — matching §7.10's "terminates without
         --  unwinding".
         if Unit_Has_Trap_Handler then
            IO.Put_Line (F, "    bl      _kurt_trap_handler");
         end if;
         IO.Put_Line (F, "    udf     #0         // @trap default divergence");

      when S_Asm =>
         --  §6.11 inline assembly: load `in`/`io` operands into their
         --  registers, emit the captured body verbatim, then store
         --  `out`/`io` registers back into their places. A logical operand
         --  `'name` is allocated a scratch x-register (x10..x15) and
         --  substituted into the body text.
         declare
            Body_U : SU.Unbounded_String := S.Asm_Body;

            --  Logical-operand → physical-register map.
            Log_Names : Path_Segments.Vector;
            Log_Regs  : Path_Segments.Vector;
            Next_Log  : Natural := 10;   --  next x-register to try (x10..)
            --  §6.11 frame temps for saving the `clobber(...)` registers
            --  across the body (one per declared register).
            Clob_Slots : array
              (1 .. Natural (S.Asm_Clobbers.Length)) of Cell_Count;

            --  Whether a register appears in the `clobber(...)` list.
            function Clobbered (Reg : String) return Boolean is
            begin
               for I in S.Asm_Clobbers.First_Index ..
                        S.Asm_Clobbers.Last_Index loop
                  if SU.To_String (S.Asm_Clobbers.Element (I)) = Reg then
                     return True;
                  end if;
               end loop;
               return False;
            end Clobbered;

            --  Resolve a target to its physical register: a `'name` logical
            --  operand allocates/looks up an x10.. register (skipping any in
            --  the clobber list, so an operand never shares a clobbered
            --  register); a concrete register name is returned unchanged.
            function Phys (Target : String) return String is
            begin
               if Target'Length = 0 or else Target (Target'First) /= ''' then
                  return Target;
               end if;
               for I in Log_Names.First_Index .. Log_Names.Last_Index loop
                  if SU.To_String (Log_Names.Element (I)) = Target then
                     return SU.To_String (Log_Regs.Element (I));
                  end if;
               end loop;
               while Clobbered ("x" & Img (Next_Log)) loop
                  Next_Log := Next_Log + 1;
               end loop;
               declare
                  Reg : constant String := "x" & Img (Next_Log);
               begin
                  Next_Log := Next_Log + 1;
                  Log_Names.Append (SU.To_Unbounded_String (Target));
                  Log_Regs.Append (SU.To_Unbounded_String (Reg));
                  return Reg;
               end;
            end Phys;

            --  Width-matched scratch (`w9` for a w-register / 32-bit target).
            function Scratch (Reg : String) return String is
              (if Reg'Length > 0 and then Reg (Reg'First) = 'w'
               then "w9" else "x9");

            --  §6.11 `'(expr)` immediate: a small constant-integer evaluator
            --  over the embedded expression text (literals + `+ - * / % & | ^
            --  << >>`, parens, unary `-`, a top-level `const` name — see
            --  Unit_Consts), folded at translation time.
            function Eval_Int (Src : String) return Long_Long_Integer is
               package CH renames Ada.Characters.Handling;
               P : Natural := Src'First;
               function Parse_E (Min_P : Natural) return Long_Long_Integer;
               procedure WS is
               begin
                  while P <= Src'Last
                    and then (Src (P) = ' ' or else Src (P) = ASCII.HT)
                  loop P := P + 1; end loop;
               end WS;
               function Atom return Long_Long_Integer is
                  V : Long_Long_Integer := 0;
               begin
                  WS;
                  if P <= Src'Last and then Src (P) = '-' then
                     P := P + 1; return -Atom;
                  elsif P <= Src'Last and then Src (P) = '(' then
                     P := P + 1;
                     V := Parse_E (0);
                     WS;
                     if P <= Src'Last and then Src (P) = ')' then P := P + 1; end if;
                     return V;
                  elsif P + 1 <= Src'Last and then Src (P) = '0'
                    and then (Src (P + 1) = 'x' or else Src (P + 1) = 'X')
                  then
                     P := P + 2;
                     while P <= Src'Last
                       and then (Src (P) in '0' .. '9'
                                 or else Src (P) in 'a' .. 'f'
                                 or else Src (P) in 'A' .. 'F'
                                 or else Src (P) = '_')
                     loop
                        if Src (P) /= '_' then
                           V := V * 16 + Long_Long_Integer
                             (if Src (P) in '0' .. '9'
                              then Character'Pos (Src (P)) - Character'Pos ('0')
                              elsif Src (P) in 'a' .. 'f'
                              then Character'Pos (Src (P)) - Character'Pos ('a') + 10
                              else Character'Pos (Src (P)) - Character'Pos ('A') + 10);
                        end if;
                        P := P + 1;
                     end loop;
                     return V;
                  elsif P <= Src'Last and then Src (P) in '0' .. '9' then
                     while P <= Src'Last
                       and then (Src (P) in '0' .. '9' or else Src (P) = '_')
                     loop
                        if Src (P) /= '_' then
                           V := V * 10 +
                             Long_Long_Integer
                               (Character'Pos (Src (P)) - Character'Pos ('0'));
                        end if;
                        P := P + 1;
                     end loop;
                     return V;
                  elsif P <= Src'Last
                    and then (CH.Is_Letter (Src (P)) or else Src (P) = '_')
                  then
                     --  §5.3/§6.11: an identifier atom names a top-level
                     --  `const`; its value is the const's own folded
                     --  initialiser (mirrors Emit's top-level-`asm`
                     --  evaluator, spec 5.13).
                     declare
                        Start : constant Natural := P;
                     begin
                        while P <= Src'Last
                          and then (CH.Is_Alphanumeric (Src (P))
                                    or else Src (P) = '_')
                        loop
                           P := P + 1;
                        end loop;
                        declare
                           Name : constant String := Src (Start .. P - 1);
                        begin
                           for I in Unit_Consts.First_Index ..
                                    Unit_Consts.Last_Index
                           loop
                              if SU.To_String (Unit_Consts.Element (I).Name)
                                = Name
                              then
                                 declare
                                    U2 : Kurt.Parser.Translation_Unit;
                                 begin
                                    U2.Consts := Unit_Consts;
                                    if Kurt.Parser.Fold_Int_Expr
                                         (U2, Unit_Consts.Element (I).Init, V)
                                    then
                                       return V;
                                    end if;
                                 end;
                                 exit;
                              end if;
                           end loop;
                           raise Codegen_Error with
                             "inline asm '(...)' expression names '" & Name
                             & "', which is not a translation-time "
                             & "evaluable `const` (spec 6.11)";
                        end;
                     end;
                  else
                     raise Codegen_Error with
                       "inline asm '(...)' expression is not "
                       & "translation-time evaluable (spec 6.11)";
                  end if;
               end Atom;
               --  Binding power: * / % = 5; + - = 4; << >> = 3; & = 2;
               --  ^ = 1; | = 0.
               function Parse_E (Min_P : Natural) return Long_Long_Integer is
                  L : Long_Long_Integer := Atom;
               begin
                  loop
                     WS;
                     exit when P > Src'Last;
                     declare
                        Op2 : constant String :=
                          (if P + 1 <= Src'Last then Src (P .. P + 1) else "");
                        C0  : constant Character := Src (P);
                        BP  : Integer := -1;
                        Wid : Natural := 1;
                     begin
                        if Op2 = "<<" or else Op2 = ">>" then BP := 3; Wid := 2;
                        elsif C0 = '*' or else C0 = '/' or else C0 = '%' then BP := 5;
                        elsif C0 = '+' or else C0 = '-' then BP := 4;
                        elsif C0 = '&' then BP := 2;
                        elsif C0 = '^' then BP := 1;
                        elsif C0 = '|' then BP := 0;
                        end if;
                        exit when BP < Integer (Min_P);
                        P := P + Wid;
                        declare
                           R : constant Long_Long_Integer :=
                             Parse_E (Natural (BP) + 1);
                        begin
                           if Op2 = "<<" then L := L * (2 ** Natural (R));
                           elsif Op2 = ">>" then L := L / (2 ** Natural (R));
                           elsif C0 = '*' then L := L * R;
                           elsif C0 = '/' then L := L / R;
                           elsif C0 = '%' then L := L mod R;
                           elsif C0 = '+' then L := L + R;
                           elsif C0 = '-' then L := L - R;
                           elsif C0 = '&' then
                              L := Long_Long_Integer (Interfaces."and"
                                (Interfaces.Unsigned_64 (L),
                                 Interfaces.Unsigned_64 (R)));
                           elsif C0 = '^' then
                              L := Long_Long_Integer (Interfaces."xor"
                                (Interfaces.Unsigned_64 (L),
                                 Interfaces.Unsigned_64 (R)));
                           elsif C0 = '|' then
                              L := Long_Long_Integer (Interfaces."or"
                                (Interfaces.Unsigned_64 (L),
                                 Interfaces.Unsigned_64 (R)));
                           end if;
                        end;
                     end;
                  end loop;
                  return L;
               end Parse_E;
            begin
               return Parse_E (0);
            end Eval_Int;
         begin
            --  Allocate registers for every logical target up front.
            for I in S.Asm_In_Regs.First_Index .. S.Asm_In_Regs.Last_Index loop
               declare
                  R : constant String :=
                    Phys (SU.To_String (S.Asm_In_Regs.Element (I)));
                  pragma Unreferenced (R);
               begin null; end;
            end loop;
            for I in S.Asm_Out_Regs.First_Index ..
                     S.Asm_Out_Regs.Last_Index loop
               declare
                  R : constant String :=
                    Phys (SU.To_String (S.Asm_Out_Regs.Element (I)));
                  pragma Unreferenced (R);
               begin null; end;
            end loop;
            --  Substitute each `'name` in the body with its register.
            for I in Log_Names.First_Index .. Log_Names.Last_Index loop
               declare
                  From : constant String := SU.To_String
                    (Log_Names.Element (I));
                  Into : constant String := SU.To_String
                    (Log_Regs.Element (I));
                  Idx  : Natural;
               begin
                  loop
                     Idx := SU.Index (Body_U, From);
                     exit when Idx = 0;
                     SU.Replace_Slice
                       (Body_U, Idx, Idx + From'Length - 1, Into);
                  end loop;
               end;
            end loop;
            --  §6.11 `'?` sequential positional: each occurrence consumes the
            --  next positional index (0, 1, …)'s register, in body order.
            declare
               Q : Natural := 0;
               P : Natural;
            begin
               loop
                  P := SU.Index (Body_U, "'?");
                  exit when P = 0;
                  SU.Replace_Slice
                    (Body_U, P, P + 1, Phys ("'" & Img (Q)));
                  Q := Q + 1;
               end loop;
            end;
            --  §6.11 `'(expr)` immediate: fold the embedded expression to an
            --  integer and substitute the value.
            declare
               P, Depth, Close : Natural;
            begin
               loop
                  P := SU.Index (Body_U, "'(");
                  exit when P = 0;
                  Depth := 1;
                  Close := P + 2;
                  while Close <= SU.Length (Body_U) and then Depth > 0 loop
                     if SU.Element (Body_U, Close) = '(' then
                        Depth := Depth + 1;
                     elsif SU.Element (Body_U, Close) = ')' then
                        Depth := Depth - 1;
                     end if;
                     exit when Depth = 0;
                     Close := Close + 1;
                  end loop;
                  declare
                     Expr_Txt : constant String :=
                       SU.Slice (Body_U, P + 2, Close - 1);
                     Val : constant Long_Long_Integer := Eval_Int (Expr_Txt);
                     Raw : constant String := Long_Long_Integer'Image (Val);
                     VS  : constant String :=
                       (if Raw (Raw'First) = ' '
                        then Raw (Raw'First + 1 .. Raw'Last) else Raw);
                  begin
                     SU.Replace_Slice (Body_U, P, Close, "#" & VS);
                  end;
               end loop;
            end;
            declare
               Body_S : constant String := SU.To_String (Body_U);
               Start  : Integer := Body_S'First;
            begin
            --  Inputs (clobber-safe): evaluate every operand expression to a
            --  fresh frame temp FIRST, then load the target registers from
            --  those temps with back-to-back `ldr`s. This way no operand
            --  expression is lowered after a target register has been set, so
            --  one operand's evaluation can never clobber another's register
            --  (nor a `clobber(...)`-listed one — none are live at this point).
            declare
               N     : constant Natural := Natural (S.Asm_In_Regs.Length);
               Slots : array (1 .. N) of Cell_Count;
            begin
               for I in 1 .. N loop
                  Slots (I) := ST.Next_Offset;
                  ST.Next_Offset := ST.Next_Offset + 8;
                  Lower_Expr_Into_Reg
                    (F, S.Asm_In_Exprs.Element
                          (S.Asm_In_Exprs.First_Index + (I - 1)), 9, ST);
                  IO.Put_Line (F, "    str     x9, [x29, #"
                                  & Img (Slots (I)) & "]");
               end loop;
               for I in 1 .. N loop
                  declare
                     Reg : constant String := Phys
                       (SU.To_String (S.Asm_In_Regs.Element
                          (S.Asm_In_Regs.First_Index + (I - 1))));
                     LR  : constant String :=
                       (if Reg'Length > 0 and then Reg (Reg'First) = 'w'
                        then "w" & Reg (Reg'First + 1 .. Reg'Last)
                        else Reg);
                  begin
                     IO.Put_Line (F, "    ldr     " & LR & ", [x29, #"
                                     & Img (Slots (I)) & "]");
                  end;
               end loop;
            end;
            --  §6.11 save the clobbered registers before the body, so their
            --  prior contents are preserved across it (the body destroys
            --  them); they are restored after. Operand registers are disjoint
            --  from the clobber set (Phys skips clobbered registers).
            for I in 1 .. Natural (S.Asm_Clobbers.Length) loop
               Clob_Slots (I) := ST.Next_Offset;
               ST.Next_Offset := ST.Next_Offset + 8;
               IO.Put_Line (F, "    str     "
                 & SU.To_String (S.Asm_Clobbers.Element
                     (S.Asm_Clobbers.First_Index + (I - 1)))
                 & ", [x29, #" & Img (Clob_Slots (I)) & "]");
            end loop;
            IO.Put_Line (F, "    // asm {");
            for I in Body_S'Range loop
               if Body_S (I) = ASCII.LF then
                  IO.Put_Line (F, "    " & Body_S (Start .. I - 1));
                  Start := I + 1;
               end if;
            end loop;
            if Start <= Body_S'Last then
               IO.Put_Line (F, "    " & Body_S (Start .. Body_S'Last));
            end if;
            IO.Put_Line (F, "    // }");
            --  Read outputs (from operand registers, disjoint from clobbers)
            --  before restoring the clobbered registers.
            --  Outputs: move the register into x9, store into the place.
            for I in S.Asm_Out_Regs.First_Index ..
                     S.Asm_Out_Regs.Last_Index loop
               declare
                  Reg  : constant String :=
                    Phys (SU.To_String (S.Asm_Out_Regs.Element (I)));
                  Nm   : constant String :=
                    SU.To_String (S.Asm_Out_Names.Element (I));
                  Bi   : constant Natural := Find_Binding (ST, Nm);
               begin
                  if Bi /= 0 then
                     IO.Put_Line (F, "    mov     " & Scratch (Reg) & ", "
                                     & Reg);
                     Store_Sized
                       (ST.Bindings.Element (Bi).Offset,
                        Sizeof (ST.Bindings.Element (Bi).Ty));
                  end if;
               end;
            end loop;
            --  §6.11 restore the clobbered registers from their temps.
            for I in 1 .. Natural (S.Asm_Clobbers.Length) loop
               IO.Put_Line (F, "    ldr     "
                 & SU.To_String (S.Asm_Clobbers.Element
                     (S.Asm_Clobbers.First_Index + (I - 1)))
                 & ", [x29, #" & Img (Clob_Slots (I)) & "]");
            end loop;
            end;
         end;
   end case;
end Lower_Stmt;
