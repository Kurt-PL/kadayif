separate (Kurt.Codegen)
   procedure Emit_Fn
     (F        : IO.File_Type;
      Fn       : Fn_Decl;
      Dyn_Syms : Dyn_Sym_Pkg.Vector;
      Fn_Rets  : Fn_Ret_Pkg.Vector;
      Str_Base : in out Natural)
   is
      --  §5.15: an `@symbol "name"` on an extern fn overrides the emitted
      --  external label; otherwise the identifier is used.
      Sym : constant String := "_"
        & (if SU.Length (Fn.Header.Symbol_Name) > 0
           then SU.To_String (Fn.Header.Symbol_Name)
           else SU.To_String (Fn.Header.Name));
      ST  : Lower_State;
   begin
      ST.Dyn_Syms := Dyn_Syms;
      ST.Fn_Rets  := Fn_Rets;
      ST.Fn_Name  := Fn.Header.Name;
      ST.Ret_Ty   := Fn.Header.Return_Type;
      --  Continue string-label numbering across functions so it matches
      --  the global order in which Collect_Strings filled the pool.
      ST.Next_Str_Idx := Str_Base;
      IO.New_Line (F);
      IO.Put_Line (F, ".globl " & Sym);
      IO.Put_Line (F, ".p2align 2");
      IO.Put_Line (F, Sym & ":");

      --  Prologue. The stp/ldp pre/post-index immediates only reach
      --  ±512, so the frame is carved with a separate sub/add (range
      --  0..4095) and x29/x30 saved at the frame base.
      IO.Put_Line (F, "    sub     sp, sp, #" & Img (Frame_Bytes));
      IO.Put_Line (F, "    stp     x29, x30, [sp]");
      IO.Put_Line (F, "    mov     x29, sp");

      ST.Epilogue_Lbl :=
        SU.To_Unbounded_String ("Lret_" & SU.To_String (Fn.Header.Name));

      ST.Ret_Scratch := ST.Next_Offset;
      ST.Next_Offset := ST.Next_Offset + 16;

      --  AAPCS64: an indirect-class (sret) return arrives as a pointer in
      --  x8. Preserve it across the body for the S_Return copy.
      if Classify_Agg (ST.Ret_Ty) = Indirect then
         ST.Sret_Off := Integer (ST.Next_Offset);
         IO.Put_Line (F, "    str     x8, [x29, #"
                         & Img (ST.Next_Offset) & "]");
         ST.Next_Offset := ST.Next_Offset + 8;
      end if;

      --  Spill parameters into stack slots and register their bindings.
      --  AAPCS64: scalars and ≤8-byte aggregates take one x register,
      --  9–16-byte aggregates a register pair, and >16-byte aggregates
      --  arrive as a pointer to a caller-owned copy (copied into the
      --  frame so the binding behaves like any local).
      declare
         NGRN : Natural := 0;   --  next general-purpose register number
      begin
         for I in Fn.Header.Params.First_Index ..
                  Fn.Header.Params.Last_Index
         loop
            declare
               P   : constant Param     := Fn.Header.Params.Element (I);
               Cls : constant Agg_Class := Classify_Agg (P.Ty);
               Off : constant Natural   := ST.Next_Offset;
            begin
               case Cls is
                  when Not_Agg | One_Reg =>
                     IO.Put_Line (F, "    str     x" & Img (NGRN)
                                     & ", [x29, #" & Img (Off) & "]");
                     NGRN := NGRN + 1;
                     ST.Next_Offset := ST.Next_Offset + 8;
                  when Two_Regs =>
                     IO.Put_Line (F, "    str     x" & Img (NGRN)
                                     & ", [x29, #" & Img (Off) & "]");
                     IO.Put_Line (F, "    str     x" & Img (NGRN + 1)
                                     & ", [x29, #" & Img (Off + 8) & "]");
                     NGRN := NGRN + 2;
                     ST.Next_Offset := ST.Next_Offset + 16;
                  when Indirect =>
                     declare
                        Sz   : constant Natural := Sizeof (P.Ty);
                        Slot : constant Natural := ((Sz + 7) / 8) * 8;
                     begin
                        IO.Put_Line (F, "    mov     x10, x" & Img (NGRN));
                        Emit_Mem_Copy (F, "x10", 0, "x29", Off, Sz);
                        NGRN := NGRN + 1;
                        ST.Next_Offset := ST.Next_Offset + Slot;
                     end;
               end case;
               if SU.Length (P.Name) > 0 then
                  ST.Bindings.Append
                    ((Name => P.Name, Offset => Off, Ty => P.Ty));
                  --  §8.4 a `destruct`-typed value parameter is destroyed when
                  --  the call returns — unless it is moved out first. Arm its
                  --  runtime drop flag (1 = live on entry) so a move-out
                  --  (`return g;`) clears it and the drop runs exactly once.
                  if P.Ty /= null and then P.Ty.Kind = T_Named
                    and then Type_Has_Drop (SU.To_String (P.Ty.Name))
                  then
                     declare
                        Flag : constant Natural := ST.Next_Offset;
                     begin
                        ST.Next_Offset := ST.Next_Offset + 8;
                        IO.Put_Line (F, "    mov     w9, #1");
                        IO.Put_Line (F, "    strb    w9, [x29, #"
                                        & Img (Flag) & "]");
                        ST.Drop_Flags.Append
                          ((Bind_Off => Off, Flag_Off => Flag));
                     end;
                  end if;
               end if;
            end;
         end loop;
      end;

      --  Body
      for I in Fn.Body_Stmts.First_Index .. Fn.Body_Stmts.Last_Index loop
         Lower_Stmt (F, Fn.Body_Stmts.Element (I), ST);
      end loop;

      --  §7.11: a `-> never` body diverges, so reaching here is impossible.
      --  Emit the implicit `@trap` the spec requires at the unreachable
      --  point — an undefined-instruction trap rather than a stray return.
      if Fn.Header.Is_Never then
         IO.Put_Line (F, "    udf     #0         // implicit @trap (§7.11)");
      end if;

      --  Epilogue
      IO.Put_Line (F, SU.To_String (ST.Epilogue_Lbl) & ":");

      --  §8.4/§8.11 scope-exit destruction (fall-through path): destroy the
      --  remaining in-scope bindings — the fn-level scope, since every inner
      --  block drops and discards its own locals at its textual end. Each
      --  `return` performs the equivalent drop inline for the bindings live
      --  at that point and branches past this to the bare epilogue.
      Emit_Binding_Drops (F, ST, Keep => 0, Preserve_Ret => True);

      --  §8.11 field destruction tail: when this subroutine is a synthesised
      --  `<T>$drop`, destroy `self`'s destruct-satisfying fields after the
      --  user `with destruct` block has run. `self` is a reference, so its
      --  own scope exit triggers no further destruction — only its fields do.
      declare
         Nm : constant String := SU.To_String (Fn.Header.Name);
      begin
         if Nm'Length > 5
           and then Nm (Nm'Last - 4 .. Nm'Last) = "$drop"
         then
            declare
               Tn       : constant String := Nm (Nm'First .. Nm'Last - 5);
               Self_Off : Integer := -1;
            begin
               for B of ST.Bindings loop
                  if SU.To_String (B.Name) = "self" then
                     Self_Off := B.Offset;
                  end if;
               end loop;
               if Self_Off >= 0 then
                  Emit_Field_Drops (F, Tn, Natural (Self_Off));
               end if;
            end;
         end if;
      end;

      --  Bare epilogue: a `return` branches here after running its own
      --  inline scope-exit drops, so the fall-through drops above are not
      --  re-run on the return path.
      IO.Put_Line (F, SU.To_String (ST.Epilogue_Lbl) & "_bare:");
      IO.Put_Line (F, "    ldp     x29, x30, [sp]");
      IO.Put_Line (F, "    add     sp, sp, #" & Img (Frame_Bytes));
      IO.Put_Line (F, "    ret");

      if ST.Next_Offset > Natural (Frame_Bytes) then
         raise Program_Error with
           "codegen: fn '" & SU.To_String (Fn.Header.Name)
           & "' needs" & Natural'Image (ST.Next_Offset)
           & " bytes of frame (fixed frame is"
           & Integer'Image (Frame_Bytes) & ")";
      end if;

      Str_Base := ST.Next_Str_Idx;
   end Emit_Fn;
