separate (Kurt.Codegen)
   procedure Emit (U : Kurt.Parser.Translation_Unit; Out_Path : String) is
      F        : IO.File_Type;
      Pool     : String_Pool;
      Dyn_Syms : Dyn_Sym_Pkg.Vector;
      Fn_Rets  : Fn_Ret_Pkg.Vector;
      --  Every subroutine to emit. §7.10.1: when a `@trap` handler is
      --  declared it is synthesised as an ordinary void subroutine
      --  `_kurt_trap_handler` so string-pool collection, return-type
      --  classification, and lowering all treat it uniformly.
      All_Fns  : Fn_Vectors.Vector := U.Fns;

      --  §8.11: synthesise a destructor `<Nm>$drop` for a `with destruct {
      --  block }` type. Its `self` is `$selftype` — an exclusive reference to
      --  the object — so the block's `self.field` accesses go through it.
      procedure Add_Drop (Nm : String; Block : Stmt_Vectors.Vector) is
         D : Fn_Decl;
         P : Param;
      begin
         Unit_Drop_Types.Append (SU.To_Unbounded_String (Nm));
         P.Name       := SU.To_Unbounded_String ("self");
         P.Ty         := new AST_Type (Kind => T_Ref);
         P.Ty.Sigil   := R_Excl;
         P.Ty.Target  := new AST_Type (Kind => T_Named);
         P.Ty.Target.Name := SU.To_Unbounded_String (Nm);
         D.Header.Name := SU.To_Unbounded_String (Nm & "$drop");
         D.Header.Params.Append (P);
         D.Body_Stmts := Block;
         All_Fns.Append (D);
      end Add_Drop;
   begin
      --  §9.5-6: publish trait metadata for the dispatch machinery.
      Unit_Traits := U.Traits;

      --  §5.4: publish the static-binding table for name resolution in
      --  the lowering passes.
      Unit_Statics := U.Statics;

      Unit_Has_Trap_Handler := U.Has_Trap_Handler;
      if U.Has_Trap_Handler then
         declare
            H : Fn_Decl;
         begin
            H.Header.Name := SU.To_Unbounded_String ("kurt_trap_handler");
            H.Header.Return_Type := null;   --  void; the body diverges
            H.Body_Stmts := U.Trap_Handler;
            All_Fns.Append (H);
         end;
      end if;

      --  §8.11: emit a destructor for every type that satisfies `destruct`
      --  — whether by an explicit `with destruct { ... }` block or by
      --  propagation through a field/payload that itself satisfies destruct.
      --  Propagation-only types carry an empty user block; their `$drop`
      --  body is purely the field-destruction tail (Emit_Field_Drops).
      Unit_Drop_Types.Clear;
      for I in U.Structs.First_Index .. U.Structs.Last_Index loop
         declare
            S    : constant Struct_Decl := U.Structs.Element (I);
            Need : Boolean := S.Has_Destruct;
         begin
            for Fld of S.Fields loop
               if Kurt.Layout.Satisfies_Destruct (Fld.Ty) then
                  Need := True;
               end if;
            end loop;
            if Need then
               Add_Drop (SU.To_String (S.Name), S.Destruct_Block);
            end if;
         end;
      end loop;
      for I in U.Enums.First_Index .. U.Enums.Last_Index loop
         declare
            E    : constant Enum_Decl := U.Enums.Element (I);
            Need : Boolean := E.Has_Destruct;
         begin
            for V of E.Variants loop
               for Fld of V.Payload loop
                  if Kurt.Layout.Satisfies_Destruct (Fld.Ty) then
                     Need := True;
                  end if;
               end loop;
            end loop;
            if Need then
               Add_Drop (SU.To_String (E.Name), E.Destruct_Block);
            end if;
         end;
      end loop;

      --  Return-type table for every internal fn, so call sites can
      --  classify aggregate returns (AAPCS64).
      for I in All_Fns.First_Index .. All_Fns.Last_Index loop
         Fn_Rets.Append
           ((Name => All_Fns.Element (I).Header.Name,
             Ty   => All_Fns.Element (I).Header.Return_Type));
      end loop;

      --  Build the @dyn symbol table from every @dyn block in the unit.
      for I in U.Dyns.First_Index .. U.Dyns.Last_Index loop
         declare
            D : constant Dyn_Decl := U.Dyns.Element (I);
         begin
            for J in D.Items.First_Index .. D.Items.Last_Index loop
               declare
                  P : constant Fn_Proto := D.Items.Element (J);
               begin
                  Dyn_Syms.Append
                    ((Name        => P.Name,
                      Fixed_Args  => Natural (P.Params.Length),
                      Is_Variadic => P.Is_Variadic,
                      Symbol      => P.Symbol_Name));
               end;
            end loop;
         end;
      end loop;

      --  Pre-pass: collect every string literal in the order the
      --  lowering pass will encounter them.
      for I in All_Fns.First_Index .. All_Fns.Last_Index loop
         declare
            Fn : constant Fn_Decl := All_Fns.Element (I);
         begin
            for J in Fn.Body_Stmts.First_Index .. Fn.Body_Stmts.Last_Index
            loop
               Collect_Strings_In_Stmt (Fn.Body_Stmts.Element (J), Pool);
            end loop;
         end;
      end loop;

      IO.Create (F, IO.Out_File, Out_Path);
      IO.Put_Line (F, "// kadayif bootstrap output");
      IO.Put_Line (F, "// target: arm64-apple-darwin");

      Emit_String_Pool (F, Pool);

      IO.Put_Line (F, ".section __TEXT,__text,regular,pure_instructions");

      --  §5.13 top-level `asm { … }` blocks, emitted verbatim into the text
      --  section (declaration order, before the translated subroutines).
      for I in U.Top_Asm.First_Index .. U.Top_Asm.Last_Index loop
         declare
            Body_S : constant String := SU.To_String (U.Top_Asm.Element (I));
            Start  : Integer := Body_S'First;
         begin
            for K in Body_S'Range loop
               if Body_S (K) = ASCII.LF then
                  IO.Put_Line (F, Body_S (Start .. K - 1));
                  Start := K + 1;
               end if;
            end loop;
            if Start <= Body_S'Last then
               IO.Put_Line (F, Body_S (Start .. Body_S'Last));
            end if;
         end;
      end loop;

      declare
         Str_Base : Natural := 0;
      begin
         for I in All_Fns.First_Index .. All_Fns.Last_Index loop
            Emit_Fn (F, All_Fns.Element (I), Dyn_Syms, Fn_Rets, Str_Base);
         end loop;
      end;

      --  §9.5-6 dispatch tables. One static table per `impl T as Trait`,
      --  with the three-zone layout (header + method pointers). Zone B
      --  (supertraits) is empty in the bootstrap.
      if not U.Trait_Impls.Is_Empty then
         --  Shared no-op destructor — Zone A field 2 always holds a valid
         --  subroutine pointer (§9.6.1).
         IO.New_Line (F);
         IO.Put_Line (F, ".p2align 2");
         IO.Put_Line (F, "_kurt_noop_dtor:");
         IO.Put_Line (F, "    ret");

         IO.Put_Line (F, ".section __DATA,__const");
         for I in U.Trait_Impls.First_Index ..
                  U.Trait_Impls.Last_Index
         loop
            declare
               TI    : constant Trait_Impl := U.Trait_Impls.Element (I);
               TyN   : constant String := SU.To_String (TI.Ty_Name);
               TrN   : constant String := SU.To_String (TI.Trait_Name);
               Conc  : constant Type_Access :=
                 new AST_Type'(Kind => T_Named,
                               Name => TI.Ty_Name, Args => <>);
            begin
               --  §9.1 an inherent `impl` (no trait) has no dispatch table.
               if TrN = "" then goto Next_Impl; end if;
               IO.Put_Line (F, ".p2align 3");
               IO.Put_Line (F, "_Ldtable_" & TyN & "_" & TrN & ":");
               IO.Put_Line (F, "    .quad " & Img (Sizeof (Conc)));   --  [0]
               IO.Put_Line (F, "    .quad "
                 & Img (Kurt.Layout.Align_Of (Conc)));               --  [1]
               IO.Put_Line (F, "    .quad _kurt_noop_dtor");         --  [2]
               for T in U.Traits.First_Index .. U.Traits.Last_Index loop
                  if SU.To_String (U.Traits.Element (T).Name) = TrN then
                     declare
                        Tr : Trait_Decl renames U.Traits.Element (T);
                     begin
                        --  Zone B (§9.6.2): one reference per direct
                        --  supertrait, to that supertrait's own table for
                        --  the same concrete type.
                        for SI in Tr.Supertraits.First_Index ..
                                  Tr.Supertraits.Last_Index
                        loop
                           IO.Put_Line (F, "    .quad _Ldtable_" & TyN
                             & "_" & SU.To_String
                                       (Tr.Supertraits.Element (SI)));
                        end loop;
                        --  Zone C: one pointer per trait method, in
                        --  declaration order — `Type$Trait$method`.
                        for M in Tr.Methods.First_Index ..
                                 Tr.Methods.Last_Index
                        loop
                           IO.Put_Line (F, "    .quad _" & TyN & "$" & TrN
                             & "$"
                             & SU.To_String
                                 (Tr.Methods.Element (M).Sig.Name));
                        end loop;
                     end;
                  end if;
               end loop;
               <<Next_Impl>> null;
            end;
         end loop;
      end if;

      --  §5.4 static objects: translation-time-initialized data words.
      if not U.Statics.Is_Empty then
         IO.New_Line (F);
         IO.Put_Line (F, ".section __DATA,__data");
         for I in U.Statics.First_Index .. U.Statics.Last_Index loop
            declare
               function To_U64 is new Ada.Unchecked_Conversion
                 (Long_Float, Interfaces.Unsigned_64);
               function To_U32 is new Ada.Unchecked_Conversion
                 (Float, Interfaces.Unsigned_32);

               D    : constant Static_Decl := U.Statics.Element (I);
               Sz   : constant Natural := Sizeof (D.Ty);
               Neg  : constant Boolean :=
                 D.Init.Kind = E_Unary;
               Lit  : constant Expr_Access :=
                 (if Neg then D.Init.U_Operand else D.Init);
               Bits : Interfaces.Unsigned_64;
            begin
               case Lit.Kind is
                  when E_Int_Lit =>
                     declare
                        V : constant Long_Long_Integer :=
                          (if Neg then -Lit.Int_V else Lit.Int_V);
                     begin
                        Bits := Interfaces.Unsigned_64'Mod (V);
                     end;
                  when E_Float_Lit =>
                     declare
                        V : constant Long_Float :=
                          (if Neg then -Lit.Float_V else Lit.Float_V);
                     begin
                        if Sz = 4 then
                           Bits := Interfaces.Unsigned_64
                             (To_U32 (Float (V)));
                        else
                           Bits := To_U64 (V);
                        end if;
                     end;
                  when E_Bool_Lit =>
                     Bits := (if Lit.Bool_V then 1 else 0);
                  when others =>
                     raise Program_Error with
                       "codegen: unsupported static initializer";
               end case;
               --  Mask to the object width for the data directive.
               if Sz < 8 then
                  Bits := Interfaces."and"
                    (Bits,
                     Interfaces.Unsigned_64'Mod
                       (Long_Long_Integer (2) ** (8 * Sz) - 1));
               end if;
               IO.Put_Line (F, ".p2align "
                 & (case Sz is
                       when 1 => "0", when 2 => "1",
                       when 4 => "2", when others => "3"));
               IO.Put_Line (F, "_Kst_" & SU.To_String (D.Name) & ":");
               IO.Put_Line (F,
                 (case Sz is
                     when 1      => "    .byte ",
                     when 2      => "    .short ",
                     when 4      => "    .long ",
                     when others => "    .quad ")
                 & Interfaces.Unsigned_64'Image (Bits));
            end;
         end loop;
      end if;

      IO.Close (F);
   end Emit;
