separate (Kurt.Sema.Check)
   function Infer (E : Expr_Access; Expected : Type_Access;
                    Neg_Ctx : Boolean := False)
      return Type_Access
   is
      --  §3.5.1: the fixed-width range of a named integer type, for the
      --  literal fits-target check below. Returns False for a type name
      --  that is not a fixed-width integer (the check is then skipped).
      --  si8/ui8/si16/ui16/si32/ui32/saddr/uaddr are wide enough that no
      --  literal representable in Long_Long_Integer (the scanner's own
      --  internal limit, §3.5.1) can overflow them, so their bounds are
      --  simply Long_Long_Integer's own range.
      function Int_Lit_Range
        (Name : String; Lo, Hi : out Long_Long_Integer) return Boolean is
      begin
         if Name = "si1" then
            Lo := -128; Hi := 127;
         elsif Name = "ui1" then
            Lo := 0; Hi := 255;
         elsif Name = "si2" then
            Lo := -32768; Hi := 32767;
         elsif Name = "ui2" then
            Lo := 0; Hi := 65535;
         elsif Name = "si4" then
            Lo := -2147483648; Hi := 2147483647;
         elsif Name = "ui4" then
            Lo := 0; Hi := 4294967295;
         elsif Name = "si8" or else Name = "si16" or else Name = "si32"
           or else Name = "saddr"
         then
            Lo := Long_Long_Integer'First; Hi := Long_Long_Integer'Last;
         elsif Name = "ui8" or else Name = "ui16" or else Name = "ui32"
           or else Name = "uaddr"
         then
            Lo := 0; Hi := Long_Long_Integer'Last;
         else
            return False;
         end if;
         return True;
      end Int_Lit_Range;

      function Infer_Closure return Type_Access is separate;
      function Infer_Cast return Type_Access is separate;
      function Infer_Match return Type_Access is separate;
      function Infer_Struct_Lit return Type_Access is separate;
      function Infer_Binary return Type_Access is separate;
      function Infer_Call return Type_Access is separate;
      function Infer_Path return Type_Access is separate;
      function Infer_Type_Intrinsic return Type_Access is separate;
      function Infer_Array_Lit return Type_Access is separate;
      function Infer_CAS return Type_Access is separate;
      function Infer_Ref return Type_Access is separate;
      function Infer_Question return Type_Access is separate;
      function Infer_Extract return Type_Access is separate;
      function Infer_Variant_New return Type_Access is separate;
      function Infer_Field return Type_Access is separate;
   begin
      case E.Kind is
         when E_Int_Lit =>
            --  §3.5.1: a type suffix fixes the type; otherwise take
            --  the expected integer type, else default to saddr.
            --  §3.5.1 also permits an integer literal in a float
            --  context (e.g. `let x: fe8m23 = 42;` => 42.0).
            if SU.Length (E.Int_Suffix) > 0 then
               E.Sem_Ty := Mk_Named (SU.To_String (E.Int_Suffix));
            elsif Is_Integer_Type (Expected)
              or else Is_Float_Type (Expected)
            then
               E.Sem_Ty := Expected;
            else
               E.Sem_Ty := Mk_Named ("saddr");
            end if;
            --  §3.5.1: the literal's value shall fit its (suffixed or
            --  inferred/annotated) type. Neg_Ctx means this literal is the
            --  direct operand of a unary '-' (e.g. `-128`); the value that
            --  actually has to fit is the negated one.
            if E.Sem_Ty /= null and then E.Sem_Ty.Kind = T_Named then
               declare
                  Lo, Hi : Long_Long_Integer;
               begin
                  if Int_Lit_Range (SU.To_String (E.Sem_Ty.Name), Lo, Hi)
                  then
                     declare
                        V : constant Long_Long_Integer :=
                          (if Neg_Ctx then -E.Int_V else E.Int_V);
                     begin
                        if V < Lo or else V > Hi then
                           Error ("integer literal" & V'Image
                                  & " does not fit target type '"
                                  & Image (E.Sem_Ty) & "' (spec 3.5.1)");
                        end if;
                     end;
                  end if;
               end;
            end if;
            return E.Sem_Ty;

         when E_Float_Lit =>
            --  §3.5.2: a suffix fixes the type; else an expected float
            --  type; else default fe11m52.
            if SU.Length (E.Float_Suffix) > 0 then
               E.Sem_Ty := Mk_Named (Canon_Float
                 (SU.To_String (E.Float_Suffix)));
            elsif Is_Float_Type (Expected) then
               E.Sem_Ty := Expected;
            else
               E.Sem_Ty := Mk_Named ("fe11m52");
            end if;
            --  §3.5.2/§4.4.2: a written NaN payload shall fit within the
            --  resolved format's payload field (mantissa bits minus the
            --  quiet bit).
            if E.Float_Special = 1 then
               declare
                  N  : constant String := SU.To_String (E.Sem_Ty.Name);
                  PB : constant Natural :=
                    (if    N = "fe5m10"   then 9
                     elsif N = "fe8m7"    then 6
                     elsif N = "fe8m23"   then 22
                     elsif N = "fe11m52"  then 51
                     elsif N = "fe15m112" then 111
                     else                      235);   --  fe19m236
               begin
                  if PB < 63
                    and then E.Nan_Payload > 2 ** PB - 1
                  then
                     Error ("NaN payload" & E.Nan_Payload'Image
                            & " does not fit the" & Natural'Image (PB)
                            & "-bit payload field of '" & N
                            & "' (spec 3.5.2/4.4.2)");
                  end if;
               end;
            end if;
            return E.Sem_Ty;

         when E_Bool_Lit =>
            --  §3.5.3 bool literal: type is the built-in alias `bool`.
            E.Sem_Ty := Mk_Named ("bool");
            return E.Sem_Ty;

         when E_String_Lit =>
            --  Slice &[ui1] fat reference. NB §3.5.5 specifies the type
            --  as `&[ui1; N]` (a thin reference to a sized array), but the
            --  bootstrap represents a string literal as a fat slice
            --  (ptr+len, the `Len => 0` sentinel). Carrying the true N in
            --  the type would require switching the whole string-literal
            --  representation to a thin sized-array reference — deferred.
            E.Sem_Ty := Mk_Ref (R_Shared, False, RS_None,
                                new AST_Type'(Kind => T_Array,
                                              Elem => Mk_Named ("ui1"),
                                              Len  => 0,
                                              Len_Expr => null));
            return E.Sem_Ty;

         when E_Path =>
            return Infer_Path;
         when E_Field =>
            return Infer_Field;
         when E_Call =>
            return Infer_Call;
         when E_Binary =>
            return Infer_Binary;
         when E_If =>
            declare
               CT : constant Type_Access :=
                 Infer (E.I_Cond, Mk_Named ("bool"));
               TT : constant Type_Access := Infer (E.I_Then, Expected);
               --  §7.11: a diverging `then` contributes no type; steer the
               --  `else` by the surviving expected type, not by `never`.
               ET : constant Type_Access :=
                 Infer (E.I_Else,
                        (if Is_Never_Ty (TT) then Expected else TT));
            begin
               --  §7.3: the condition of a `then`/`else` expression form
               --  shall satisfy `contract` (bool, verdict, or an enum
               --  `with contract`); a truthy C-style condition is a TF.
               if not Is_Contract_Ty (CT) then
                  Error ("`if` condition must satisfy `contract` (bool, "
                         & "verdict, or an enum `with contract`); got '"
                         & Image (CT) & "' (spec 7.3)");
               end if;
               --  §7.11 unification: drop the diverging branch; the
               --  result type comes from the non-diverging one (or is
               --  itself `never` when both diverge).
               if Is_Never_Ty (TT) then
                  E.Sem_Ty := ET;
               elsif Is_Never_Ty (ET) then
                  E.Sem_Ty := TT;
               else
                  if not Same_Type (TT, ET) then
                     Error ("if branches have differing types: '"
                            & Image (TT) & "' vs '" & Image (ET)
                            & "' (§7.1)");
                  end if;
                  E.Sem_Ty := TT;
               end if;
               return E.Sem_Ty;
            end;

         when E_Deref =>
            declare
               IT : constant Type_Access := Infer (E.D_Inner, null);
            begin
               if Is_Ref (IT) then
                  --  §2.6: dereferencing a `%` reference is an
                  --  airside-only operation. `&`/`$` derefs are landside.
                  if IT.Sigil = R_Raw and then In_Airside = 0 then
                     Error ("dereference of a `%` reference is "
                            & "permitted only in an `airside` region "
                            & "(spec 2.6)");
                  end if;
                  --  §2.6: `&mut T` access (load and store) is an
                  --  airside-only operation. This E_Deref case is
                  --  reached both for an rvalue load (`*m`) and for a
                  --  store target (the S_Assign LHS is inferred here),
                  --  so a single gate covers both directions. `$`
                  --  (R_Excl) and plain `&`/atomic/guard are not in the
                  --  §2.6 list and are not gated here.
                  if IT.Sigil = R_Shared and then IT.R_Store = RS_Mut
                    and then In_Airside = 0
                  then
                     Error ("load/store through a `&mut T` reference is "
                            & "permitted only in an `airside` region "
                            & "(spec 2.6)");
                  end if;
                  E.Sem_Ty := IT.Target;
               else
                  Error ("dereference of non-reference type '"
                         & Image (IT) & "'");
                  E.Sem_Ty := null;
               end if;
               return E.Sem_Ty;
            end;

         when E_Struct_Lit =>
            return Infer_Struct_Lit;
         when E_Variant_New =>
            return Infer_Variant_New;
         when E_Match =>
            return Infer_Match;
         when E_Cast =>
            return Infer_Cast;
         when E_Unary =>
            --  §6.3.1 negation (numeric: int or float) / §6.5.3 bitwise
            --  NOT (integer) / §7.2.1 contract polarity inversion.
            declare
               OT : constant Type_Access :=
                 Infer (E.U_Operand, Expected,
                        Neg_Ctx => E.U_Op = U_Neg
                                   and then E.U_Operand.Kind = E_Int_Lit);
               Result_Ty : Type_Access := OT;
            begin
               if OT /= null then
                  if E.U_Op = U_Neg
                    and then not (Is_Integer_Type (OT)
                                  or else Is_Float_Type (OT)
                                  or else Generic_Arith_OK (OT))
                  then
                     Error ("unary '-' requires a numeric operand, got '"
                            & Image (OT) & "'");
                  elsif E.U_Op = U_Not
                    and then not Is_Integer_Type (OT)
                  then
                     --  §7.2.1: `!` on a contract value exchanges the
                     --  success and failure variants.
                     if not Is_Contract_Ty (OT) then
                        Error ("unary '!' requires an integer or a "
                               & "`contract` operand, got '"
                               & Image (OT) & "'");
                     elsif SU.To_String (OT.Name) = "bool" then
                        null;   --  self-inverse; Result_Ty = OT already.
                     elsif SU.To_String (OT.Name) = "verdict" then
                        --  §7.2/§4: the built-in `verdict.<T, F>` declares
                        --  `contract -> selftype.<F, T>` -- swap the two
                        --  type arguments (works whether or not T = F).
                        declare
                           Inv : constant Type_Access :=
                             new AST_Type (Kind => T_Named);
                        begin
                           Inv.Name := OT.Name;
                           if Natural (OT.Args.Length) = 2 then
                              Inv.Args.Append
                                (OT.Args.Element (OT.Args.Last_Index));
                              Inv.Args.Append
                                (OT.Args.Element (OT.Args.First_Index));
                           end if;
                           Result_Ty := Inv;
                        end;
                     else
                        declare
                           Decl_Inv : constant Type_Access :=
                             Kurt.Layout.Contract_Inv_Type (OT);
                        begin
                           if Decl_Inv /= null then
                              --  §7.2 declared inverted pair: the result
                              --  type is the pair (payload cross-match
                              --  already enforced at declaration time by
                              --  Validate_Enums).
                              Result_Ty := Decl_Inv;
                           else
                              --  No declared pair: permitted only when the
                              --  success/failure payloads are identical
                              --  (self-inverse case).
                              declare
                                 EN : constant String :=
                                   SU.To_String (OT.Name);
                                 SV : constant String :=
                                   Kurt.Layout.Contract_Success_Variant (EN);
                                 FV : constant String :=
                                   Kurt.Layout.Contract_Fail_Variant (EN);
                                 SC : constant Natural :=
                                   Kurt.Layout.Variant_Field_Count (EN, SV);
                                 FC : constant Natural :=
                                   Kurt.Layout.Variant_Field_Count (EN, FV);
                              begin
                                 if SC /= FC
                                   or else (SC > 0 and then not Same_Type
                                     (Kurt.Layout.Variant_Field_Type
                                        (OT, SV, 1),
                                      Kurt.Layout.Variant_Field_Type
                                        (OT, FV, 1)))
                                 then
                                    Error ("'!' on '" & Image (OT)
                                       & "' needs a declared inverted "
                                       & "pair -- asymmetric payloads "
                                       & "(spec 7.2.1)");
                                 end if;
                              end;
                           end if;
                        end;
                     end if;
                  end if;
               end if;
               E.Sem_Ty := Result_Ty;
               return Result_Ty;
            end;

         when E_Question =>
            return Infer_Question;
         when E_Tuple_Lit =>
            --  §6.1.7: type is .{T1, ..., TN} from element types. When an
            --  expected tuple type is in context, steer each element.
            declare
               Tup : constant Type_Access :=
                 new AST_Type (Kind => T_Tuple);
            begin
               for I in E.TL_Elems.First_Index .. E.TL_Elems.Last_Index
               loop
                  declare
                     Exp : Type_Access := null;
                     Eit : constant Expr_Access := E.TL_Elems.Element (I);
                  begin
                     if Expected /= null and then Expected.Kind = T_Tuple
                       and then I - E.TL_Elems.First_Index
                         < Natural (Expected.Elems.Length)
                     then
                        Exp := Expected.Elems.Element
                          (Expected.Elems.First_Index
                             + (I - E.TL_Elems.First_Index));
                     end if;
                     Tup.Elems.Append (Infer (Eit, Exp));
                  end;
               end loop;
               E.Sem_Ty := Tup;
               return Tup;
            end;

         when E_Ref =>
            return Infer_Ref;
         when E_Extract =>
            return Infer_Extract;
         when E_CAS =>
            return Infer_CAS;
         when E_Array_Lit =>
            return Infer_Array_Lit;
         when E_Dyn_Cast =>
            --  Synthesised by the coercion logic below; its type is
            --  the `&dyn Trait` it was annotated with at creation.
            return E.Sem_Ty;

         when E_Slice_Cast =>
            --  Synthesised by the coercion logic below; type is the
            --  `&[T]` it was annotated with at creation.
            return E.Sem_Ty;

         when E_Type_Intrinsic =>
            return Infer_Type_Intrinsic;
         when E_Uninit =>
            --  §6.1.8: `uninit` is valid only as the value of an
            --  assignment to a binding's object (handled in S_Let/S_Mut/
            --  S_Assign). Reaching it through ordinary inference means it
            --  appeared in some other position, which is ill-formed.
            Error ("`uninit` shall appear only as the value of an "
                   & "assignment to a binding (spec 6.1.8)");
            E.Sem_Ty := Expected;
            return Expected;

         when E_Closure =>
            return Infer_Closure;
         when E_Destruct =>
            --  §8.4/§8.11: `destruct(e)` runs e's destructor now;
            --  `undestruct(e)` reclaims e's storage without running it
            --  (airside only). Both consume the operand binding — a
            --  later use is a use-after-transfer failure. The result is
            --  `void`.
            declare
               IT      : constant Type_Access := Infer (E.DT_Inner, null);
               Is_Bind : constant Boolean :=
                 E.DT_Inner /= null and then E.DT_Inner.Kind = E_Path
                 and then Natural (E.DT_Inner.Segments.Length) = 1;
               Word    : constant String :=
                 (if E.DT_Undo then "`undestruct`" else "`destruct`");
            begin
               if not Is_Bind then
                  Error (Word & " operand shall be a binding (bootstrap)");
               elsif not Satisfies_Destruct (IT) then
                  Error (Word & " requires an operand whose type satisfies "
                         & "`destruct` (spec 8.11)");
               end if;
               if E.DT_Undo and then In_Airside = 0 then
                  Error ("`undestruct` shall appear only inside an "
                         & "`airside` block or `airside fn` body "
                         & "(spec 8.4)");
               end if;
               Maybe_Move (E.DT_Inner);
               E.Sem_Ty := Mk_Named ("void");
               return E.Sem_Ty;
            end;

         when E_Airside_Blk =>
            --  §6.9 `airside { ... }` block expression. The body is
            --  checked as an airside lexical scope; the block's type is
            --  the type of the trailing `express` value, or `void` when
            --  no `express` targets the block. (Bootstrap: only a
            --  trailing `express` yields the value.)
            declare
               Saved   : constant Type_Access := Express_Expected;
               Has_Lbl : constant Boolean := SU.Length (E.AB_Label) > 0;
            begin
               Express_Expected := Expected;
               In_Expr_Block := In_Expr_Block + 1;   --  §7.8 express target
               if Has_Lbl then
                  --  §7.9 the block's label is in scope for its body.
                  Label_Stack.Append ((Name => E.AB_Label, Is_Block => True));
               end if;
               if E.AB_Airside then
                  In_Airside := In_Airside + 1;
               end if;
               Check_Block (E.AB_Stmts);
               if E.AB_Airside then
                  In_Airside := In_Airside - 1;
               end if;
               if Has_Lbl then
                  Label_Stack.Delete_Last;
               end if;
               In_Expr_Block := In_Expr_Block - 1;
               Express_Expected := Saved;
            end;
            --  §7.9: a trailing `express 'l` types the block only when
            --  'l names THIS block (one naming an outer block exits it
            --  instead); a plain trailing `express` always does.
            if not E.AB_Stmts.Is_Empty
              and then E.AB_Stmts.Last_Element.Kind = S_Express
              and then E.AB_Stmts.Last_Element.Xp_Val /= null
              and then (SU.Length (E.AB_Stmts.Last_Element.Xp_Label) = 0
                        or else SU.To_String
                                  (E.AB_Stmts.Last_Element.Xp_Label)
                                = SU.To_String (E.AB_Label))
            then
               E.Sem_Ty := E.AB_Stmts.Last_Element.Xp_Val.Sem_Ty;
            elsif Stmts_Diverge (E.AB_Stmts) then
               --  §7.11: a block expression where control cannot reach
               --  the end (a diverging expression on every path) is
               --  itself diverging — it types as `never` and contributes
               --  no constraint to any type unification.
               E.Sem_Ty := Mk_Named ("never");
            else
               E.Sem_Ty := Mk_Named ("void");
            end if;
            return E.Sem_Ty;

         when E_Loop =>
            --  §7.7 `loop { … }` as an expression. The body is checked in
            --  a loop context; its type is the annotated (expected) type
            --  when known, otherwise the type of the first `break expr`
            --  targeting this loop, or `never` when no break carries a
            --  value (a diverging loop).
            declare
               Found      : Type_Access := null;
               Mismatched : Boolean := False;

               --  Scan for every `break`-with-value that targets this loop:
               --  descend into `if`/`airside` bodies but not into a nested
               --  loop (whose breaks target the inner loop). §7.7: every
               --  `break value` in the same loop shall agree in type -- the
               --  loop's type is otherwise ambiguous (which arm's value
               --  does the loop expression actually produce?). The first
               --  break-with-value fixes the loop's type; every later one
               --  is checked against it.
               procedure Scan (V : Stmt_Vectors.Vector) is
               begin
                  for I in V.First_Index .. V.Last_Index loop
                     declare
                        BS : constant Stmt_Access := V.Element (I);
                     begin
                        case BS.Kind is
                           when S_Break =>
                              if BS.Brk_Val /= null then
                                 if Found = null then
                                    Found := BS.Brk_Val.Sem_Ty;
                                 elsif not Mismatched
                                   and then not Same_Type
                                     (Found, BS.Brk_Val.Sem_Ty)
                                 then
                                    Mismatched := True;
                                    Error
                                      ("`break` value type '"
                                       & Image (BS.Brk_Val.Sem_Ty)
                                       & "' disagrees with this loop's "
                                       & "type '" & Image (Found)
                                       & "', fixed by an earlier `break` "
                                       & "(spec 7.7)");
                                 end if;
                              end if;
                           when S_If =>
                              Scan (BS.SI_Then);
                              Scan (BS.SI_Else);
                           when S_Airside_Block =>
                              Scan (BS.A_Stmts);
                           when others =>
                              null;   --  skip S_While (nested loop)
                        end case;
                     end;
                  end loop;
               end Scan;
            begin
               In_Loop := In_Loop + 1;
               Check_Block (E.Loop_Body);
               In_Loop := In_Loop - 1;
               --  Run unconditionally: agreement among the loop's own
               --  `break value`s is required (spec 7.7) whether or not an
               --  outer annotation also pins the loop's type.
               Scan (E.Loop_Body);
               if Expected /= null and then not Is_Void_Type (Expected) then
                  E.Sem_Ty := Expected;
               else
                  E.Sem_Ty :=
                    (if Found /= null then Found else Mk_Named ("never"));
               end if;
            end;
            return E.Sem_Ty;
      end case;
   end Infer;
