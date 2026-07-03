separate (Kurt.Sema.Check)
   function Infer (E : Expr_Access; Expected : Type_Access)
      return Type_Access
   is
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
      function Infer_Variant_New return Type_Access is separate;
      function Infer_Field return Type_Access is separate;
   begin
      case E.Kind is
         when E_Int_Lit =>
            --  §3.4.1: a type suffix fixes the type; otherwise take
            --  the expected integer type, else default to saddr.
            --  §3.4.1 also permits an integer literal in a float
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
            return E.Sem_Ty;

         when E_Float_Lit =>
            --  §3.4.2: a suffix fixes the type; else an expected float
            --  type; else default fe11m52.
            if SU.Length (E.Float_Suffix) > 0 then
               E.Sem_Ty := Mk_Named (Canon_Float
                 (SU.To_String (E.Float_Suffix)));
            elsif Is_Float_Type (Expected) then
               E.Sem_Ty := Expected;
            else
               E.Sem_Ty := Mk_Named ("fe11m52");
            end if;
            return E.Sem_Ty;

         when E_Bool_Lit =>
            --  §3.4.3 bool literal: type is the built-in alias `bool`.
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
                                              Len  => 0));
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
               pragma Unreferenced (CT);
            begin
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
                  --  §2.6: dereferencing a `&raw` reference is an
                  --  airside-only operation. `&`/`$` derefs are landside.
                  if IT.Sigil = R_Raw and then In_Airside = 0 then
                     Error ("dereference of a `&raw` reference is "
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
               OT : constant Type_Access := Infer (E.U_Operand, Expected);
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
                     --  success and failure variants. The bootstrap
                     --  supports the self-inverse cases: bool, and any
                     --  contract enum whose two payloads are identical
                     --  (a declared `-> inv_type` pair is otherwise
                     --  required and not yet implemented).
                     if not Is_Contract_Ty (OT) then
                        Error ("unary '!' requires an integer or a "
                               & "`contract` operand, got '"
                               & Image (OT) & "'");
                     elsif SU.To_String (OT.Name) /= "bool" then
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
                                     & "(spec 7.2.1; bootstrap supports "
                                     & "the self-inverse case only)");
                           end if;
                        end;
                     end if;
                  end if;
               end if;
               E.Sem_Ty := OT;
               return OT;
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
               Saved : constant Type_Access := Express_Expected;
            begin
               Express_Expected := Expected;
               if E.AB_Airside then
                  In_Airside := In_Airside + 1;
               end if;
               Check_Block (E.AB_Stmts);
               if E.AB_Airside then
                  In_Airside := In_Airside - 1;
               end if;
               Express_Expected := Saved;
            end;
            if not E.AB_Stmts.Is_Empty
              and then E.AB_Stmts.Last_Element.Kind = S_Express
              and then E.AB_Stmts.Last_Element.Xp_Val /= null
            then
               E.Sem_Ty := E.AB_Stmts.Last_Element.Xp_Val.Sem_Ty;
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
               Found : Type_Access := null;

               --  Scan for a `break`-with-value that targets this loop:
               --  descend into `if`/`airside` bodies but not into a nested
               --  loop (whose breaks target the inner loop).
               procedure Scan (V : Stmt_Vectors.Vector) is
               begin
                  for I in V.First_Index .. V.Last_Index loop
                     declare
                        BS : constant Stmt_Access := V.Element (I);
                     begin
                        case BS.Kind is
                           when S_Break =>
                              if Found = null
                                and then BS.Brk_Val /= null
                              then
                                 Found := BS.Brk_Val.Sem_Ty;
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
               if Expected /= null and then not Is_Void_Type (Expected) then
                  E.Sem_Ty := Expected;
               else
                  Scan (E.Loop_Body);
                  E.Sem_Ty :=
                    (if Found /= null then Found else Mk_Named ("never"));
               end if;
            end;
            return E.Sem_Ty;
      end case;
   end Infer;
