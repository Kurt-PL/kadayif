separate (Kurt.Parser)
   function Parse_Binary
     (C : in out Cursor; Min_BP : Natural) return Expr_Access
   is
      Left : Expr_Access := Parse_Cast (C);
      Op   : Binary_Op;
   begin
      while Token_To_Binop (C.Cur.Kind, Op) loop
         declare
            BP : constant Natural := Binding_Power (Op);
            Next : Expr_Access;
         begin
            exit when BP < Min_BP;
            Advance (C);
            --  Left-associative: parse RHS with strictly higher BP.
            declare
               R : constant Expr_Access := Parse_Binary (C, BP + 1);
               Next_Op : Binary_Op;
            begin
               --  §6.6/§6.4.3: comparison operators (all one shared tier)
               --  and each widening operator (`+@`, `*@`, its own tier) are
               --  non-associative. `a < b < c` / `a *@ b *@ c` shall be
               --  parenthesised, not chained.
               if Non_Assoc (Op)
                 and then Token_To_Binop (C.Cur.Kind, Next_Op)
                 and then Binding_Power (Next_Op) = BP
               then
                  raise Syntax_Error with
                    "this operator is non-associative (§6.4.3/§6.6); "
                    & "parenthesise the chain at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               --  §6.6 mixed comparison × bitwise/shift without parens.
               if Mixes_Cmp_Bitsh (Op, Left)
                 or else Mixes_Cmp_Bitsh (Op, R)
               then
                  raise Syntax_Error with
                    "a comparison mixed with a bitwise/shift operator "
                    & "requires explicit parentheses (§6.6) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Next := new Expr_Node (Kind => E_Binary);
               Next.B_Op  := Op;
               Next.B_Lhs := Left;
               Next.B_Rhs := R;
               Left := Next;
            end;
         end;
      end loop;
      return Left;
   end Parse_Binary;
