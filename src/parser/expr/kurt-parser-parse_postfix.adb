separate (Kurt.Parser)
   function Parse_Postfix (C : in out Cursor; Start : Expr_Access)
      return Expr_Access
   is
      Left : Expr_Access := Start;
   begin
      loop
         case C.Cur.Kind is
            when Punct_Dot =>
               Advance (C);
               declare
                  --  Struct/method field is an identifier; tuple field is
                  --  a non-negative integer literal (§4.7, §6.2.2).
                  Name : SU.Unbounded_String;
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Field);
               begin
                  if C.Cur.Kind = Tok_Int_Lit then
                     declare
                        Im : constant String := C.Cur.Int_V'Image;
                     begin  --  'Image of a non-negative has a leading space
                        Name := SU.To_Unbounded_String
                          (Im (Im'First + 1 .. Im'Last));
                     end;
                     Advance (C);
                  else
                     Name := Take_Ident (C, "field name or tuple index");
                  end if;
                  Next.F_Recv := Left;
                  Next.F_Name := Name;
                  Left := Next;
               end;

            when Op_Question =>
               --  §6.2.4 / §7.2.4: contract propagation. `e?` extracts the
               --  success payload of a contract value, or returns its
               --  failure value from the enclosing subroutine.
               Advance (C);
               declare
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Question);
               begin
                  Next.Q_Inner := Left;
                  Left := Next;
               end;

            when Punct_LParen =>
               Advance (C);
               declare
                  Args : Expr_Vectors.Vector;
                  Next : Expr_Access;
               begin
                  if C.Cur.Kind /= Punct_RParen then
                     loop
                        Args.Append (Parse_Expr (C));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RParen;
                     end loop;
                  end if;
                  Expect (C, Punct_RParen, "')'");
                  Next := new Expr_Node (Kind => E_Call);
                  Next.C_Callee := Left;
                  Next.C_Args   := Args;
                  Left := Next;
               end;

            when Punct_ColonColon =>
               --  §6.1.1 qualified path root `(T as Trait)::item…`: the left
               --  operand is a parenthesized `(T as Trait)` cast. Desugar to
               --  the path `T::item…` — the trait selects the impl namespace,
               --  and in the bootstrap an associated item mangles identically
               --  to `T$item`, so resolution is unambiguous. (The `T`-impl-
               --  `Trait` relationship is not separately re-validated here.)
               exit when Left.Kind /= E_Cast
                 or else not Left.Was_Paren
                 or else Left.Cast_Bang or else Left.Cast_Disc
                 or else Left.Cast_Inner = null
                 or else Left.Cast_Inner.Kind /= E_Path;
               declare
                  NP : constant Expr_Access := new Expr_Node (Kind => E_Path);
               begin
                  NP.Segments := Left.Cast_Inner.Segments;   --  T
                  NP.Path_Trait := Left.Cast_Ty.Name;        --  Trait
                  loop
                     Advance (C);   --  '::'
                     NP.Segments.Append
                       (Take_Ident (C, "name after '::' in qualified path"));
                     exit when C.Cur.Kind /= Punct_ColonColon;
                  end loop;
                  Left := NP;
               end;

            when others =>
               exit;
         end case;
      end loop;
      return Left;
   end Parse_Postfix;
