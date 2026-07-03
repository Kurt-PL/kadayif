separate (Kurt.Parser)
   function Parse_Closure
     (C : in out Cursor; Xfer : Boolean) return Expr_Access
   is
      E : constant Expr_Access := new Expr_Node (Kind => E_Closure);
   begin
      E.Clo_Xfer := Xfer;
      Expect (C, Op_Slash, "'/.' to open a closure");
      Expect (C, Punct_Dot, "'.' after '/' to open a closure");
      if C.Cur.Kind /= Op_Slash then
         loop
            declare
               PName : constant SU.Unbounded_String :=
                 Take_Ident (C, "closure parameter name");
               PTy   : Type_Access := null;
            begin
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  PTy := Parse_Type (C);
               end if;
               E.Clo_Params.Append ((Name => PName, Ty => PTy));
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
         end loop;
      end if;
      Expect (C, Op_Slash, "'/' to close the closure parameter list");

      if C.Cur.Kind = Punct_Arrow then
         Advance (C);
         E.Clo_Ret := Parse_Type (C);
         Parse_Block_Stmts (C, E.Clo_Body);
      elsif C.Cur.Kind = Punct_LBrace then
         Parse_Block_Stmts (C, E.Clo_Body);
      elsif C.Cur.Kind = Punct_LArrow then
         --  Short form `/.p/ <- e` desugars to `{ return e; }`.
         Advance (C);
         declare
            R : constant Stmt_Access := new Stmt_Node (Kind => S_Return);
         begin
            R.R_Val := Parse_Expr (C);
            E.Clo_Body.Append (R);
         end;
      else
         raise Syntax_Error with
           "expected '->', '{', or '<-' in a closure tail at line"
           & Positive'Image (C.Cur.Line);
      end if;
      return E;
   end Parse_Closure;
