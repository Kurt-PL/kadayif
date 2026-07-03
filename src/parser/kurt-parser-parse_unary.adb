separate (Kurt.Parser)
   function Parse_Unary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
   begin
      if C.Cur.Kind = Op_Star then
         Advance (C);
         E := new Expr_Node (Kind => E_Deref);
         E.D_Inner := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Amp then
         --  §8.1 reference creation. Prefix position only — the infix
         --  bitwise `&` is consumed by Parse_Binary before reaching here.
         declare
            Amp_Line : constant Positive := C.Cur.Line;
            Amp_Col  : constant Positive := C.Cur.Col;
         begin
            Advance (C);
            E := new Expr_Node (Kind => E_Ref);
            E.Rf_Sigil := R_Shared;
            --  §8.1 `&raw` is a single fused token — see Parse_Type.
            if C.Cur.Kind = Tok_Ident
              and then SU.To_String (C.Cur.Lexeme) = "raw"
              and then C.Cur.Line = Amp_Line
              and then C.Cur.Col = Amp_Col + 1
            then
               Advance (C);
               E.Rf_Sigil := R_Raw;
            end if;
         end;
         Parse_Ref_Modifiers (C, E.Rf_Volatile, E.Rf_Store);
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Dollar then
         Advance (C);
         E := new Expr_Node (Kind => E_Ref);
         E.Rf_Sigil := R_Excl;
         declare
            Vol   : Boolean   := False;
            Store : Ref_Store := RS_None;
         begin
            Parse_Ref_Modifiers (C, Vol, Store);
            if Store /= RS_None then
               raise Syntax_Error with
                 "'$' is inherently storable; 'mut'/'atomic'/'guard' shall "
                 & "not appear after it (spec 8.1) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E.Rf_Volatile := Vol;
         end;
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Minus then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Neg;
         E.U_Operand := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Bang then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Not;
         E.U_Operand := Parse_Unary (C);
         return E;
      else
         return Parse_Postfix (C, Parse_Primary (C));
      end if;
   end Parse_Unary;
