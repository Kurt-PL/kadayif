separate (Kurt.Parser)
   function Parse_Param
     (C : in out Cursor; Allow_Unnamed : Boolean) return Param
   is
      P : Param;
   begin
      --  §5.1 `mut name: T` — a mutable parameter binding. The `mut` modifier
      --  is local to the body; it does not affect the signature.
      if C.Cur.Kind = Kw_Mut then
         Advance (C);
         P.Is_Mut := True;
      end if;
      --  §9.2 self parameter: `&self` / `$self`. The referent is the
      --  placeholder `selftype`, substituted with the impl type by
      --  Parse_Impl_Decl.
      if (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar)
        and then Peek_Tok (C).Kind = Kw_Self
      then
         --  §9.2 self_param: `mut` and a reference sigil are mutually
         --  exclusive alternatives — `mut &self` shall not appear.
         if P.Is_Mut then
            raise Syntax_Error with
              "`mut` and a reference sigil are mutually exclusive on "
              & "`self` (spec 9.2) at line" & Positive'Image (C.Cur.Line);
         end if;
         declare
            Sigil : constant Ref_Sigil :=
              (if C.Cur.Kind = Op_Amp then R_Shared else R_Excl);
         begin
            Advance (C);   --  sigil
            Advance (C);   --  self
            P.Name := SU.To_Unbounded_String ("self");
            P.Ty   := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil  := Sigil;
            P.Ty.Target := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String ("selftype");
            return P;
         end;
      end if;
      if C.Cur.Kind = Tok_Ident then
         declare
            Saved : constant SU.Unbounded_String := C.Cur.Lexeme;
         begin
            Advance (C);
            if C.Cur.Kind = Punct_Colon then
               Advance (C);
               P.Name := Saved;
               P.Ty   := Parse_Type (C);
               return P;
            elsif Allow_Unnamed then
               --  The identifier we already consumed was the head of a
               --  bare-type expression: synthesize a named type from it.
               P.Name := SU.Null_Unbounded_String;
               P.Ty   := new AST_Type (Kind => T_Named);
               P.Ty.Name := Saved;
               return P;
            else
               raise Syntax_Error with
                 "expected ':' after parameter name, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
            end if;
         end;
      elsif Allow_Unnamed
        and then (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar
                  or else C.Cur.Kind = Kw_Dyn
                  or else C.Cur.Kind = Punct_LBracket
                  --  §4.10 unnamed subroutine-pointer-typed parameter.
                  or else C.Cur.Kind = Kw_Fn
                  or else C.Cur.Kind = Kw_Extern
                  or else C.Cur.Kind = Kw_Variadic
                  or else C.Cur.Kind = Kw_Airside)
      then
         P.Name := SU.Null_Unbounded_String;
         P.Ty   := Parse_Type (C);
         return P;
      else
         raise Syntax_Error with
           "expected parameter, got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Param;
