separate (Kurt.Parser)
   function Parse_Fn_Decl (C : in out Cursor) return Fn_Decl is
      F : Fn_Decl;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => False, H => F.Header);
      --  §5.15: `@symbol` on a definition requires the `extern` prefix
      --  (a non-extern subroutine has no external name to override).
      if SU.Length (F.Header.Symbol_Name) > 0
        and then not F.Header.Is_Extern
      then
         raise Syntax_Error with
           "`@symbol` requires `extern` (or a `@dyn` block) (spec 5.15) at "
           & "line" & Positive'Image (C.Cur.Line);
      end if;
      Parse_Block_Stmts (C, F.Body_Stmts);
      return F;
   end Parse_Fn_Decl;
