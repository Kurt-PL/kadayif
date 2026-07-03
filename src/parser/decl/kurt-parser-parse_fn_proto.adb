separate (Kurt.Parser)
   function Parse_Fn_Proto (C : in out Cursor) return Fn_Proto is
      H : Fn_Header;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => True, H => H);
      --  §5.14: inlining directives shall not apply to a prototype (a
      --  declaration without a body).
      if H.Is_Inline or else H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline`/`@no_inline` shall not be applied to a subroutine "
           & "prototype (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;
      Expect (C, Punct_Semi, "';' to terminate fn prototype");
      return H;
   end Parse_Fn_Proto;
