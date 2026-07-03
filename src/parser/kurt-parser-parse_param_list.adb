separate (Kurt.Parser)
   procedure Parse_Param_List
     (C             : in out Cursor;
      Params        : out Param_Vectors.Vector;
      Allow_Unnamed : Boolean)
   is
   begin
      Expect (C, Punct_LParen, "'('");
      if C.Cur.Kind /= Punct_RParen then
         loop
            Params.Append (Parse_Param (C, Allow_Unnamed));
            --  §9.2: the self_param production fixes `self` as the FIRST
            --  parameter; a self parameter in any later position shall
            --  not appear.
            if Natural (Params.Length) > 1
              and then SU.To_String (Params.Last_Element.Name) = "self"
            then
               raise Syntax_Error with
                 "`self` shall be the first parameter (spec 9.2) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;
         end loop;
      end if;
      Expect (C, Punct_RParen, "')'");
   end Parse_Param_List;
