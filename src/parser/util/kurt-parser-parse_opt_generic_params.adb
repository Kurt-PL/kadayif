separate (Kurt.Parser)
   procedure Parse_Opt_Generic_Params
     (C : in out Cursor; Params : out Path_Segments.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            Params.Append (Take_Ident (C, "generic parameter"));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params;
