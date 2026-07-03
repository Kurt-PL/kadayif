separate (Kurt.Parser)
   procedure Parse_Ref_Modifiers
     (C        : in out Cursor;
      Volatile : in out Boolean;
      Store    : in out Ref_Store)
   is
      procedure Set_Store (S : Ref_Store) is
      begin
         if Store /= RS_None then
            raise Syntax_Error with
              "'mut', 'atomic' and 'guard' are mutually exclusive "
              & "(spec 8.1) at line" & Positive'Image (C.Cur.Line);
         end if;
         Store := S;
      end Set_Store;
   begin
      loop
         if C.Cur.Kind = Kw_Mut then
            Advance (C);
            Set_Store (RS_Mut);
         elsif C.Cur.Kind = Kw_Volatile then
            Advance (C);
            Volatile := True;
         elsif C.Cur.Kind = Kw_Atomic then
            Advance (C);
            Set_Store (RS_Atomic);
         elsif C.Cur.Kind = Kw_Guard then
            Advance (C);
            Set_Store (RS_Guard);
         else
            exit;
         end if;
      end loop;
   end Parse_Ref_Modifiers;
