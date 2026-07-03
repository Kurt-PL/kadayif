separate (Kurt.Parser)
   function Parse_Cast (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Unary (C);
   begin
      while C.Cur.Kind = Kw_As or else C.Cur.Kind = Kw_As_Bang loop
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_Cast);
            Bang : constant Boolean := C.Cur.Kind = Kw_As_Bang;  --  §6.8.11
         begin
            Advance (C);   --  consume `as` / `as!`
            Next.Cast_Inner := E;
            Next.Cast_Bang  := Bang;
            if C.Cur.Kind = Op_Question and then not Bang then
               Advance (C);
               Next.Cast_Disc := True;
               Next.Cast_Ty   := null;
            else
               Next.Cast_Ty := Parse_Type (C);
            end if;
            E := Next;
         end;
      end loop;
      return E;
   end Parse_Cast;
