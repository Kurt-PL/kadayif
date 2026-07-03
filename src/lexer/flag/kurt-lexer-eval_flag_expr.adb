separate (Kurt.Lexer)
   function Eval_Flag_Expr (L : Lexer; S : String) return Boolean is
      P : Natural := S'First;

      procedure Skip_Ws is
      begin
         while P <= S'Last and then (S (P) = ' ' or else S (P) = ASCII.HT)
         loop
            P := P + 1;
         end loop;
      end Skip_Ws;

      function Parse_Or return Boolean;

      function Parse_Atom return Boolean is
         R : Boolean;
      begin
         Skip_Ws;
         if P <= S'Last and then S (P) = '!' then
            P := P + 1;
            return not Parse_Atom;
         elsif P <= S'Last and then S (P) = '(' then
            P := P + 1;
            R := Parse_Or;
            Skip_Ws;
            if P <= S'Last and then S (P) = ')' then
               P := P + 1;
            end if;
            return R;
         else
            declare
               Start : constant Natural := P;
            begin
               while P <= S'Last
                 and then (Is_Ident_Continue (S (P)))
               loop
                  P := P + 1;
               end loop;
               if P = Start then
                  return False;   --  malformed; treat as false
               end if;
               return Flag_Set (L, S (Start .. P - 1));
            end;
         end if;
      end Parse_Atom;

      function Parse_And return Boolean is
         R : Boolean := Parse_Atom;
      begin
         loop
            Skip_Ws;
            if P + 1 <= S'Last and then S (P) = '&' and then S (P + 1) = '&'
            then
               P := P + 2;
               R := Parse_Atom and then R;   --  evaluate both (no short-circuit side effects)
            else
               exit;
            end if;
         end loop;
         return R;
      end Parse_And;

      function Parse_Or return Boolean is
         R : Boolean := Parse_And;
      begin
         loop
            Skip_Ws;
            if P + 1 <= S'Last and then S (P) = '|' and then S (P + 1) = '|'
            then
               P := P + 2;
               R := Parse_And or else R;
            else
               exit;
            end if;
         end loop;
         return R;
      end Parse_Or;
   begin
      return Parse_Or;
   end Eval_Flag_Expr;
