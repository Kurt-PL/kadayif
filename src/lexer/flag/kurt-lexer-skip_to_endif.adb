separate (Kurt.Lexer)
   procedure Skip_To_Endif (L : in out Lexer; Else_Seen : Boolean) is
      Seen : Boolean := Else_Seen;
      D    : Flag_Dir;
   begin
      --  §10.8: L is positioned right after the `flag_else`/`flag_else_if`
      --  keyword that just ended the taken block branch (the caller has
      --  already consumed it as an ordinary token). Consume its `(cond)`
      --  when present; then a line-form branch (a mixed chain: its whole
      --  body sits on this line, closed by a lone `@`) is skipped here,
      --  while a block-form branch's body is scanned by the loop below.
      if not Else_Seen then
         --  It was `@flag_else_if`: consume its "(cond)"; the value is
         --  irrelevant — no branch after the taken one is ever entered.
         declare
            Discard : constant Boolean := Read_Paren_Cond (L);
            pragma Unreferenced (Discard);
         begin
            null;
         end;
      end if;
      if Line_Has_More_Tokens (L) then
         if not Cur_Line_Ends_With_At (L) then
            raise Translation_Failure with
              "a line-form `@flag` branch shall end with a lone `@` "
              & "(§10.8) at line" & Positive'Image (L.Line);
         end if;
         Skip_Line (L);   --  line-form: the inactive body is this line
      end if;
      --  Skip the chain's remaining branches — each independently line-
      --  or block-form (§10.8) — up to and including the `@flag_endif`
      --  this chain requires (it contains at least the taken block
      --  branch).
      loop
         D := Skip_Inactive_Branch (L);
         case D is
            when FD_Endif =>
               Skip_Line (L);
               return;
            when FD_Else | FD_Else_If =>
               if Seen then
                  raise Translation_Failure with
                    (if D = FD_Else
                     then "duplicate `@flag_else` in one chain"
                     else "`@flag_else_if` after `@flag_else`")
                    & " (§10.8) at line" & Positive'Image (L.Line);
               end if;
               if D = FD_Else then
                  Seen := True;
               else
                  declare
                     Discard : constant Boolean := Read_Paren_Cond (L);
                     pragma Unreferenced (Discard);
                  begin
                     null;
                  end;
               end if;
               if Line_Has_More_Tokens (L)
                 and then not Cur_Line_Ends_With_At (L)
               then
                  raise Translation_Failure with
                    "a line-form `@flag` branch shall end with a lone `@` "
                    & "(§10.8) at line" & Positive'Image (L.Line);
               end if;
               --  Line-form: its body is this line; block-form: its body
               --  follows. Either way the scan resumes past this line.
               Skip_Line (L);
            when others =>
               null;   --  unreachable: Skip_Inactive_Branch returns only
                       --  the enclosing chain's own directives
         end case;
      end loop;
   end Skip_To_Endif;
