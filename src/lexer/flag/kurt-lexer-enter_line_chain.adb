separate (Kurt.Lexer)
   procedure Enter_Line_Chain (L : in out Lexer; First_Cond : Boolean) is
      Cond      : Boolean := First_Cond;
      Else_Seen : Boolean := False;
      --  §10.8: whether the chain has a block branch so far. A chain with
      --  a block branch requires `@flag_endif`; an all-line chain forbids
      --  it. Discovered incrementally as the branches are scanned.
      Has_Block : Boolean := False;
   begin
      Outer : loop
         if Cond then
            --  Take this line-form branch: the body runs to the closing
            --  `@`; the main token loop consumes the chain's remainder
            --  from there (Skip_Line_Chain_Rest, driven by these fields).
            L.Line_Close     := Find_Line_Close (L);
            L.Line_Else_Seen := Else_Seen;
            L.Line_Has_Block := Has_Block;
            return;
         end if;
         Skip_Line (L);   --  skip this inactive line branch (body+`@`+LF)
         declare
            Save : constant Positive := L.Pos;
            D    : Flag_Dir := Peek_Line_Directive (L);
         begin
            Inner : loop
               case D is
                  when FD_None | FD_If =>
                     --  The chain ended (a fresh `@flag_if` opens a new
                     --  one); no branch was taken.
                     if Has_Block then
                        raise Translation_Failure with
                          "missing `@flag_endif`: a `@flag` chain "
                          & "containing a block branch requires one "
                          & "(§10.8) at line" & Positive'Image (L.Line);
                     end if;
                     L.Pos := Save;   --  leave the line for the main loop
                     return;
                  when FD_Endif =>
                     if not Has_Block then
                        raise Translation_Failure with
                          "`@flag_endif` shall not appear in an "
                          & "all-line-branch chain (§10.8) at line"
                          & Positive'Image (L.Line);
                     end if;
                     Skip_Line (L);   --  consume it; no branch taken
                     return;
                  when FD_Else | FD_Else_If =>
                     if Else_Seen then
                        raise Translation_Failure with
                          (if D = FD_Else
                           then "duplicate `@flag_else` in one chain"
                           else "`@flag_else_if` after `@flag_else`")
                          & " (§10.8) at line" & Positive'Image (L.Line);
                     end if;
                     if D = FD_Else then
                        Else_Seen := True;
                        Cond := True;
                     else
                        Cond := Read_Paren_Cond (L);
                     end if;
                     if Line_Has_More_Tokens (L) then
                        --  §10.8 line-form branch.
                        if not Cur_Line_Ends_With_At (L) then
                           raise Translation_Failure with
                             "a line-form `@flag` branch shall end with a "
                             & "lone `@` (§10.8) at line"
                             & Positive'Image (L.Line);
                        end if;
                        exit Inner;   --  the outer loop takes or skips it
                     end if;
                     --  §10.8 mixed chain: a block-form branch within a
                     --  chain that began with a line branch.
                     Has_Block := True;
                     if Cond then
                        Skip_Line (L);   --  into the body
                        SU.Append (L.Chain_Stack,
                                   (if D = FD_Else then 'e' else 'i'));
                        return;
                     end if;
                     --  Inactive block branch: scan past its body to the
                     --  chain's next directive and process that one.
                     D := Skip_Inactive_Branch (L);
               end case;
            end loop Inner;
         end;
      end loop Outer;
   end Enter_Line_Chain;
