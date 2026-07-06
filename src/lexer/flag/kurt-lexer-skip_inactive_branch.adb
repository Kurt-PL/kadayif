separate (Kurt.Lexer)
   function Skip_Inactive_Branch (L : in out Lexer) return Flag_Dir is
      --  §10.8 nested-chain tracking within the inactive region. One
      --  character per open nested chain, innermost last: 'B' for a chain
      --  whose branches seen so far include a block branch (a matching
      --  `@flag_endif` is pending), 'L' for an all-line chain so far (it
      --  closes implicitly at the first line that does not continue it,
      --  or turns into 'B' when a block-form branch appears). This is the
      --  §10.8 implementation-requirements scan: directives at line start
      --  plus the line-branch closing `@`; no lexing of inactive text.
      Nest : SU.Unbounded_String;

      function Empty return Boolean is (SU.Length (Nest) = 0);
      function Top return Character is
        (SU.Element (Nest, SU.Length (Nest)));
      procedure Pop is
      begin
         SU.Head (Nest, SU.Length (Nest) - 1);
      end Pop;
   begin
      loop
         if At_End (L) then
            raise Translation_Failure with
              "unterminated `@flag_if` (missing `@flag_endif`)";
         end if;
         declare
            D : constant Flag_Dir := Peek_Line_Directive (L);
            --  A directive line is line-form when the lone `@` is its
            --  final non-whitespace character (§10.8).
            Is_Line : constant Boolean :=
              D /= FD_None and then Cur_Line_Ends_With_At (L);
         begin
            case D is
               when FD_None =>
                  if not Empty and then Top = 'L' then
                     Pop;   --  a non-directive line ends a nested line chain
                  end if;
                  Skip_Line (L);
               when FD_If =>
                  if not Empty and then Top = 'L' then
                     Pop;   --  a fresh chain ends the open line chain too
                  end if;
                  SU.Append (Nest, (if Is_Line then 'L' else 'B'));
                  Skip_Line (L);
               when FD_Else | FD_Else_If =>
                  if not Empty and then Top = 'L' then
                     --  continuation of the innermost nested line chain; a
                     --  block-form branch turns the chain into a block one
                     --  (its `@flag_endif` will close it).
                     if not Is_Line then
                        Pop;
                        SU.Append (Nest, 'B');
                     end if;
                     Skip_Line (L);
                  elsif Empty then
                     return D;   --  the enclosing chain's own directive
                  else
                     Skip_Line (L);   --  belongs to a nested block chain
                  end if;
               when FD_Endif =>
                  if not Empty and then Top = 'L' then
                     Pop;   --  the endif closes the open line chain first
                  end if;
                  if Empty then
                     return FD_Endif;   --  the enclosing chain's endif
                  end if;
                  Pop;
                  Skip_Line (L);
            end case;
         end;
      end loop;
   end Skip_Inactive_Branch;
