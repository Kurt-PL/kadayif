with Declarations;
with Expressions;
with Idents;
with Parser;
with Tokens;

package body Statements is

   use AST;
   use Parser;
   use Tokens;
   use type Idents.Ident;

   function Starts_Label return Boolean is
     (Peek = T_Ident and then Peek (1) = P_Colon
      and then Peek (2) in P_LBrace | K_Loop | K_While | K_If | K_Match);

   function Starts_Control return Boolean is
     (Starts_Label
      or else Peek in P_LBrace | K_If | K_While | K_Loop | K_Airside
                    | K_Match | K_Return | K_Break | K_Continue | K_Express
      or else (Peek = K_Const and then Peek (1) in P_LBrace | P_Colon_Colon)
      or else (Peek in K_Xlat | K_Arbit and then Peek (1) = P_Question)
      or else Peek = K_Instruct
      or else (Peek = K_Contract and then Peek (1) not in T_Ident | P_Bang));

   --  label_ref = '.', ws, identifier ;
   function Parse_Label_Ref return Idents.Ident is
   begin
      if Peek = P_Dot and then Peek (1) = T_Ident then
         Advance;
         return Take_Ident;
      end if;
      return Idents.No_Ident;
   end Parse_Label_Ref;

   function Can_Start_Value return Boolean is
     (Peek not in P_Semi | P_RBrace | P_RParen | P_Comma | P_RBracket
                | K_Else | T_EOF);

   function Parse_Block return Node_Id is
      N     : Node := Fresh (N_Block);
      Items : Id_Vectors.Vector;
   begin
      Expect (P_LBrace);
      while Peek /= P_RBrace loop
         if Peek = T_EOF then
            Fail ("expected '}'");
         elsif Peek = K_Let then
            declare
               L : Node := Fresh (N_Let);
            begin
               Advance;
               L.Flags (F_Mut) := Skip (K_Mut);
               if Peek /= T_Ident or else Peek (1) not in P_Colon | P_Eq then
                  Unimplemented ("let patterns other than an identifier"
                                 & " (§4.11)");
               end if;
               L.Name := Take_Ident;
               if Skip (P_Colon) then
                  L.A := Declarations.Parse_Type;
               end if;
               if Skip (P_Eq) then
                  L.B := Expressions.Parse_Expression;
               end if;
               if Peek = K_Else then
                  Unimplemented ("let with else (§4.3.1)");
               end if;
               Expect (P_Semi);
               Items.Append (Add (L));
            end;
         elsif Declarations.Starts_Item then
            Unimplemented ("items within blocks (§4.1)");
         elsif Starts_Control then
            declare
               Block_Form : Boolean;
               E          : constant Node_Id := Parse_Control (Block_Form);
            begin
               Items.Append (E);
               if not Block_Form then
                  if Peek in P_Semi then
                     Advance;
                  else
                     --  제어 식 뒤에 연산이 이어지는 꼴은 아직 받지 않는다
                     Expect (P_Semi);
                  end if;
               end if;
            end;
         elsif Skip (P_Semi) then
            null;
         else
            Items.Append (Expressions.Parse_Expression);
            Expect (P_Semi);
         end if;
      end loop;
      Expect (P_RBrace);
      N.List := Make_List (Items);
      return Add (N);
   end Parse_Block;

   --  if_head, if_lead, else_branch / else_value (§7.3)
   function Parse_If (Ends_With_Block : out Boolean) return Node_Id is
      N : Node := Fresh (N_If);
   begin
      Expect (K_If);
      if Peek = K_Let then
         Unimplemented ("if let (§7.3.1)");
      end if;
      N.A := Expressions.Parse_Expression;
      if Peek = P_Arrow then
         Unimplemented ("payload binding on if (§7.3)");
      end if;

      declare
         Then_Form : constant Boolean := Skip (K_Then);
      begin
         N.B := (if Then_Form then Expressions.Parse_Expression
                 else Parse_Block);
         Ends_With_Block := not Then_Form;
         if Peek = K_Else then
            Advance;
            if Peek = P_Dot then
               Unimplemented ("payload binding on else (§7.3)");
            end if;
            if Peek = P_LBrace then
               N.C := Parse_Block;
               Ends_With_Block := True;
            elsif Peek = K_If then
               N.C := Parse_If (Ends_With_Block);
            else
               N.C := Expressions.Parse_Expression;
               Ends_With_Block := False;
            end if;
         elsif Then_Form then
            Fail ("expected 'else'");
         end if;
      end;
      return Add (N);
   end Parse_If;

   function Parse_Control (Ends_With_Block : out Boolean) return Node_Id is
      Label : Idents.Ident := Idents.No_Ident;
   begin
      Ends_With_Block := True;
      if Starts_Label then
         Label := Take_Ident;
         Expect (P_Colon);
      end if;

      case Peek is
         when P_LBrace =>
            declare
               B : constant Node_Id := Parse_Block;
            begin
               Nodes (Positive (B)).Name := Label;
               return B;
            end;

         when K_Airside =>
            declare
               N : Node := Fresh (N_Airside);
            begin
               Advance;
               N.A := Parse_Block;
               return Add (N);
            end;

         when K_If =>
            if Label /= Idents.No_Ident then
               Unimplemented ("labelled if (§7.9)");
            end if;
            return Parse_If (Ends_With_Block);

         when K_Loop =>
            declare
               N : Node := Fresh (N_Loop);
            begin
               Advance;
               N.Name := Label;
               N.A := Parse_Block;
               return Add (N);
            end;

         when K_While =>
            declare
               N : Node := Fresh (N_While);
            begin
               Advance;
               N.Name := Label;
               if Peek = K_Let then
                  Unimplemented ("while let (§7.5.1)");
               end if;
               N.A := Expressions.Parse_Expression;
               if Peek = P_Arrow then
                  Unimplemented ("payload binding on while (§7.5.1)");
               elsif Peek = K_Then then
                  Unimplemented ("while with then (§7.5.1)");
               end if;
               N.B := Parse_Block;
               if Peek = K_And and then Peek (1) = K_Then then
                  Unimplemented ("while continuation 'and then' (§7.5.1)");
               elsif Peek = K_Else then
                  Unimplemented ("while with else (§7.5.1)");
               end if;
               return Add (N);
            end;

         when K_Return =>
            declare
               N : Node := Fresh (N_Return);
            begin
               Advance;
               Ends_With_Block := False;
               if Can_Start_Value then
                  N.A := Expressions.Parse_Expression;
               end if;
               return Add (N);
            end;

         when K_Break =>
            declare
               N : Node := Fresh (N_Break);
            begin
               Advance;
               Ends_With_Block := False;
               N.Name := Parse_Label_Ref;
               if Can_Start_Value then
                  Unimplemented ("break with a value (§7.7)");
               end if;
               return Add (N);
            end;

         when K_Continue =>
            declare
               N : Node := Fresh (N_Continue);
            begin
               Advance;
               Ends_With_Block := False;
               N.Name := Parse_Label_Ref;
               return Add (N);
            end;

         when K_Express =>
            Unimplemented ("express (§7.8)");
         when K_Match =>
            Unimplemented ("match (§7.4)");
         when K_Const =>
            Unimplemented ("const blocks (§6.11)");
         when K_Xlat | K_Arbit =>
            Unimplemented ("xlat? and arbit? conditionals (§6.11)");
         when K_Instruct =>
            Unimplemented ("instruct blocks (§6.12)");
         when K_Contract =>
            Unimplemented ("contract extraction (§7.2.3)");
         when others =>
            Fail ("expected expression");
      end case;
   end Parse_Control;

end Statements;
