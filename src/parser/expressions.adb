with Ada.Strings.Unbounded;
with Declarations;
with Parser;
with Scanner;
with Statements;
with Tokens;

package body Expressions is

   use AST;
   use Parser;
   use Tokens;

   --  §6.14의 이항 연산자 결합력. 클수록 강하다. 0은 이항 연산자 아님.
   type Assoc is (Leading, Non_Assoc);

   type Binding is record
      Power : Natural := 0;
      Kind  : Assoc   := Leading;
   end record;

   Cast_Power : constant := 17;

   function Binary_Binding (K : Token_Kind) return Binding is
     (case K is
        when P_Star | P_Slash | P_Percent | P_Star_Pipe | P_Slash_Pipe =>
           (16, Leading),
        when P_Star_At => (15, Non_Assoc),
        when P_Plus | P_Minus | P_Plus_Pipe | P_Minus_Pipe =>
           (14, Leading),
        when P_Plus_At => (13, Non_Assoc),
        when P_Shl | P_Shr => (12, Leading),
        when P_Amp => (11, Leading),
        when P_Caret => (10, Leading),
        when P_Pipe => (9, Leading),
        when P_Eq_Eq | P_Ne | P_Lt | P_Gt | P_Le | P_Ge => (8, Non_Assoc),
        when K_And => (7, Leading),
        when K_Xor => (6, Leading),
        when K_Or => (5, Leading),
        when P_Cas => (4, Non_Assoc),
        when P_Eq | P_Plus_Eq | P_Minus_Eq | P_Star_Eq | P_Slash_Eq
           | P_Percent_Eq | P_Plus_Pipe_Eq | P_Minus_Pipe_Eq
           | P_Star_Pipe_Eq | P_Slash_Pipe_Eq | P_Amp_Eq | P_Pipe_Eq
           | P_Caret_Eq | P_Shl_Eq | P_Shr_Eq =>
           (2, Non_Assoc),
        when others => (0, Leading));

   function Is_Assignment (K : Token_Kind) return Boolean is
     (Binary_Binding (K).Power = 2);

   function Parse_Binary (Min_Power : Natural) return Node_Id;

   function Literal (Kind : Node_Kind) return Node_Id is
      N : Node := Fresh (Kind);
   begin
      if Kind in N_Char_Lit | N_String_Lit then
         N.Text := Ada.Strings.Unbounded.To_Unbounded_String
           (Scanner.Literal_Content (Source, Current));
      else
         N.Text := Ada.Strings.Unbounded.To_Unbounded_String (Current_Text);
      end if;
      Advance;
      --  타입 접미사: [ ws, '~', ws, single_path ]  (§3.5.1)
      if Kind in N_Int_Lit | N_Float_Lit and then Skip (P_Tilde) then
         N.A := Declarations.Parse_Path (In_Type => True);
      end if;
      return Add (N);
   end Literal;

   --  '{' [ expression_list | field_init_list ] '}'
   function Construction_Items return List_Id is
      Items : Id_Vectors.Vector;
   begin
      Expect (P_LBrace);
      while Peek /= P_RBrace loop
         if Peek = P_Dot and then Peek (1) = T_Ident and then Peek (2) = P_Eq
         then
            declare
               F : Node := Fresh (N_Field_Init);
            begin
               Advance;
               F.Name := Take_Ident;
               Expect (P_Eq);
               F.A := Parse_Expression;
               Items.Append (Add (F));
            end;
         else
            Items.Append (Parse_Expression);
         end if;
         exit when not Skip (P_Comma);
      end loop;
      Expect (P_RBrace);
      return Make_List (Items);
   end Construction_Items;

   function Parse_Primary return Node_Id is
   begin
      case Peek is
         when T_Int =>
            return Literal (N_Int_Lit);
         when T_Float =>
            return Literal (N_Float_Lit);
         when T_Char =>
            return Literal (N_Char_Lit);
         when T_String | T_Raw_String =>
            return Literal (N_String_Lit);

         when T_Ident | K_Super | K_Srcroot | K_Selftype =>
            declare
               N : Node := Fresh (N_Name);
            begin
               N.A := Declarations.Parse_Path (In_Type => False);
               if Peek = P_Colon_Colon and then Peek (1) = K_Wild then
                  --  wild_construction (§6.2.4)
                  Advance;
                  Advance;
                  N.Kind := N_Wild_Construct;
               elsif Peek = P_Dot and then Peek (1) = P_LBrace then
                  --  composite_construction (§6.2.3)
                  Advance;
                  N.Kind := N_Construct;
                  N.Flags (F_Braces) := True;
                  N.List := Construction_Items;
               end if;
               return Add (N);
            end;

         when P_LParen =>
            Advance;
            declare
               E : constant Node_Id := Parse_Expression;
            begin
               if Peek = K_Impl then
                  Unimplemented ("qualified method invocation (§6.3.3)");
               end if;
               Expect (P_RParen);
               return E;
            end;

         when P_LBracket =>
            Unimplemented ("array construction (§6.2.5)");
         when P_Dot =>
            --  anon_struct_construction (§6.2.6)
            declare
               N : Node := Fresh (N_Anon);
            begin
               Advance;
               if Peek /= P_LBrace then
                  Fail ("expected '{'");
               end if;
               N.List := Construction_Items;
               if N.List.Count = 0 then
                  Fail ("an anonymous struct has at least one field");
               end if;
               return Add (N);
            end;
         when K_Self =>
            Unimplemented ("self (§9.2)");
         when K_Trap =>
            Unimplemented ("trap (§7.10)");
         when K_Uninit =>
            Unimplemented ("uninit (§6.2.7)");
         when K_Cellbits =>
            Unimplemented ("cellbits (§5.3.1)");
         when K_Volatile | K_Guard =>
            Unimplemented ("ordering fences (§8.4.3)");

         when others =>
            if Statements.Starts_Control then
               declare
                  Ignored : Boolean;
               begin
                  return Statements.Parse_Control (Ignored);
               end;
            end if;
            Fail ("expected expression");
      end case;
   end Parse_Primary;

   function Parse_Postfix (Operand : Node_Id) return Node_Id is
      E : Node_Id := Operand;
   begin
      loop
         case Peek is
            when P_LParen =>
               declare
                  N    : Node := Fresh (N_Call);
                  Args : Id_Vectors.Vector;
               begin
                  Advance;
                  N.A := E;
                  while Peek /= P_RParen loop
                     Args.Append (Parse_Expression);
                     exit when not Skip (P_Comma);
                  end loop;
                  Expect (P_RParen);
                  N.List := Make_List (Args);
                  E := Add (N);
               end;

            when P_Dot =>
               declare
                  N : Node := Fresh (N_Field);
               begin
                  Advance;
                  N.A := E;
                  if Peek = T_Int then
                     N.Text := Ada.Strings.Unbounded.To_Unbounded_String
                       (Current_Text);
                     Advance;
                  else
                     N.Name := Take_Ident;
                  end if;
                  if Peek in P_LParen | P_LBracket then
                     Unimplemented ("method invocation (§6.3.3)");
                  end if;
                  E := Add (N);
               end;

            when P_Question =>
               Unimplemented ("contract propagation (§6.3.4)");
            when P_LBracket =>
               Unimplemented ("generic arguments (§4.10)");
            when others =>
               return E;
         end case;
      end loop;
   end Parse_Postfix;

   --  전위 연산자 (§6.4)
   function Parse_Unary return Node_Id is
   begin
      case Peek is
         when P_Minus | P_Plus | P_Bang | P_Star =>
            declare
               N : Node := Fresh (N_Unary);
            begin
               N.Op := Peek;
               Advance;
               N.A := Parse_Unary;
               return Add (N);
            end;

         when P_Amp | P_Dollar | P_Percent =>
            declare
               N : Node := Fresh (N_Unary);
            begin
               N.Op := Peek;
               Advance;
               loop
                  case Peek is
                     when K_Volatile => N.Flags (F_Volatile) := True;
                     when K_Mut      => N.Flags (F_Mut) := True;
                     when K_Atomic   => N.Flags (F_Atomic) := True;
                     when K_Guard    => N.Flags (F_Guard) := True;
                     when others     => exit;
                  end case;
                  Advance;
               end loop;
               N.A := Parse_Unary;
               return Add (N);
            end;

         when others =>
            return Parse_Postfix (Parse_Primary);
      end case;
   end Parse_Unary;

   function Parse_Binary (Min_Power : Natural) return Node_Id is
      Left      : Node_Id := Parse_Unary;
      Last_Non  : Natural := 0;  --  직전에 쓴 비결합 연산자의 결합력
   begin
      loop
         if Peek = K_As and then Cast_Power >= Min_Power then
            declare
               N : Node := Fresh (N_Cast);
            begin
               Advance;
               N.A := Left;
               N.Flags (F_Reinterpret) := Skip (P_Bang);
               N.B := Declarations.Parse_Type;
               Left := Add (N);
            end;
         else
            declare
               Op : constant Token_Kind := Peek;
               B  : constant Binding := Binary_Binding (Op);
            begin
               exit when B.Power = 0 or else B.Power < Min_Power;
               if B.Kind = Non_Assoc and then Last_Non = B.Power then
                  Fail ("operator '" & Spelling (Op)
                        & "' is not associative");
               end if;
               if Op = P_Cas then
                  Unimplemented ("compare-and-swap (§8.6)");
               end if;
               declare
                  N : Node := Fresh
                    (if Is_Assignment (Op) then N_Assign else N_Binary);
               begin
                  Advance;
                  N.Op := Op;
                  N.A := Left;
                  N.B := Parse_Binary (B.Power + 1);
                  Left := Add (N);
               end;
               Last_Non := (if B.Kind = Non_Assoc then B.Power else 0);
            end;
         end if;
      end loop;
      return Left;
   end Parse_Binary;

   function Parse_Expression return Node_Id is (Parse_Binary (1));

end Expressions;
