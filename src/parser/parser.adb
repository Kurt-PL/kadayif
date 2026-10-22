with Declarations;
with Diagnostics;
with Scanner;

package body Parser is

   use Tokens;

   Src  : Strip.Stripped;
   Toks : Scanner.Token_Vectors.Vector;
   Cur  : Positive := 1;

   function Peek (Ahead : Natural := 0) return Token_Kind is
     (if Cur + Ahead <= Toks.Last_Index then Toks (Cur + Ahead).Kind
      else T_EOF);

   function Current return Token is (Toks (Cur));

   procedure Advance is
   begin
      if Cur < Toks.Last_Index then
         Cur := Cur + 1;
      end if;
   end Advance;

   function Skip (K : Token_Kind) return Boolean is
   begin
      if Peek = K then
         Advance;
         return True;
      end if;
      return False;
   end Skip;

   procedure Expect (K : Token_Kind) is
   begin
      if Peek /= K then
         Fail ("expected '" & Spelling (K) & "'");
      end if;
      Advance;
   end Expect;

   function Here return Source_Map.Source_Pos is
     (Scanner.Position (Src, Current));

   function Current_Text return String is
     (Scanner.Spelling (Src, Current));

   function Take_Ident return Idents.Ident is
   begin
      if Peek /= T_Ident then
         Fail ("expected identifier");
      end if;
      declare
         T    : constant Token := Current;
         Text : constant String := Scanner.Spelling (Src, T);
      begin
         Advance;
         if T.Raw then
            return Idents.Intern (Text (Text'First + 2 .. Text'Last));
         end if;
         return Idents.Intern (Text);
      end;
   end Take_Ident;

   procedure Fail (Message : String) is
   begin
      if Peek = T_EOF then
         Diagnostics.Error (Here, Message & ", found end of source unit");
      else
         Diagnostics.Error
           (Here, Message & ", found '" & Current_Text & "'");
      end if;
      raise Syntax_Error;
   end Fail;

   procedure Unimplemented (What : String) is
   begin
      Diagnostics.Unimplemented (Here, What);
      raise Syntax_Error;
   end Unimplemented;

   function Source return Strip.Stripped is (Src);

   function Fresh (Kind : AST.Node_Kind) return AST.Node is
      N : AST.Node;
   begin
      N.Kind := Kind;
      N.Pos := Here;
      return N;
   end Fresh;

   --  구문 오류가 난 항목을 통째로 건너뛴다: 항목 시작으로 되감고,
   --  첫 '{'와 짝이 맞는 '}' 또는 중괄호 밖의 ';'까지 넘긴다
   procedure Recover (Item_Start : Positive) is
      Depth : Integer := 0;
   begin
      Cur := Item_Start;
      loop
         case Peek is
            when T_EOF =>
               return;
            when P_LBrace =>
               Depth := Depth + 1;
            when P_RBrace =>
               Depth := Depth - 1;
               if Depth <= 0 then
                  Advance;
                  return;
               end if;
            when P_Semi =>
               if Depth = 0 then
                  Advance;
                  return;
               end if;
            when others =>
               null;
         end case;
         Advance;
      end loop;
   end Recover;

   function Parse (S : Strip.Stripped) return AST.Node_Id is
      Unit  : AST.Node;
      Items : AST.Id_Vectors.Vector;
   begin
      Src := S;
      Toks := Scanner.Run (S);
      Cur := 1;
      Unit := Fresh (AST.N_Unit);
      while Peek /= T_EOF loop
         declare
            Item_Start : constant Positive := Cur;
         begin
            Items.Append (Declarations.Parse_Item);
         exception
            when Syntax_Error =>
               Recover (Item_Start);
         end;
      end loop;
      Unit.List := AST.Make_List (Items);
      return AST.Add (Unit);
   end Parse;

end Parser;
