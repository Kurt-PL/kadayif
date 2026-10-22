with Expressions;
with Parser;
with Statements;
with Tokens;

package body Declarations is

   use AST;
   use Parser;
   use Tokens;

   function Starts_Item return Boolean is
     (case Peek is
        when K_Pub | K_Extern | K_Fn | K_Const | K_Static | K_Struct
           | K_Enum | K_Type | K_Use | K_Module | K_Impl | K_Protocol
           | D_Add | D_Dyn | D_Path | D_Symbol | D_Inline | D_No_Inline
           | T_Annotation =>
           True,
        when K_Variadic | K_Airside =>
           Peek (1) in K_Fn | K_Airside | P_LParen,
        when K_Contract =>
           Peek (1) in T_Ident | P_Bang,
        when K_Trap =>
           Peek (1) = P_LBrace,
        when others =>
           False);

   function Parse_Path (In_Type : Boolean) return Node_Id is
      Path : Node := Fresh (N_Path);
      Segs : Id_Vectors.Vector;
   begin
      loop
         declare
            Seg : Node := Fresh (N_Segment);
         begin
            case Peek is
               when T_Ident =>
                  Seg.Name := Take_Ident;
               when K_Super | K_Srcroot | K_Selftype =>
                  Unimplemented ("'" & Current_Text
                                 & "' path segments (§10.7)");
               when P_LParen =>
                  Unimplemented ("qualified path segments (§10.7)");
               when others =>
                  Fail ("expected path");
            end case;
            if In_Type and then Peek = P_LBracket then
               declare
                  Args : Id_Vectors.Vector;
               begin
                  Advance;
                  loop
                     Args.Append (Parse_Type);
                     exit when not Skip (P_Comma) or else Peek = P_RBracket;
                  end loop;
                  Expect (P_RBracket);
                  Seg.List := Make_List (Args);
               end;
            end if;
            Segs.Append (Add (Seg));
         end;
         exit when Peek /= P_Colon_Colon or else Peek (1) = K_Wild;
         Advance;
      end loop;
      Path.List := Make_List (Segs);
      return Add (Path);
   end Parse_Path;

   function Parse_Type return Node_Id is
   begin
      case Peek is
         when P_Amp | P_Dollar | P_Percent =>
            declare
               N : Node := Fresh (N_Ref_Type);
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
               if Peek = P_LBracket then
                  --  &[T] 는 slice 참조, &[T; N] 은 배열 참조
                  declare
                     Inner : constant Node_Id := Parse_Type;
                  begin
                     if Kind (Inner) = N_Slice_Type then
                        N.Kind := N_Slice_Type;
                        N.A := Nodes (Positive (Inner)).A;
                     else
                        N.A := Inner;
                     end if;
                  end;
               else
                  N.A := Parse_Type;
               end if;
               return Add (N);
            end;

         when P_LBracket =>
            --  [T; N]. 참조 없이 나온 [T]는 Parse_Type의 호출자
            --  (참조 타입)만 slice로 받아 준다.
            declare
               N : Node := Fresh (N_Array_Type);
            begin
               Advance;
               N.A := Parse_Type;
               if Skip (P_RBracket) then
                  N.Kind := N_Slice_Type;
                  return Add (N);
               end if;
               Expect (P_Semi);
               if Peek = P_Question then
                  Unimplemented ("inferred array length (§5.7)");
               end if;
               N.B := Expressions.Parse_Expression;
               Expect (P_RBracket);
               return Add (N);
            end;

         when P_Question =>
            declare
               N : constant Node := Fresh (N_Infer_Type);
            begin
               Advance;
               return Add (N);
            end;

         when P_Dot =>
            Unimplemented ("anonymous struct types (§5.8)");
         when K_Fn | K_Extern | K_Variadic | K_Airside =>
            Unimplemented ("subroutine pointer types (§5.10)");
         when K_Dyn =>
            Unimplemented ("protocol types (§9.6)");
         when others =>
            return Parse_Path (In_Type => True);
      end case;
   end Parse_Type;

   --  subroutine_def / subroutine_proto (§4.2, §10.5)
   function Parse_Subroutine (Is_Proto : Boolean; Pub : Boolean)
                              return Node_Id
   is
      N      : Node := Fresh (N_Fn);
      Params : Id_Vectors.Vector;
   begin
      N.Flags (F_Pub) := Pub;
      if Skip (K_Extern) then
         N.Flags (F_Extern) := True;
         if Skip (P_LParen) then
            N.Name2 := Take_Ident;
            Expect (P_RParen);
         end if;
      end if;
      if Peek = K_Variadic then
         if not Is_Proto then
            Unimplemented ("variadic subroutine definitions (§4.2.3)");
         end if;
         Advance;
         N.Flags (F_Variadic) := True;
      end if;
      if Skip (K_Airside) then
         N.Flags (F_Airside) := True;
      end if;
      Expect (K_Fn);
      N.Name := Take_Ident;
      if Peek = P_LBracket then
         Unimplemented ("generic declarations (§4.10)");
      end if;

      Expect (P_LParen);
      while Peek /= P_RParen loop
         declare
            P : Node := Fresh (N_Param);
         begin
            if Peek in K_Self | P_Amp | P_Dollar | P_Percent
              and then Peek (1) = K_Self
            then
               Unimplemented ("self parameters (§9.2)");
            end if;
            P.Flags (F_Mut) := Skip (K_Mut);
            if not Is_Proto or else
              (Peek = T_Ident and then Peek (1) = P_Colon)
            then
               P.Name := Take_Ident;
               Expect (P_Colon);
            end if;
            P.A := Parse_Type;
            Params.Append (Add (P));
         end;
         exit when not Skip (P_Comma);
      end loop;
      Expect (P_RParen);
      N.List := Make_List (Params);

      if Skip (P_Arrow) then
         if Peek = P_Bang then
            declare
               Never : constant Node := Fresh (N_Never_Type);
            begin
               Advance;
               N.A := Add (Never);
            end;
         else
            N.A := Parse_Type;
         end if;
      end if;
      if Peek = K_Routes then
         Unimplemented ("routes clauses (§8.1.2)");
      elsif Peek = K_With then
         Unimplemented ("with clauses on subroutines (§4.12)");
      end if;

      if Is_Proto then
         Expect (P_Semi);
      else
         N.B := Statements.Parse_Block;
      end if;
      return Add (N);
   end Parse_Subroutine;

   --  dyn_decl (§10.5)
   function Parse_Dyn return Node_Id is
      N     : Node := Fresh (N_Dyn);
      Items : Id_Vectors.Vector;
   begin
      Advance;
      N.Flags (F_Xlat) := Skip (K_Xlat);
      N.Flags (F_Pub) := Skip (K_Pub);
      N.Name := Take_Ident;
      Expect (P_LBrace);
      while Peek /= P_RBrace loop
         if Peek in D_Symbol | D_Inline | D_No_Inline | T_Annotation then
            Unimplemented ("item decorations (§4.15, §4.16, §4.17)");
         end if;
         declare
            Pub : constant Boolean := Skip (K_Pub);
         begin
            if Peek = K_Static then
               Unimplemented ("#dyn static declarations (§10.5)");
            end if;
            Items.Append (Parse_Subroutine (Is_Proto => True, Pub => Pub));
         end;
      end loop;
      Expect (P_RBrace);
      N.List := Make_List (Items);
      return Add (N);
   end Parse_Dyn;

   function Parse_Item return Node_Id is
   begin
      case Peek is
         when D_Symbol | D_Inline | D_No_Inline | T_Annotation =>
            Unimplemented ("item decorations (§4.15, §4.16, §4.17)");
         when D_Dyn =>
            return Parse_Dyn;
         when D_Add =>
            Unimplemented ("#add declarations (§10.4)");
         when D_Path =>
            Unimplemented ("#path declarations (§10.6)");
         when others =>
            null;
      end case;

      declare
         Pub : constant Boolean := Skip (K_Pub);
      begin
         case Peek is
            when K_Fn | K_Extern | K_Variadic | K_Airside =>
               return Parse_Subroutine (Is_Proto => False, Pub => Pub);
            when K_Const =>
               Unimplemented ("const declarations (§4.4)");
            when K_Static =>
               Unimplemented ("static declarations (§4.5)");
            when K_Struct =>
               Unimplemented ("struct declarations (§4.7)");
            when K_Enum =>
               Unimplemented ("enum declarations (§4.8)");
            when K_Contract =>
               Unimplemented ("contract declarations (§7.2)");
            when K_Type =>
               Unimplemented ("type aliases (§4.9)");
            when K_Use =>
               Unimplemented ("use declarations (§4.13.2)");
            when K_Module =>
               Unimplemented ("modules (§10.7)");
            when K_Impl =>
               Unimplemented ("implantations (§9.1)");
            when K_Protocol =>
               Unimplemented ("protocol declarations (§9.3)");
            when K_Instruct =>
               Unimplemented ("global instruct blocks (§4.14)");
            when K_Trap =>
               Unimplemented ("trap handlers (§7.10.1)");
            when others =>
               Fail ("expected item");
         end case;
      end;
   end Parse_Item;

end Declarations;
