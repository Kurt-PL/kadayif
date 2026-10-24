with Ada.Strings.Unbounded;
with Expressions;
with Idents;
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
      pragma Unreferenced (In_Type);
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
            if Peek = P_LBracket then
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
            declare
               N     : Node := Fresh (N_Anon_Type);
               Types : Id_Vectors.Vector;
            begin
               Advance;
               Expect (P_LBrace);
               loop
                  Types.Append (Parse_Type);
                  exit when not Skip (P_Comma) or else Peek = P_RBrace;
               end loop;
               Expect (P_RBrace);
               N.List := Make_List (Types);
               return Add (N);
            end;
         when K_Fn | K_Extern | K_Variadic | K_Airside =>
            Unimplemented ("subroutine pointer types (§5.10)");
         when K_Dyn =>
            Unimplemented ("protocol types (§9.6)");
         when others =>
            return Parse_Path (In_Type => True);
      end case;
   end Parse_Type;

   --  route_path = { '*' }, [ '...' ], ( identifier | "self" | dec_literal )
   function Parse_Route_Path (Is_Target : Boolean) return Node_Id is
      P     : Node := Fresh (N_Route_Path);
      Stars : Natural := 0;
   begin
      if Peek = K_Static then
         Advance;
         P.Flags (F_Static) := True;
         return Add (P);
      elsif Is_Target and then Peek = K_Return then
         Advance;
         P.Flags (F_Return) := True;
         return Add (P);
      end if;
      while Skip (P_Star) loop
         Stars := Stars + 1;
      end loop;
      P.Flags (F_Ellipsis) := Skip (P_Ellipsis);
      case Peek is
         when T_Ident =>
            P.Name := Take_Ident;
         when K_Self =>
            Advance;
            P.Flags (F_Self) := True;
         when T_Int =>
            P.Text := Ada.Strings.Unbounded.To_Unbounded_String (Current_Text);
            Advance;
         when others =>
            Fail ("expected a parameter");
      end case;
      P.Sym := Stars;
      return Add (P);
   end Parse_Route_Path;

   --  routes_clause (§8.1.2)
   function Parse_Routes return Node_Id is
      N      : Node := Fresh (N_Routes);
      Routes : Id_Vectors.Vector;
   begin
      Expect (K_Routes);
      Expect (P_LParen);
      loop
         declare
            R       : Node := Fresh (N_Route);
            Sources : Id_Vectors.Vector;
         begin
            loop
               Sources.Append (Parse_Route_Path (Is_Target => False));
               exit when not Skip (P_Plus);
            end loop;
            Expect (P_Arrow);
            R.A := Parse_Route_Path (Is_Target => True);
            R.List := Make_List (Sources);
            Routes.Append (Add (R));
         end;
         exit when not Skip (P_Comma) or else Peek = P_RParen;
      end loop;
      Expect (P_RParen);
      N.List := Make_List (Routes);
      return Add (N);
   end Parse_Routes;

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
         N.C := Parse_Routes;
      end if;
      if Peek = K_With then
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

   function Is_Context_Word (Word : String) return Boolean is
     (Peek = T_Ident and then Current_Text = Word);

   --  with_single / with_curly (§4.12)
   function Parse_With return Node_Id is
      N     : Node := Fresh (N_With);
      Items : Id_Vectors.Vector;

      function Parse_With_Item return Node_Id is
         I : Node := Fresh (N_With_Item);
      begin
         if Peek = K_Copyable or else Peek = K_Variadic then
            I.Name := Idents.Intern (Current_Text);
            Advance;
         elsif Peek = K_Impl then
            Unimplemented ("subject bounds (§9.4.2)");
         elsif Is_Context_Word ("inv") then
            I.Name := Take_Ident;
            Expect (P_Arrow);
            I.A := Parse_Type;
         elsif Is_Context_Word ("discrim") then
            I.Name := Take_Ident;
            Expect (P_LParen);
            I.A := Parse_Type;
            Expect (P_RParen);
         elsif Is_Context_Word ("align") then
            I.Name := Take_Ident;
            Expect (P_LParen);
            I.A := Expressions.Parse_Expression;
            Expect (P_RParen);
         elsif Is_Context_Word ("repr") then
            I.Name := Take_Ident;
            Expect (P_LParen);
            if Is_Context_Word ("pack") then
               I.Name2 := Take_Ident;
               Expect (P_LParen);
               I.A := Expressions.Parse_Expression;
               Expect (P_RParen);
            else
               I.Name2 := Take_Ident;
            end if;
            Expect (P_RParen);
         elsif Is_Context_Word ("destruct") then
            Unimplemented ("destructors (§8.8)");
         else
            Fail ("expected with item");
         end if;
         return Add (I);
      end Parse_With_Item;

   begin
      Expect (K_With);
      if Skip (P_LBrace) then
         loop
            Items.Append (Parse_With_Item);
            exit when not Skip (P_Comma) or else Peek = P_RBrace;
         end loop;
         Expect (P_RBrace);
         N.Flags (F_Braces) := True;
      else
         Items.Append (Parse_With_Item);
      end if;
      N.List := Make_List (Items);
      return Add (N);
   end Parse_With;

   --  composite_form (§4.6). Named는 이름 있는 필드 형태인지.
   procedure Parse_Composite_Form (Fields : out List_Id; Named : out Boolean)
   is
      Items : Id_Vectors.Vector;
      Ahead : Natural := 0;
   begin
      Expect (P_LBrace);
      while Peek (Ahead) in K_Pub | K_Airside | K_Mut loop
         Ahead := Ahead + 1;
      end loop;
      Named := (Peek (Ahead) = T_Ident and then Peek (Ahead + 1) = P_Colon)
        or else Peek (Ahead) = P_Question;
      loop
         declare
            F : Node := Fresh (N_Field_Decl);
         begin
            loop
               case Peek is
                  when K_Pub     => F.Flags (F_Pub) := True;
                  when K_Airside => F.Flags (F_Airside) := True;
                  when K_Mut     => F.Flags (F_Mut) := True;
                  when others    => exit;
               end case;
               Advance;
            end loop;
            if Named then
               if Skip (P_Question) then
                  F.Flags (F_Pad) := True;
               else
                  F.Name := Take_Ident;
               end if;
               Expect (P_Colon);
            end if;
            F.A := Parse_Type;
            if Skip (P_Eq) then
               F.B := Expressions.Parse_Expression;
            end if;
            Items.Append (Add (F));
         end;
         exit when not Skip (P_Comma) or else Peek = P_RBrace;
      end loop;
      Expect (P_RBrace);
      Fields := Make_List (Items);
   end Parse_Composite_Form;

   --  [ with_single, ';' | with_curly ]
   procedure Parse_Trailing_With (N : in out Node; Required_Semi : Boolean)
   is
   begin
      if Peek = K_With then
         N.C := Parse_With;
         if not Nodes (Positive (N.C)).Flags (F_Braces) then
            Expect (P_Semi);
         end if;
      elsif Required_Semi then
         Expect (P_Semi);
      end if;
   end Parse_Trailing_With;

   --  struct_decl (§4.7)
   function Parse_Struct (Pub : Boolean) return Node_Id is
      N : Node := Fresh (N_Struct);
   begin
      N.Flags (F_Pub) := Pub;
      Expect (K_Struct);
      N.Name := Take_Ident;
      if Peek = P_LBracket then
         Unimplemented ("generic declarations (§4.10)");
      end if;
      if Peek = P_LBrace then
         declare
            Named : Boolean;
         begin
            Parse_Composite_Form (N.List, Named);
            N.Flags (F_Named) := Named;
         end;
         Parse_Trailing_With (N, Required_Semi => False);
      else
         N.Flags (F_Unit) := True;
         Parse_Trailing_With (N, Required_Semi => True);
      end if;
      return Add (N);
   end Parse_Struct;

   --  discrim_value = [ sign, ws ], integer_literal ;  부호는 철자에 붙인다
   function Parse_Discrim_Value return Node_Id is
      N    : Node := Fresh (N_Int_Lit);
      Sign : String := " ";
   begin
      if Peek in P_Minus | P_Plus then
         Sign := (if Peek = P_Minus then "-" else " ");
         Advance;
      end if;
      if Peek /= T_Int then
         Fail ("expected integer literal");
      end if;
      N.Text := Ada.Strings.Unbounded.To_Unbounded_String
        ((if Sign = "-" then "-" else "") & Current_Text);
      Advance;
      if Peek = P_Tilde then
         Unimplemented ("type suffixes on discriminant values (§4.8)");
      end if;
      return Add (N);
   end Parse_Discrim_Value;

   --  variant (§4.8)
   function Parse_Variant return Node_Id is
      V : Node := Fresh (N_Variant);
   begin
      V.Name := Take_Ident;
      if Peek = P_LBrace then
         declare
            Named : Boolean;
         begin
            Parse_Composite_Form (V.List, Named);
            V.Flags (F_Named) := Named;
         end;
      else
         V.Flags (F_Unit) := True;
      end if;
      if Skip (P_Eq) then
         if Skip (K_Wild) then
            V.Flags (F_Wild) := True;
            if Skip (P_LParen) then
               V.A := Parse_Discrim_Value;
               Expect (P_RParen);
            end if;
         else
            V.A := Parse_Discrim_Value;
         end if;
      end if;
      return Add (V);
   end Parse_Variant;

   --  enum_decl (§4.8), contract_decl (§7.2)
   function Parse_Variant_Type (Pub : Boolean) return Node_Id is
      Is_Contract : constant Boolean := Peek = K_Contract;
      N : Node := Fresh (if Is_Contract then N_Contract else N_Enum);
      Variants : Id_Vectors.Vector;
   begin
      N.Flags (F_Pub) := Pub;
      Advance;
      if Is_Contract then
         N.Flags (F_Inverted) := Skip (P_Bang);
      end if;
      N.Name := Take_Ident;
      if Peek = P_LBracket then
         Unimplemented ("generic declarations (§4.10)");
      end if;
      Expect (P_LBrace);
      while Peek /= P_RBrace loop
         Variants.Append (Parse_Variant);
         exit when not Skip (P_Comma);
      end loop;
      Expect (P_RBrace);
      N.List := Make_List (Variants);
      Parse_Trailing_With (N, Required_Semi => False);
      return Add (N);
   end Parse_Variant_Type;

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
               return Parse_Struct (Pub);
            when K_Enum | K_Contract =>
               return Parse_Variant_Type (Pub);
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
