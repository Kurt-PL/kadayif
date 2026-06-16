package body Kurt.Parser is

   use Kurt.Lexer;

   ----------------------------------------------------------------------
   --  Token cursor
   ----------------------------------------------------------------------

   --  §5.8 type aliases registered so far (substituted at use sites
   --  during type parsing; bootstrap: non-generic, declare-before-use).
   type Alias_Entry is record
      Name   : SU.Unbounded_String;
      Target : Type_Access;
   end record;

   package Alias_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Alias_Entry);

   package Token_Vectors is new Ada.Containers.Vectors
     (Index_Type => Positive, Element_Type => Kurt.Lexer.Token);

   type Cursor is record
      Lex  : access Kurt.Lexer.Lexer;
      Cur  : Kurt.Lexer.Token;
      Lookahead : Token_Vectors.Vector;
      --  When set, a `path {` is NOT read as a struct literal — used
      --  while parsing if/while conditions, where `{` opens the body.
      --  (Same disambiguation Rust applies.)
      No_Struct_Lit : Boolean := False;
      Aliases : Alias_Vectors.Vector;
   end record;

   procedure Advance (C : in out Cursor) is
   begin
      if not C.Lookahead.Is_Empty then
         C.Cur := C.Lookahead.First_Element;
         C.Lookahead.Delete_First;
      else
         C.Cur := Next_Token (C.Lex.all);
      end if;
   end Advance;

   --  Token after C.Cur (without consuming it).
   function Peek_Tok (C : in out Cursor) return Kurt.Lexer.Token is
   begin
      if C.Lookahead.Is_Empty then
         C.Lookahead.Append (Next_Token (C.Lex.all));
      end if;
      return C.Lookahead.First_Element;
   end Peek_Tok;

   procedure Split_Shr_If_Present (C : in out Cursor) is
   begin
      if C.Cur.Kind = Op_Shr then
         C.Cur.Kind := Op_Gt;
         C.Cur.Lexeme := SU.To_Unbounded_String (">");
         declare
            Tok : Kurt.Lexer.Token;
         begin
            Tok.Kind := Op_Gt;
            Tok.Lexeme := SU.To_Unbounded_String (">");
            Tok.Line := C.Cur.Line;
            Tok.Col := C.Cur.Col + 1;
            C.Lookahead.Prepend (Tok);
         end;
      end if;
   end Split_Shr_If_Present;

   function Image (K : Token_Kind) return String is (Token_Kind'Image (K));

   function Image (T : Kurt.Lexer.Token) return String is
      (Image (T.Kind) & " '" & SU.To_String (T.Lexeme) & "'");

   procedure Expect (C : in out Cursor; K : Token_Kind; What : String) is
   begin
      if K = Op_Gt then
         Split_Shr_If_Present (C);
      end if;
      if C.Cur.Kind /= K then
         raise Syntax_Error with
           "expected " & What & " (" & Image (K) & "), got "
           & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line)
           & ", col"   & Positive'Image (C.Cur.Col);
      end if;
      Advance (C);
   end Expect;

   function Take_Ident (C : in out Cursor; What : String)
      return SU.Unbounded_String
   is
      Name : SU.Unbounded_String;
   begin
      if C.Cur.Kind /= Tok_Ident then
         raise Syntax_Error with
           "expected identifier (" & What & "), got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
      Name := C.Cur.Lexeme;
      Advance (C);
      return Name;
   end Take_Ident;

   ----------------------------------------------------------------------
   --  Types
   ----------------------------------------------------------------------

   --  Canonicalise floating-point type aliases to their fe{e}m{m} spelling
   --  (§4) so the rest of the compiler compares one name per type.
   function Canon_Float (N : String) return String is
     (if    N = "f16"  then "fe5m10"
      elsif N = "bf16" then "fe8m7"
      elsif N = "f32"  then "fe8m23"
      elsif N = "f64"  then "fe11m52"
      elsif N = "f128" then "fe15m112"
      elsif N = "f256" then "fe19m236"
      else  N);

   --  §8.1: consume the `[volatile] [mut|atomic|guard]` modifier sequence
   --  between a reference sigil and the referent. Shared by Parse_Type and
   --  the E_Ref prefix expression. The modifiers may appear in any order;
   --  `mut`/`atomic`/`guard` are pairwise mutually exclusive.
   procedure Parse_Ref_Modifiers
     (C        : in out Cursor;
      Volatile : in out Boolean;
      Store    : in out Ref_Store)
   is
      procedure Set_Store (S : Ref_Store) is
      begin
         if Store /= RS_None then
            raise Syntax_Error with
              "'mut', 'atomic' and 'guard' are mutually exclusive "
              & "(spec 8.1) at line" & Positive'Image (C.Cur.Line);
         end if;
         Store := S;
      end Set_Store;
   begin
      loop
         if C.Cur.Kind = Kw_Mut then
            Advance (C);
            Set_Store (RS_Mut);
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "volatile"
         then
            Advance (C);
            Volatile := True;
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "atomic"
         then
            Advance (C);
            Set_Store (RS_Atomic);
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "guard"
         then
            Advance (C);
            Set_Store (RS_Guard);
         else
            exit;
         end if;
      end loop;
   end Parse_Ref_Modifiers;

   function Parse_Type (C : in out Cursor) return Type_Access is
      Node : Type_Access;
   begin
      if C.Cur.Kind = Op_Amp then
         Advance (C);
         Node := new AST_Type (Kind => T_Ref);
         Node.Sigil := R_Shared;
         if C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "raw"
         then
            Advance (C);
            Node.Sigil := R_Raw;
         end if;
         Parse_Ref_Modifiers (C, Node.R_Volatile, Node.R_Store);
         Node.Target := Parse_Type (C);
         return Node;
      elsif C.Cur.Kind = Op_Dollar then
         Advance (C);
         Node := new AST_Type (Kind => T_Ref);
         Node.Sigil := R_Excl;
         --  §8.1: `$` is inherently storable — only `volatile` may follow.
         Parse_Ref_Modifiers (C, Node.R_Volatile, Node.R_Store);
         if Node.R_Store /= RS_None then
            raise Syntax_Error with
              "'$' is inherently storable; 'mut'/'atomic'/'guard' shall "
              & "not appear after it (spec 8.1) at line"
              & Positive'Image (C.Cur.Line);
         end if;
         Node.Target := Parse_Type (C);
         return Node;
      elsif C.Cur.Kind = Kw_Dyn then
         --  §9.5 trait object `dyn Trait` (appears as `&dyn Trait`).
         Advance (C);
         Node := new AST_Type (Kind => T_Dyn);
         Node.Trait_Name := Take_Ident (C, "trait name after 'dyn'");
         return Node;
      elsif C.Cur.Kind = Punct_LBracket then
         --  §4.6 array type: `[T; N]` fixed-size (Len = N) or `[T]`
         --  unsized slice (Len = 0, only valid as a reference target).
         Advance (C);
         Node := new AST_Type (Kind => T_Array);
         Node.Elem := Parse_Type (C);
         if C.Cur.Kind = Punct_Semi then
            Advance (C);
            if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
               raise Syntax_Error with
                 "array length must be a positive integer literal at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            Node.Len := Natural (C.Cur.Int_V);
            Advance (C);
         else
            Node.Len := 0;   --  unsized slice `[T]`
         end if;
         Expect (C, Punct_RBracket, "']' to close array type");
         return Node;
      elsif C.Cur.Kind = Punct_Dot then
         --  Tuple type `.{ T, T, … }` (§4.7).
         Advance (C);
         Expect (C, Punct_LBrace, "'{' after '.' in tuple type");
         Node := new AST_Type (Kind => T_Tuple);
         if C.Cur.Kind /= Punct_RBrace then
            loop
               Node.Elems.Append (Parse_Type (C));
               exit when C.Cur.Kind /= Punct_Comma;
               Advance (C);
               exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
            end loop;
         end if;
         Expect (C, Punct_RBrace, "'}' to close tuple type");
         return Node;
      elsif C.Cur.Kind = Tok_Ident then
         Node := new AST_Type (Kind => T_Named);
         Node.Name := SU.To_Unbounded_String
           (Canon_Float (SU.To_String (C.Cur.Lexeme)));
         Advance (C);
         --  Generic arguments: `Name.<T, U>`.
         if C.Cur.Kind = Punct_Dot then
            Advance (C);
            Expect (C, Op_Lt, "'<' after '.' in generic arguments");
            Split_Shr_If_Present (C);
            if C.Cur.Kind /= Op_Gt then
               loop
                  Node.Args.Append (Parse_Type (C));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  Split_Shr_If_Present (C);
                  exit when C.Cur.Kind = Op_Gt;
               end loop;
            end if;
            Expect (C, Op_Gt, "'>' to close generic arguments");
         end if;
         --  §4.8: the built-in range types are intrinsic — rewrite
         --  `range_ex.<T>` / `range_in.<T>` to the dedicated T_Range kind.
         declare
            NN : constant String := SU.To_String (Node.Name);
         begin
            if (NN = "range_ex" or else NN = "range_in")
              and then Natural (Node.Args.Length) = 1
            then
               return new AST_Type'
                 (Kind          => T_Range,
                  Rng_Inclusive => NN = "range_in",
                  Rng_Elem      => Node.Args.First_Element);
            end if;
         end;
         --  §5.8: a type-alias name is replaced by its underlying type
         --  at every use site before any further analysis. Bootstrap:
         --  non-generic aliases, declared before use.
         if Node.Args.Is_Empty then
            for I in C.Aliases.First_Index .. C.Aliases.Last_Index loop
               if SU."=" (C.Aliases.Element (I).Name, Node.Name) then
                  return C.Aliases.Element (I).Target;
               end if;
            end loop;
         end if;
         return Node;
      else
         raise Syntax_Error with
           "expected type expression, got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Type;

   --  Optional generic parameter clause on a subroutine (§5.9):
   --  `.< T [: bound { '+' bound }], … >`. Bounds are builtin bound
   --  names (§9.8) recorded for the type-erasure check in Kurt.Sema.
   procedure Parse_Opt_Generic_Params_Bounded
     (C : in out Cursor; Params : out Generic_Param_Vectors.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            declare
               P : Generic_Param;
            begin
               P.Name := Take_Ident (C, "generic parameter");
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  loop
                     P.Bounds.Append (Take_Ident (C, "bound name"));
                     exit when C.Cur.Kind /= Op_Plus;
                     Advance (C);
                  end loop;
               end if;
               Params.Append (P);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params_Bounded;

   --  Optional generic parameter clause on a declaration: `.<T, U>`.
   procedure Parse_Opt_Generic_Params
     (C : in out Cursor; Params : out Path_Segments.Vector)
   is
   begin
      if C.Cur.Kind /= Punct_Dot then
         return;
      end if;
      Advance (C);
      Expect (C, Op_Lt, "'<' after '.' in generic clause");
      Split_Shr_If_Present (C);
      if C.Cur.Kind /= Op_Gt then
         loop
            Params.Append (Take_Ident (C, "generic parameter"));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            Split_Shr_If_Present (C);
            exit when C.Cur.Kind = Op_Gt;
         end loop;
      end if;
      Expect (C, Op_Gt, "'>' to close generic clause");
   end Parse_Opt_Generic_Params;

   ----------------------------------------------------------------------
   --  Parameters
   ----------------------------------------------------------------------

   function Parse_Param
     (C : in out Cursor; Allow_Unnamed : Boolean) return Param
   is
      P : Param;
   begin
      --  §9.2 self parameter: `&self` / `$self`. The referent is the
      --  placeholder `self_t`, substituted with the impl type by
      --  Parse_Impl_Decl.
      if (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar)
        and then Peek_Tok (C).Kind = Tok_Ident
        and then SU.To_String (Peek_Tok (C).Lexeme) = "self"
      then
         declare
            Sigil : constant Ref_Sigil :=
              (if C.Cur.Kind = Op_Amp then R_Shared else R_Excl);
         begin
            Advance (C);   --  sigil
            Advance (C);   --  self
            P.Name := SU.To_Unbounded_String ("self");
            P.Ty   := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil  := Sigil;
            P.Ty.Target := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String ("self_t");
            return P;
         end;
      end if;
      if C.Cur.Kind = Tok_Ident then
         declare
            Saved : constant SU.Unbounded_String := C.Cur.Lexeme;
         begin
            Advance (C);
            if C.Cur.Kind = Punct_Colon then
               Advance (C);
               P.Name := Saved;
               P.Ty   := Parse_Type (C);
               return P;
            elsif Allow_Unnamed then
               --  The identifier we already consumed was the head of a
               --  bare-type expression: synthesize a named type from it.
               P.Name := SU.Null_Unbounded_String;
               P.Ty   := new AST_Type (Kind => T_Named);
               P.Ty.Name := Saved;
               return P;
            else
               raise Syntax_Error with
                 "expected ':' after parameter name, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
            end if;
         end;
      elsif Allow_Unnamed
        and then (C.Cur.Kind = Op_Amp or else C.Cur.Kind = Op_Dollar)
      then
         P.Name := SU.Null_Unbounded_String;
         P.Ty   := Parse_Type (C);
         return P;
      else
         raise Syntax_Error with
           "expected parameter, got " & Image (C.Cur)
           & " at line" & Positive'Image (C.Cur.Line);
      end if;
   end Parse_Param;

   procedure Parse_Param_List
     (C             : in out Cursor;
      Params        : out Param_Vectors.Vector;
      Allow_Unnamed : Boolean)
   is
   begin
      Expect (C, Punct_LParen, "'('");
      if C.Cur.Kind /= Punct_RParen then
         loop
            Params.Append (Parse_Param (C, Allow_Unnamed));
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;
         end loop;
      end if;
      Expect (C, Punct_RParen, "')'");
   end Parse_Param_List;

   ----------------------------------------------------------------------
   --  Expressions
   --
   --  Grammar layered as:
   --     Expr      = Binary
   --     Binary    = Postfix { binop Postfix }      Pratt by binding power
   --     Postfix   = Primary { '.' IDENT | '(' args ')' }
   --     Primary   = INT | STRING | path | '(' Expr ')'
   --               | "if" Expr "then" Expr "else" Expr
   --
   --  Precedence is taken from §6 (lower number = tighter binding).
   --  We convert to "binding power" where higher number = tighter.
   ----------------------------------------------------------------------

   function Parse_Expr (C : in out Cursor) return Expr_Access;

   function Token_To_Binop (K : Token_Kind; Op : out Binary_Op) return Boolean is
   begin
      case K is
         when Op_Plus     => Op := B_Add;
         when Op_Minus    => Op := B_Sub;
         when Op_Star     => Op := B_Mul;
         when Op_Slash    => Op := B_Div;
         when Op_Percent  => Op := B_Mod;
         when Op_PlusBar  => Op := B_Sat_Add;
         when Op_MinusBar => Op := B_Sat_Sub;
         when Op_StarBar  => Op := B_Sat_Mul;
         when Op_SlashBar => Op := B_Sat_Div;
         when Op_Amp      => Op := B_And;
         when Op_Bar      => Op := B_Or;
         when Op_Caret    => Op := B_Xor;
         when Op_Shl      => Op := B_Shl;
         when Op_Shr      => Op := B_Shr;
         when Op_PlusAt   => Op := B_Wide_Add;
         when Op_StarAt   => Op := B_Wide_Mul;
         when Op_EqEq    => Op := B_Eq;
         when Op_BangEq  => Op := B_Ne;
         when Op_Lt      => Op := B_Lt;
         when Op_Gt      => Op := B_Gt;
         when Op_Le      => Op := B_Le;
         when Op_Ge      => Op := B_Ge;
         when Op_AmpAmp  => Op := B_LAnd;
         when Op_BarBar  => Op := B_LOr;
         when others     => return False;
      end case;
      return True;
   end Token_To_Binop;

   --  Higher = tighter binding. Mirrors §6 precedence table:
   --    spec prec 7  (* / %)              => bp 70
   --    spec prec 8  (+ -)                => bp 60
   --    spec prec 13 (== != < > <= >=)    => bp 30
   function Binding_Power (Op : Binary_Op) return Natural is
   begin
      case Op is
         when B_Mul | B_Div | B_Mod | B_Sat_Mul | B_Sat_Div
            | B_Wide_Mul => return 70;
         when B_Add | B_Sub | B_Sat_Add | B_Sat_Sub
            | B_Wide_Add => return 60;
         when B_Shl | B_Shr => return 50;   --  §6 level 9
         when B_And         => return 45;   --  level 10
         when B_Xor         => return 40;   --  level 11
         when B_Or          => return 35;   --  level 12
         when B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge => return 30;  --  13
         when B_LAnd        => return 20;   --  §7.2.2, below comparison
         when B_LOr         => return 15;
      end case;
   end Binding_Power;

   function Parse_Primary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
   begin
      case C.Cur.Kind is
         when Tok_Int_Lit =>
            E := new Expr_Node (Kind => E_Int_Lit);
            E.Int_V      := C.Cur.Int_V;
            E.Int_Suffix := C.Cur.Int_Suffix;
            Advance (C);
            return E;

         when Kw_Uninit =>
            --  §6.1.8: uninitialized value. Its type is supplied by the
            --  enclosing assignment; sema enforces the airside-only and
            --  assignment-value-only constraints.
            E := new Expr_Node (Kind => E_Uninit);
            Advance (C);
            return E;

         when Tok_Char_Lit =>
            --  §3.5.4: a character literal denotes a single cell value
            --  of type ui1.
            E := new Expr_Node (Kind => E_Int_Lit);
            E.Int_V      := C.Cur.Int_V;
            E.Int_Suffix := SU.To_Unbounded_String ("ui1");
            Advance (C);
            return E;

         when Kw_Cellbits =>
            --  §4.2.1: `cellbits[::exec|::xlat]` evaluates to a `uaddr`
            --  value. Translation and execution environment cell widths
            --  are both 8 on this host/target, so every form is 8 (and
            --  the unqualified xlatime max(exec, xlat) is too).
            Advance (C);
            if C.Cur.Kind = Punct_ColonColon then
               Advance (C);
               declare
                  Q : constant String :=
                    SU.To_String (Take_Ident (C, "cellbits qualifier"));
               begin
                  if Q /= "exec" and then Q /= "xlat" then
                     raise Syntax_Error with
                       "cellbits qualifier shall be 'exec' or 'xlat' "
                       & "(spec 4.2.1) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end;
            end if;
            E := new Expr_Node (Kind => E_Int_Lit);
            E.Int_V      := 8;
            E.Int_Suffix := SU.To_Unbounded_String ("uaddr");
            return E;

         when Tok_Float_Lit =>
            E := new Expr_Node (Kind => E_Float_Lit);
            E.Float_V      := C.Cur.Float_V;
            E.Float_Suffix := C.Cur.Int_Suffix;
            Advance (C);
            return E;

         when Kw_True | Kw_False =>
            --  §3.4.3 bool literals (built-in constants of type bool).
            E := new Expr_Node (Kind => E_Bool_Lit);
            E.Bool_V := C.Cur.Kind = Kw_True;
            Advance (C);
            return E;

         when Punct_Dot =>
            --  Tuple literal `.{ e, e, … }` (§6.1.7).
            Advance (C);
            Expect (C, Punct_LBrace, "'{' after '.' in tuple literal");
            E := new Expr_Node (Kind => E_Tuple_Lit);
            if C.Cur.Kind /= Punct_RBrace then
               loop
                  E.TL_Elems.Append (Parse_Expr (C));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
               end loop;
            end if;
            Expect (C, Punct_RBrace, "'}' to close tuple literal");
            return E;

         when Tok_String_Lit =>
            E := new Expr_Node (Kind => E_String_Lit);
            E.Str_Bytes := C.Cur.Str_Bytes;
            Advance (C);
            return E;

         when Tok_Ident =>
            E := new Expr_Node (Kind => E_Path);
            E.Segments.Append (C.Cur.Lexeme);
            Advance (C);
            while C.Cur.Kind = Punct_ColonColon loop
               Advance (C);
               if C.Cur.Kind /= Tok_Ident then
                  raise Syntax_Error with
                    "expected identifier after '::', got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               E.Segments.Append (C.Cur.Lexeme);
               Advance (C);
            end loop;
            --  Explicit generic arguments `path.< T, … >` (§5.9.2). On a
            --  callee path they drive monomorphisation (Kurt.Mono); on a
            --  literal path (`Box.<si4> { … }`) the concrete type comes
            --  from context, so the captured args are simply unused.
            if C.Cur.Kind = Punct_Dot
              and then Peek_Tok (C).Kind = Op_Lt
            then
               Advance (C);   --  '.'
               Advance (C);   --  '<'
               Split_Shr_If_Present (C);
               if C.Cur.Kind /= Op_Gt then
                  loop
                     E.P_Type_Args.Append (Parse_Type (C));
                     exit when C.Cur.Kind /= Punct_Comma;
                     Advance (C);
                     Split_Shr_If_Present (C);
                     exit when C.Cur.Kind = Op_Gt;
                  end loop;
               end if;
               Expect (C, Op_Gt, "'>' to close generic arguments");
            end if;
            --  §6.12 type intrinsic: the parsed path names a *type* when
            --  followed by `@size` / `@align` / `@offset(field)`.
            --  Bootstrap subset: a single-segment named type.
            if C.Cur.Kind in Dir_At_Size | Dir_At_Align | Dir_At_Offset
            then
               if Natural (E.Segments.Length) /= 1
                 or else not E.P_Type_Args.Is_Empty
               then
                  raise Syntax_Error with
                    "type intrinsic operand shall be a plain named type "
                    & "(bootstrap) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               declare
                  TI : constant Expr_Access :=
                    new Expr_Node (Kind => E_Type_Intrinsic);
               begin
                  TI.TI_Ty := new AST_Type'
                    (Kind => T_Named,
                     Name => E.Segments.First_Element,
                     Args => Type_Vectors.Empty_Vector);
                  case C.Cur.Kind is
                     when Dir_At_Size  => TI.TI_Op := TI_Size;
                     when Dir_At_Align => TI.TI_Op := TI_Align;
                     when others       => TI.TI_Op := TI_Offset;
                  end case;
                  Advance (C);
                  if TI.TI_Op = TI_Offset then
                     Expect (C, Punct_LParen, "'('");
                     TI.TI_Field := Take_Ident (C, "field name");
                     Expect (C, Punct_RParen, "')'");
                  end if;
                  return TI;
               end;
            end if;
            if C.Cur.Kind = Punct_LBrace
              and then not C.No_Struct_Lit
              and then Natural (E.Segments.Length) in 1 .. 2
            then
               declare
                  Two  : constant Boolean :=
                    Natural (E.Segments.Length) = 2;
                  Lit  : constant Expr_Access :=
                    (if Two then new Expr_Node (Kind => E_Variant_New)
                            else new Expr_Node (Kind => E_Struct_Lit));
               begin
                  if Two then
                     Lit.VN_Enum    := E.Segments.First_Element;
                     Lit.VN_Variant := E.Segments.Last_Element;
                  else
                     Lit.SL_Name := E.Segments.Last_Element;
                  end if;
                  Advance (C);  --  consume '{'
                  if C.Cur.Kind /= Punct_RBrace then
                     --  §6.1.5 positional vs named: a leading `ident '='`
                     --  starts a named initialiser; anything else is
                     --  positional. Named form is allowed for both struct
                     --  literals and (struct-)variant construction. The
                     --  positional form is meaningful only for tuple
                     --  variants — but using it for a struct literal will
                     --  surface as a field-not-found error in sema.
                     declare
                        Named : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Eq;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              FI : Field_Init;
                           begin
                              if Named then
                                 FI.Name := Take_Ident (C, "field name");
                                 Expect (C, Punct_Eq, "'='");
                              else
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    FI.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Idx := Idx + 1;
                              end if;
                              FI.Val := Parse_Expr (C);
                              if Two then
                                 Lit.VN_Fields.Append (FI);
                              else
                                 Lit.SL_Fields.Append (FI);
                              end if;
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
                  return Lit;
               end;
            end if;
            return E;

         when Punct_LParen =>
            Advance (C);
            E := Parse_Expr (C);
            Expect (C, Punct_RParen, "')'");
            return E;

         when Kw_If =>
            --  §7.1 inline form: `if cond then a else b`. The block
            --  form is deferred.
            Advance (C);
            E := new Expr_Node (Kind => E_If);
            E.I_Cond := Parse_Expr (C);
            Expect (C, Kw_Then, "'then'");
            E.I_Then := Parse_Expr (C);
            Expect (C, Kw_Else, "'else'");
            E.I_Else := Parse_Expr (C);
            return E;

         when Kw_Match =>
            --  §7: match scrut { pattern = expr, … }
            --  Bootstrap: expression-bodied arms only.
            Advance (C);
            E := new Expr_Node (Kind => E_Match);
            --  Suppress struct-literal parsing so the following '{' opens
            --  the match body, not a struct literal.
            declare
               Saved : constant Boolean := C.No_Struct_Lit;
            begin
               C.No_Struct_Lit := True;
               E.M_Scrut := Parse_Expr (C);
               C.No_Struct_Lit := Saved;
            end;
            Expect (C, Punct_LBrace, "'{'");
            while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF
            loop
               declare
                  Arm : Match_Arm;
               begin
                  --  pattern
                  case C.Cur.Kind is
                     when Tok_Hash_Wild =>
                        Arm.Pat.Kind := Pat_Wild;
                        Advance (C);
                     when Tok_Int_Lit =>
                        Arm.Pat.Kind  := Pat_Int;
                        Arm.Pat.Int_V := C.Cur.Int_V;
                        Advance (C);
                     when Tok_Ident =>
                        Arm.Pat.Kind := Pat_Variant;
                        Arm.Pat.Path.Append (C.Cur.Lexeme);
                        Advance (C);
                        while C.Cur.Kind = Punct_ColonColon loop
                           Advance (C);
                           Arm.Pat.Path.Append
                             (Take_Ident (C, "variant name"));
                        end loop;
                        --  Optional payload destructuring `{ a, b }`
                        --  (positional binding names).
                        if C.Cur.Kind = Punct_LBrace then
                           Advance (C);
                           if C.Cur.Kind /= Punct_RBrace then
                              loop
                                 Arm.Pat.Bindings.Append
                                   (Take_Ident (C, "payload binding"));
                                 exit when C.Cur.Kind /= Punct_Comma;
                                 Advance (C);
                                 exit when C.Cur.Kind = Punct_RBrace;
                              end loop;
                           end if;
                           Expect (C, Punct_RBrace, "'}'");
                        end if;
                     when others =>
                        raise Syntax_Error with
                          "expected match pattern, got " & Image (C.Cur)
                          & " at line" & Positive'Image (C.Cur.Line);
                  end case;
                  Expect (C, Punct_Eq, "'=' in match arm");
                  Arm.Arm_Body := Parse_Expr (C);
                  E.M_Arms.Append (Arm);
                  --  §3.2: comma separates expression-bodied arms.
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
               end;
            end loop;
            Expect (C, Punct_RBrace, "'}'");
            return E;

         when Punct_LBracket =>
            --  §6.1.6 array literal `[a, b, c]` or repeat `[v; N]`.
            Advance (C);
            E := new Expr_Node (Kind => E_Array_Lit);
            if C.Cur.Kind = Punct_RBracket then
               raise Syntax_Error with
                 "array literal needs at least one element at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E.AL_Elems.Append (Parse_Expr (C));
            if C.Cur.Kind = Punct_Semi then
               --  repeat form: the single element fills N slots.
               Advance (C);
               if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
                  raise Syntax_Error with
                    "repeat count must be a positive integer literal at "
                    & "line" & Positive'Image (C.Cur.Line);
               end if;
               E.AL_Repeat := Natural (C.Cur.Int_V);
               Advance (C);
            else
               while C.Cur.Kind = Punct_Comma loop
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBracket;  --  trailing comma
                  E.AL_Elems.Append (Parse_Expr (C));
               end loop;
            end if;
            Expect (C, Punct_RBracket, "']' to close array literal");
            return E;

         when others =>
            raise Syntax_Error with
              "expected primary expression, got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
      end case;
   end Parse_Primary;

   function Parse_Postfix (C : in out Cursor; Start : Expr_Access)
      return Expr_Access
   is
      Left : Expr_Access := Start;
   begin
      loop
         case C.Cur.Kind is
            when Punct_Dot =>
               Advance (C);
               declare
                  --  Struct/method field is an identifier; tuple field is
                  --  a non-negative integer literal (§4.7, §6.2.2).
                  Name : SU.Unbounded_String;
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Field);
               begin
                  if C.Cur.Kind = Tok_Int_Lit then
                     declare
                        Im : constant String := C.Cur.Int_V'Image;
                     begin  --  'Image of a non-negative has a leading space
                        Name := SU.To_Unbounded_String
                          (Im (Im'First + 1 .. Im'Last));
                     end;
                     Advance (C);
                  else
                     Name := Take_Ident (C, "field name or tuple index");
                  end if;
                  Next.F_Recv := Left;
                  Next.F_Name := Name;
                  Left := Next;
               end;

            when Op_Question =>
               --  §6.2.4 / §7.2.4: contract propagation. `e?` extracts the
               --  success payload of a contract value, or returns its
               --  failure value from the enclosing subroutine.
               Advance (C);
               declare
                  Next : constant Expr_Access :=
                    new Expr_Node (Kind => E_Question);
               begin
                  Next.Q_Inner := Left;
                  Left := Next;
               end;

            when Punct_LParen =>
               Advance (C);
               declare
                  Args : Expr_Vectors.Vector;
                  Next : Expr_Access;
               begin
                  if C.Cur.Kind /= Punct_RParen then
                     loop
                        Args.Append (Parse_Expr (C));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RParen;
                     end loop;
                  end if;
                  Expect (C, Punct_RParen, "')'");
                  Next := new Expr_Node (Kind => E_Call);
                  Next.C_Callee := Left;
                  Next.C_Args   := Args;
                  Left := Next;
               end;

            when others =>
               exit;
         end case;
      end loop;
      return Left;
   end Parse_Postfix;

   --  Unary prefix operators (§6.3, prec 5). Bootstrap: `*` deref, `-` neg,
   --  `!` not, and §8.1 reference creation `&[raw] [mods] place` / `$place`.
   function Parse_Unary (C : in out Cursor) return Expr_Access is
      E : Expr_Access;
   begin
      if C.Cur.Kind = Op_Star then
         Advance (C);
         E := new Expr_Node (Kind => E_Deref);
         E.D_Inner := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Amp then
         --  §8.1 reference creation. Prefix position only — the infix
         --  bitwise `&` is consumed by Parse_Binary before reaching here.
         Advance (C);
         E := new Expr_Node (Kind => E_Ref);
         E.Rf_Sigil := R_Shared;
         if C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "raw"
         then
            Advance (C);
            E.Rf_Sigil := R_Raw;
         end if;
         Parse_Ref_Modifiers (C, E.Rf_Volatile, E.Rf_Store);
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Dollar then
         Advance (C);
         E := new Expr_Node (Kind => E_Ref);
         E.Rf_Sigil := R_Excl;
         declare
            Vol   : Boolean   := False;
            Store : Ref_Store := RS_None;
         begin
            Parse_Ref_Modifiers (C, Vol, Store);
            if Store /= RS_None then
               raise Syntax_Error with
                 "'$' is inherently storable; 'mut'/'atomic'/'guard' shall "
                 & "not appear after it (spec 8.1) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            E.Rf_Volatile := Vol;
         end;
         E.Rf_Place := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Minus then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Neg;
         E.U_Operand := Parse_Unary (C);
         return E;
      elsif C.Cur.Kind = Op_Bang then
         Advance (C);
         E := new Expr_Node (Kind => E_Unary);
         E.U_Op      := U_Not;
         E.U_Operand := Parse_Unary (C);
         return E;
      else
         return Parse_Postfix (C, Parse_Primary (C));
      end if;
   end Parse_Unary;

   --  Cast operators `as` / `as ?` (§6.8, prec 6 — between unary and
   --  multiplicative). `as!` (airside reinterpret) is deferred.
   function Parse_Cast (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Unary (C);
   begin
      while C.Cur.Kind = Kw_As loop
         Advance (C);
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_Cast);
            Bang : Boolean := False;
         begin
            if C.Cur.Kind = Op_Bang then   --  `as!` reinterpret (§6.8.11)
               Advance (C);
               Bang := True;
            end if;
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

   function Is_Cmp (Op : Binary_Op) return Boolean is
     (Op in B_Eq | B_Ne | B_Lt | B_Gt | B_Le | B_Ge);

   function Parse_Binary
     (C : in out Cursor; Min_BP : Natural) return Expr_Access
   is
      Left : Expr_Access := Parse_Cast (C);
      Op   : Binary_Op;
   begin
      while Token_To_Binop (C.Cur.Kind, Op) loop
         declare
            BP : constant Natural := Binding_Power (Op);
            Next : Expr_Access;
         begin
            exit when BP < Min_BP;
            Advance (C);
            --  Left-associative: parse RHS with strictly higher BP.
            declare
               R : constant Expr_Access := Parse_Binary (C, BP + 1);
               Next_Op : Binary_Op;
            begin
               --  §6.6: comparison operators are non-associative.
               --  `a < b < c` shall be parenthesised, not chained.
               if Is_Cmp (Op)
                 and then Token_To_Binop (C.Cur.Kind, Next_Op)
                 and then Is_Cmp (Next_Op)
               then
                  raise Syntax_Error with
                    "comparison operators are non-associative (§6.6); "
                    & "parenthesise the chain at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Next := new Expr_Node (Kind => E_Binary);
               Next.B_Op  := Op;
               Next.B_Lhs := Left;
               Next.B_Rhs := R;
               Left := Next;
            end;
         end;
      end loop;
      return Left;
   end Parse_Binary;

   --  §8.7 compare-and-swap: `target >.< expected <- new` (eq-CAS) and
   --  `target >!< expected <- new` (ne-CAS), at the lowest binding power
   --  (the operands are full binary expressions). Non-associative.
   function Parse_Expr (C : in out Cursor) return Expr_Access is
      E : Expr_Access := Parse_Binary (C, 0);
   begin
      --  §4.8 range literal `a..b` / `a..=b`. The `..`/`..=` operators
      --  produce the intrinsic range type (T_Range); sema resolves the
      --  element type from the operands. Non-associative (`a..b..c` is
      --  ill-formed).
      if C.Cur.Kind = Op_DotDot or else C.Cur.Kind = Op_DotDotEq then
         declare
            Rng : constant Expr_Access := new Expr_Node (Kind => E_Range);
         begin
            Rng.Rg_Inclusive := C.Cur.Kind = Op_DotDotEq;
            Advance (C);
            Rng.Rg_Lo := E;
            Rng.Rg_Hi := Parse_Binary (C, 0);
            if C.Cur.Kind = Op_DotDot or else C.Cur.Kind = Op_DotDotEq then
               raise Syntax_Error with
                 "range operators are non-associative (§4.8) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            return Rng;
         end;
      end if;
      if C.Cur.Kind = Op_EqCas or else C.Cur.Kind = Op_NeCas then
         declare
            Next : constant Expr_Access := new Expr_Node (Kind => E_CAS);
         begin
            Next.CAS_Ne := C.Cur.Kind = Op_NeCas;
            Advance (C);
            Next.CAS_Tgt := E;
            Next.CAS_Exp := Parse_Binary (C, 0);
            Expect (C, Punct_LArrow, "'<-' in compare-and-swap (spec 8.7)");
            Next.CAS_New := Parse_Binary (C, 0);
            E := Next;
         end;
      end if;
      return E;
   end Parse_Expr;

   ----------------------------------------------------------------------
   --  Statements / blocks
   ----------------------------------------------------------------------

   function Parse_Stmt (C : in out Cursor) return Stmt_Access;

   --  Parse a condition expression with struct-literal suppression so
   --  the following '{' is read as a block, not a struct literal.
   function Parse_Cond (C : in out Cursor) return Expr_Access is
      Saved : constant Boolean := C.No_Struct_Lit;
      R     : Expr_Access;
   begin
      C.No_Struct_Lit := True;
      R := Parse_Expr (C);
      C.No_Struct_Lit := Saved;
      return R;
   end Parse_Cond;

   procedure Parse_Block_Stmts
     (C : in out Cursor; Stmts : out Stmt_Vectors.Vector)
   is
   begin
      Expect (C, Punct_LBrace, "'{'");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         Stmts.Append (Parse_Stmt (C));
      end loop;
      Expect (C, Punct_RBrace, "'}'");
   end Parse_Block_Stmts;

   function Parse_Stmt (C : in out Cursor) return Stmt_Access is
      S : Stmt_Access;
   begin
      case C.Cur.Kind is
         when Kw_Return =>
            Advance (C);
            S := new Stmt_Node (Kind => S_Return);
            S.R_Val := Parse_Expr (C);
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Airside =>
            Advance (C);
            S := new Stmt_Node (Kind => S_Airside_Block);
            Parse_Block_Stmts (C, S.A_Stmts);
            --  §3.2: block expressions used as statements need no ';'
            return S;

         when Dir_At_Guard | Dir_At_Volatile =>
            --  §8.5.3 ordering fences: `@guard[.start|.end]`,
            --  `@volatile[.start|.end]`. Fence directives are statements;
            --  no terminating ';' is required (one is tolerated).
            S := new Stmt_Node (Kind => S_Fence);
            S.Fn_Guard := C.Cur.Kind = Dir_At_Guard;
            Advance (C);
            if C.Cur.Kind = Punct_Dot then
               Advance (C);
               declare
                  Suffix : constant SU.Unbounded_String :=
                    Take_Ident (C, "'start' or 'end' fence suffix");
               begin
                  if SU.To_String (Suffix) = "start" then
                     S.Fn_Form := FF_Start;
                  elsif SU.To_String (Suffix) = "end" then
                     S.Fn_Form := FF_End;
                  else
                     raise Syntax_Error with
                       "fence suffix must be 'start' or 'end' (spec 8.5.3), "
                       & "got '" & SU.To_String (Suffix) & "' at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
               end;
            end if;
            if C.Cur.Kind = Punct_Semi then
               Advance (C);
            end if;
            return S;

         when Kw_Let =>
            --  §5.2 binding  OR  §7 contract extraction  OR  §4.7 tuple
            --  destructuring:
            --      let v = expr ;
            --      let v <- expr else [err] { … } ;
            --      let .{ a, b } = expr ;
            Advance (C);
            if C.Cur.Kind = Punct_Dot then
               Advance (C);
               Expect (C, Punct_LBrace, "'{' after '.' in destructuring let");
               S := new Stmt_Node (Kind => S_Let);
               loop
                  S.L_Tuple_Names.Append
                    (Take_Ident (C, "destructuring binding name"));
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
                  exit when C.Cur.Kind = Punct_RBrace;  --  trailing comma
               end loop;
               Expect (C, Punct_RBrace, "'}' to close destructuring pattern");
               Expect (C, Punct_Eq, "'='");
               S.L_Init := Parse_Expr (C);
               Expect (C, Punct_Semi, "';'");
               return S;
            end if;
            declare
               Name : constant SU.Unbounded_String :=
                 Take_Ident (C, "let binding name");
            begin
               if C.Cur.Kind = Punct_LArrow then
                  --  Extraction: bind the success payload to `v`, or run
                  --  the (diverging) else block with the failure payload.
                  Advance (C);
                  S := new Stmt_Node (Kind => S_Extract);
                  S.X_Bind := Name;
                  S.X_Expr := Parse_Expr (C);
                  Expect (C, Kw_Else, "'else'");
                  if C.Cur.Kind = Tok_Ident then
                     S.X_Err := Take_Ident (C, "failure binding");
                  end if;
                  Parse_Block_Stmts (C, S.X_Else);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               else
                  S := new Stmt_Node (Kind => S_Let);
                  S.L_Name := Name;
                  if C.Cur.Kind = Punct_Colon then
                     Advance (C);
                     --  §4.12: a `?` annotation is equivalent to an omitted
                     --  one — the type is synthesised from the initializer.
                     if C.Cur.Kind = Op_Question then
                        Advance (C);
                     else
                        S.L_Ty := Parse_Type (C);
                     end if;
                  end if;
                  Expect (C, Punct_Eq, "'='");
                  S.L_Init := Parse_Expr (C);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               end if;
            end;

         when Kw_Mut =>
            --  §5.2: mut IDENT [: type] [= expr] ;
            --  Multi-assignment binding (§2.2.1).
            Advance (C);
            S := new Stmt_Node (Kind => S_Mut);
            S.L_Name := Take_Ident (C, "mut binding name");
            if C.Cur.Kind = Punct_Colon then
               Advance (C);
               if C.Cur.Kind = Op_Question then   --  §4.12 inferred
                  Advance (C);
               else
                  S.L_Ty := Parse_Type (C);
               end if;
            end if;
            if C.Cur.Kind = Punct_Eq then
               Advance (C);
               S.L_Init := Parse_Expr (C);
            else
               S.L_Init := null;
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Tok_Label =>
            --  §7.9: a `'name:` label prefixes a loop (labelled blocks are
            --  not yet supported). Attach the name to the loop it heads.
            declare
               Lbl : constant SU.Unbounded_String := C.Cur.Lexeme;
            begin
               Advance (C);
               Expect (C, Punct_Colon, "':' after loop label (spec 7.9)");
               if C.Cur.Kind /= Kw_While and then C.Cur.Kind /= Kw_Loop then
                  raise Syntax_Error with
                    "a label shall prefix a `while`/`loop` (labelled blocks "
                    & "are not supported) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               S := Parse_Stmt (C);   --  parse the loop, then label it
               S.W_Label := Lbl;
               return S;
            end;

         when Kw_While =>
            --  §7.5.1 / §7.5.3: while expr { stmts } [ then { stmts } ].
            --  The `then` block runs after each iteration and is the
            --  target of `continue`; `break` skips it.
            Advance (C);
            S := new Stmt_Node (Kind => S_While);
            S.W_Cond := Parse_Cond (C);
            Parse_Block_Stmts (C, S.W_Body);
            if C.Cur.Kind = Kw_Then then
               Advance (C);
               if C.Cur.Kind /= Punct_LBrace then
                  raise Syntax_Error with
                    "`then` on a loop requires a braced block "
                    & "(spec 7.5.3) at line"
                    & Positive'Image (C.Cur.Line);
               end if;
               Parse_Block_Stmts (C, S.W_Then);
            end if;
            return S;

         when Kw_Loop =>
            --  §7.5.2: `loop` is semantically `while true`.
            Advance (C);
            S := new Stmt_Node (Kind => S_While);
            S.W_Cond := new Expr_Node (Kind => E_Bool_Lit);
            S.W_Cond.Bool_V := True;
            Parse_Block_Stmts (C, S.W_Body);
            return S;

         when Kw_If =>
            --  Two surface forms share the `if` keyword:
            --    block-form statement   if cond { ... } [else { ... } | else if …]
            --    inline expression      if cond then a else b      (as a stmt)
            --  Disambiguate after the condition: '{' => statement.
            Advance (C);

            --  §7.3.3 `if let PAT = e { } else { }` refutable pattern branch.
            if C.Cur.Kind = Kw_Let then
               Advance (C);
               S := new Stmt_Node (Kind => S_If);
               S.SI_Is_Let := True;
               --  Pattern: Enum::Variant [ { binds } ] (positional bindings),
               --  same shape as a match arm pattern.
               S.SI_Let_Pat.Kind := Pat_Variant;
               S.SI_Let_Pat.Path.Append
                 (Take_Ident (C, "enum name in if-let pattern"));
               while C.Cur.Kind = Punct_ColonColon loop
                  Advance (C);
                  S.SI_Let_Pat.Path.Append (Take_Ident (C, "variant name"));
               end loop;
               if C.Cur.Kind = Punct_LBrace then
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     loop
                        S.SI_Let_Pat.Bindings.Append
                          (Take_Ident (C, "payload binding"));
                        exit when C.Cur.Kind /= Punct_Comma;
                        Advance (C);
                        exit when C.Cur.Kind = Punct_RBrace;
                     end loop;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
               end if;
               Expect (C, Punct_Eq, "'=' in if-let");
               --  Suppress trailing struct-literal parsing so the then-block
               --  `{` is not read as `scrutinee { … }`.
               S.SI_Cond := Parse_Cond (C);
               Parse_Block_Stmts (C, S.SI_Then);
               Expect (C, Kw_Else, "'else' in if-let (spec 7.3.3)");
               if C.Cur.Kind = Kw_If then
                  S.SI_Else.Append (Parse_Stmt (C));   --  else-if chaining
               else
                  Parse_Block_Stmts (C, S.SI_Else);
               end if;
               return S;
            end if;

            declare
               Cond : constant Expr_Access := Parse_Cond (C);
            begin
               if C.Cur.Kind = Punct_Arrow then
                  --  Contract-binding form: if e -> v [| err] { } else { }
                  Advance (C);
                  S := new Stmt_Node (Kind => S_If);
                  S.SI_Cond        := Cond;
                  S.SI_Is_Contract := True;
                  S.SI_Succ_Bind   := Take_Ident (C, "success binding");
                  if C.Cur.Kind = Op_Bar then
                     Advance (C);
                     S.SI_Fail_Bind := Take_Ident (C, "failure binding");
                  end if;
                  Parse_Block_Stmts (C, S.SI_Then);
                  if C.Cur.Kind = Kw_Else then
                     Advance (C);
                     if C.Cur.Kind = Kw_If then
                        S.SI_Else.Append (Parse_Stmt (C));
                     else
                        Parse_Block_Stmts (C, S.SI_Else);
                     end if;
                  end if;
                  return S;
               elsif C.Cur.Kind = Punct_LBrace then
                  S := new Stmt_Node (Kind => S_If);
                  S.SI_Cond := Cond;
                  Parse_Block_Stmts (C, S.SI_Then);
                  if C.Cur.Kind = Kw_Else then
                     Advance (C);
                     if C.Cur.Kind = Kw_If then
                        --  else-if: nest a single S_If in the else body.
                        S.SI_Else.Append (Parse_Stmt (C));
                     else
                        Parse_Block_Stmts (C, S.SI_Else);
                     end if;
                  end if;
                  return S;
               else
                  --  Inline if-expression used as an expression statement.
                  declare
                     E : constant Expr_Access :=
                       new Expr_Node (Kind => E_If);
                  begin
                     E.I_Cond := Cond;
                     Expect (C, Kw_Then, "'then'");
                     E.I_Then := Parse_Expr (C);
                     Expect (C, Kw_Else, "'else'");
                     E.I_Else := Parse_Expr (C);
                     Expect (C, Punct_Semi, "';'");
                     S := new Stmt_Node (Kind => S_Expr);
                     S.E_Val := E;
                     return S;
                  end;
               end if;
            end;

         when Kw_Break =>
            --  §7.7 / §7.9: break ['label] [expr] ";". The label names the
            --  loop to terminate; the optional expression is its value.
            Advance (C);
            S := new Stmt_Node (Kind => S_Break);
            if C.Cur.Kind = Tok_Label then
               S.Brk_Label := C.Cur.Lexeme;
               Advance (C);
            end if;
            if C.Cur.Kind /= Punct_Semi then
               S.Brk_Val := Parse_Expr (C);
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Continue =>
            --  §7.9: continue ['label] ";".
            Advance (C);
            S := new Stmt_Node (Kind => S_Continue);
            if C.Cur.Kind = Tok_Label then
               S.Cont_Label := C.Cur.Lexeme;
               Advance (C);
            end if;
            Expect (C, Punct_Semi, "';'");
            return S;

         when Kw_Express =>
            --  §7.8: express <expr> ";"  (labels deferred).
            Advance (C);
            S := new Stmt_Node (Kind => S_Express);
            S.Xp_Val := Parse_Expr (C);
            Expect (C, Punct_Semi, "';'");
            return S;

         when others =>
            --  Expression statement, assignment `place = expr`, or
            --  compound assignment `place op= expr` (§6.7; desugared to
            --  `place = place op expr`).
            declare
               E : constant Expr_Access := Parse_Expr (C);

               function Compound_Op
                 (K : Token_Kind; Op : out Binary_Op) return Boolean is
               begin
                  case K is
                     when Op_PlusEq      => Op := B_Add;
                     when Op_MinusEq     => Op := B_Sub;
                     when Op_StarEq      => Op := B_Mul;
                     when Op_SlashEq     => Op := B_Div;
                     when Op_PercentEq   => Op := B_Mod;
                     when Op_AmpEq       => Op := B_And;
                     when Op_BarEq       => Op := B_Or;
                     when Op_CaretEq     => Op := B_Xor;
                     when Op_ShlEq       => Op := B_Shl;
                     when Op_ShrEq       => Op := B_Shr;
                     when Op_PlusBarEq   => Op := B_Sat_Add;
                     when Op_MinusBarEq  => Op := B_Sat_Sub;
                     when Op_StarBarEq   => Op := B_Sat_Mul;
                     when Op_SlashBarEq  => Op := B_Sat_Div;
                     when others         => return False;
                  end case;
                  return True;
               end Compound_Op;

               C_Op : Binary_Op;
            begin
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  S := new Stmt_Node (Kind => S_Assign);
                  S.Asn_Lhs := E;
                  S.Asn_Rhs := Parse_Expr (C);
                  Expect (C, Punct_Semi, "';'");
                  return S;
               elsif Compound_Op (C.Cur.Kind, C_Op) then
                  Advance (C);
                  declare
                     Rhs    : constant Expr_Access := Parse_Expr (C);
                     Combo  : constant Expr_Access :=
                       new Expr_Node (Kind => E_Binary);
                  begin
                     Combo.B_Op  := C_Op;
                     Combo.B_Lhs := E;     --  evaluated twice in bootstrap
                     Combo.B_Rhs := Rhs;
                     S := new Stmt_Node (Kind => S_Assign);
                     S.Asn_Lhs := E;
                     S.Asn_Rhs := Combo;
                     Expect (C, Punct_Semi, "';'");
                     return S;
                  end;
               else
                  S := new Stmt_Node (Kind => S_Expr);
                  S.E_Val := E;
                  Expect (C, Punct_Semi, "';'");
                  return S;
               end if;
            end;
      end case;
   end Parse_Stmt;

   ----------------------------------------------------------------------
   --  fn header / proto / decl
   ----------------------------------------------------------------------

   procedure Parse_Fn_Header
     (C             : in out Cursor;
      Allow_Unnamed : Boolean;
      H             : out Fn_Header)
   is
   begin
      --  §5.14/§5.15: `@inline` / `@no_inline` / `@symbol "name"` precede
      --  the rest of the header (before `pub`/`airside`). The inlining
      --  directives are mutually exclusive.
      while C.Cur.Kind = Dir_At_Inline
            or else C.Cur.Kind = Dir_At_No_Inline
            or else C.Cur.Kind = Dir_At_Symbol
      loop
         if C.Cur.Kind = Dir_At_Inline then
            H.Is_Inline := True;
            Advance (C);
         elsif C.Cur.Kind = Dir_At_No_Inline then
            H.Is_No_Inline := True;
            Advance (C);
         else
            Advance (C);   --  past @symbol
            if C.Cur.Kind /= Tok_String_Lit then
               raise Syntax_Error with
                 "`@symbol` requires a string literal (spec 5.15) at line"
                 & Positive'Image (C.Cur.Line);
            end if;
            H.Symbol_Name := C.Cur.Str_Bytes;
            Advance (C);
         end if;
      end loop;
      if H.Is_Inline and then H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline` and `@no_inline` shall not both appear on the same "
           & "subroutine (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;

      --  §5.1 header order: [pub] [extern[(iface)]] — independent
      --  modifiers; `pub extern fn` is legal.
      if C.Cur.Kind = Kw_Pub then
         H.Is_Pub := True;
         Advance (C);
      end if;
      if C.Cur.Kind = Kw_Extern then
         H.Is_Extern := True;
         Advance (C);
      end if;

      if C.Cur.Kind = Kw_Variadic then
         Advance (C);
         H.Is_Variadic := True;
         --  §5.1.3: the declaration form requires the binding clause
         --  `variadic(name: T)`; the bare keyword is the prototype form
         --  (subroutine_proto_header, e.g. inside @dyn).
         if C.Cur.Kind = Punct_LParen then
            Advance (C);
            H.Variadic_Name := Take_Ident (C, "variadic binding name");
            Expect (C, Punct_Colon, "':'");
            H.Variadic_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         elsif not Allow_Unnamed then
            raise Syntax_Error with
              "a variadic subroutine definition requires "
              & "'variadic(name: type)' (spec 5.1.3) at line"
              & Positive'Image (C.Cur.Line);
         end if;
      end if;

      if C.Cur.Kind = Kw_Airside then
         H.Is_Airside := True;
         Advance (C);
      end if;

      Expect (C, Kw_Fn, "'fn'");
      H.Name := Take_Ident (C, "function name");
      Parse_Opt_Generic_Params_Bounded (C, H.Generic_Params);
      Parse_Param_List (C, H.Params, Allow_Unnamed);

      if C.Cur.Kind = Punct_Arrow then
         Advance (C);
         H.Return_Type := Parse_Type (C);
      else
         H.Return_Type := null;
      end if;
   end Parse_Fn_Header;

   function Parse_Fn_Decl (C : in out Cursor) return Fn_Decl is
      F : Fn_Decl;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => False, H => F.Header);
      --  §5.15: `@symbol` on a definition requires the `extern` prefix
      --  (a non-extern subroutine has no external name to override).
      if SU.Length (F.Header.Symbol_Name) > 0
        and then not F.Header.Is_Extern
      then
         raise Syntax_Error with
           "`@symbol` requires `extern` (or a `@dyn` block) (spec 5.15) at "
           & "line" & Positive'Image (C.Cur.Line);
      end if;
      Parse_Block_Stmts (C, F.Body_Stmts);
      return F;
   end Parse_Fn_Decl;

   function Parse_Fn_Proto (C : in out Cursor) return Fn_Proto is
      H : Fn_Header;
   begin
      Parse_Fn_Header (C, Allow_Unnamed => True, H => H);
      --  §5.14: inlining directives shall not apply to a prototype (a
      --  declaration without a body).
      if H.Is_Inline or else H.Is_No_Inline then
         raise Syntax_Error with
           "`@inline`/`@no_inline` shall not be applied to a subroutine "
           & "prototype (spec 5.14) at line" & Positive'Image (C.Cur.Line);
      end if;
      Expect (C, Punct_Semi, "';' to terminate fn prototype");
      return H;
   end Parse_Fn_Proto;

   ----------------------------------------------------------------------
   --  @dyn declaration
   ----------------------------------------------------------------------

   function Parse_Dyn_Decl (C : in out Cursor) return Dyn_Decl is
      D : Dyn_Decl;
   begin
      Expect (C, Dir_At_Dyn, "'@dyn'");
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_As, "'as'");
      D.Alias := Take_Ident (C, "alias name for @dyn block");

      Expect (C, Punct_LBrace, "'{'");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         if C.Cur.Kind = Kw_Fn
           or else C.Cur.Kind = Kw_Pub
           or else C.Cur.Kind = Kw_Extern
           or else C.Cur.Kind = Kw_Variadic
           or else C.Cur.Kind = Dir_At_Symbol   --  §5.15 on a dyn item
         then
            D.Items.Append (Parse_Fn_Proto (C));
         else
            raise Syntax_Error with
              "expected fn prototype inside @dyn block, got "
              & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}'");
      return D;
   end Parse_Dyn_Decl;

   ----------------------------------------------------------------------
   --  impl block (§9.1 — inherent implementations, bootstrap subset:
   --  concrete type, fn items with &self/$self). Methods are lowered to
   --  plain fns named `Type$method` with the receiver as first param;
   --  the call-site desugar lives in Kurt.Sema.
   ----------------------------------------------------------------------

   procedure Parse_Impl_Decl
     (C           : in out Cursor;
      Fns         : in out Fn_Vectors.Vector;
      Trait_Impls : in out Trait_Impl_Vectors.Vector;
      Gen_Methods : in out Gen_Method_Vectors.Vector)
   is
      Ty_Name     : SU.Unbounded_String;
      Impl_Params : Generic_Param_Vectors.Vector;  --  §9.1 `impl(...)` list
      Is_Generic  : Boolean := False;

      --  Replace the `self_t` placeholder with the impl type, in place.
      procedure Subst_Self (T : Type_Access) is
      begin
         if T = null then
            return;
         end if;
         case T.Kind is
            when T_Named =>
               if SU.To_String (T.Name) = "self_t" then
                  T.Name := Ty_Name;
               end if;
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  Subst_Self (T.Args.Element (I));
               end loop;
            when T_Ref =>
               Subst_Self (T.Target);
            when T_Array =>
               Subst_Self (T.Elem);
            when T_Tuple =>
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  Subst_Self (T.Elems.Element (I));
               end loop;
            when T_Range =>
               Subst_Self (T.Rng_Elem);
            when T_Dyn =>
               null;   --  `dyn Trait` names a trait, never `self_t`
         end case;
      end Subst_Self;
      TI : Trait_Impl;        --  populated only for `impl Type as Trait`
   begin
      Expect (C, Kw_Impl, "'impl'");
      --  §9.1 / §9.4: optional `impl(P [: bound]…)` generic parameter list,
      --  immediately after `impl` and before the target type.
      if C.Cur.Kind = Punct_LParen then
         Advance (C);
         loop
            declare
               P : Generic_Param;
            begin
               P.Name := Take_Ident (C, "impl generic parameter");
               if C.Cur.Kind = Punct_Colon then
                  Advance (C);
                  loop
                     P.Bounds.Append (Take_Ident (C, "bound name"));
                     exit when C.Cur.Kind /= Op_Plus;
                     Advance (C);
                  end loop;
               end if;
               Impl_Params.Append (P);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RParen;  --  trailing comma
         end loop;
         Expect (C, Punct_RParen, "')' to close impl generic parameters");
         Is_Generic := True;
      end if;
      Ty_Name := Take_Ident (C, "impl type name");
      TI.Ty_Name := Ty_Name;
      --  The target's own generic clause `Owner.<P…>` binds the impl
      --  parameters to the owner; the names are recorded in Impl_Params,
      --  so the clause itself is consumed and discarded here.
      declare
         Dummy : Generic_Param_Vectors.Vector;
      begin
         Parse_Opt_Generic_Params_Bounded (C, Dummy);
      end;
      --  §9.4: `impl Type as Trait`. (`impl Type` is an inherent block.)
      if C.Cur.Kind = Kw_As then
         Advance (C);
         TI.Trait_Name := Take_Ident (C, "trait name");
         --  A trait may carry its own generic clause `as Trait.<…>`.
         declare
            Dummy : Generic_Param_Vectors.Vector;
         begin
            Parse_Opt_Generic_Params_Bounded (C, Dummy);
         end;
      end if;
      Expect (C, Punct_LBrace, "'{' to open impl block");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
       if C.Cur.Kind = Kw_Const then
         --  §9.3.2 associated-const definition `const NAME: type = expr;`.
         Advance (C);
         declare
            AC : Assoc_Const;
         begin
            AC.Name := Take_Ident (C, "associated const name");
            Expect (C, Punct_Colon, "':' in associated const");
            AC.Ty := Parse_Type (C);
            Expect (C, Punct_Eq, "'=' in associated const definition");
            AC.Val := Parse_Expr (C);
            AC.Has_Val := True;
            Expect (C, Punct_Semi, "';' after associated const");
            TI.Consts.Append (AC);
         end;
       else
         declare
            Fn : Fn_Decl := Parse_Fn_Decl (C);
            MN : constant SU.Unbounded_String := Fn.Header.Name;
         begin
            if Is_Generic then
               --  §9.1/§9.4 generic impl: keep the method as a template.
               --  `self_t` stays a placeholder and the impl parameters are
               --  free; Kurt.Mono specialises it per owner instance. The
               --  bare method name is preserved (mangled to
               --  `Owner$args$method` at instantiation time).
               Gen_Methods.Append
                 ((Owner      => Ty_Name,
                   Trait_Name => TI.Trait_Name,
                   Gen_Params => Impl_Params,
                   Method     => Fn));
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            else
               for I in Fn.Header.Params.First_Index ..
                        Fn.Header.Params.Last_Index
               loop
                  Subst_Self (Fn.Header.Params.Element (I).Ty);
               end loop;
               Subst_Self (Fn.Header.Return_Type);
               --  §9.2: the method is namespaced under its type. Both
               --  inherent and trait-impl methods lower to `Type$method`,
               --  so static dispatch finds them uniformly.
               Fn.Header.Name := SU.To_Unbounded_String
                 (SU.To_String (Ty_Name) & "$" & SU.To_String (MN));
               Fns.Append (Fn);
               if SU.Length (TI.Trait_Name) > 0 then
                  TI.Methods.Append (MN);
               end if;
            end if;
         end;
       end if;
      end loop;
      Expect (C, Punct_RBrace, "'}' to close impl block");
      --  A concrete `impl Type as Trait` registers a dispatch-table
      --  candidate; a generic trait impl provides static methods only
      --  (per-instance dispatch tables are out of scope for the
      --  bootstrap), so it is not registered here.
      if SU.Length (TI.Trait_Name) > 0 and then not Is_Generic then
         Trait_Impls.Append (TI);
      end if;
   end Parse_Impl_Decl;

   ----------------------------------------------------------------------
   --  trait declaration (§9.3). Bootstrap subset: method signatures and
   --  default methods. The `self_t` placeholder in signatures stays
   --  abstract here; impl blocks substitute the concrete type.
   ----------------------------------------------------------------------

   procedure Parse_Trait_Decl
     (C : in out Cursor; Traits : in out Trait_Vectors.Vector)
   is
      D : Trait_Decl;
   begin
      if C.Cur.Kind = Kw_Pub then
         Advance (C);          --  visibility not modelled in bootstrap
      end if;
      Expect (C, Kw_Trait, "'trait'");
      D.Name := Take_Ident (C, "trait name");
      --  §9.3.3 supertrait bounds: `with { self_t: Bar + Baz }`.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         Expect (C, Punct_LBrace, "'{' after 'with' on a trait");
         --  Expect `self_t : Trait { '+' Trait }`. (The bootstrap models
         --  only the single `self_t: …` form.)
         declare
            Head : constant SU.Unbounded_String :=
              Take_Ident (C, "'self_t' in supertrait bound");
            pragma Unreferenced (Head);
         begin
            Expect (C, Punct_Colon, "':' in supertrait bound");
            loop
               D.Supertraits.Append (Take_Ident (C, "supertrait name"));
               exit when C.Cur.Kind /= Op_Plus;
               Advance (C);
            end loop;
         end;
         Expect (C, Punct_RBrace, "'}' to close supertrait clause");
      end if;
      Expect (C, Punct_LBrace, "'{' to open trait body");
      while C.Cur.Kind /= Punct_RBrace and then C.Cur.Kind /= Tok_EOF loop
         if C.Cur.Kind = Kw_Const then
            --  §9.3.2 associated constant: `const NAME: type [= expr];`.
            Advance (C);
            declare
               AC : Assoc_Const;
            begin
               AC.Name := Take_Ident (C, "associated const name");
               Expect (C, Punct_Colon, "':' in associated const");
               AC.Ty := Parse_Type (C);
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  AC.Val := Parse_Expr (C);
                  AC.Has_Val := True;
               end if;
               Expect (C, Punct_Semi, "';' after associated const");
               D.Consts.Append (AC);
            end;
         else
            declare
               M : Trait_Method;
            begin
               --  Parse_Fn_Header consumes `fn name(params) -> ret`.
               Parse_Fn_Header (C, Allow_Unnamed => False, H => M.Sig);
               if C.Cur.Kind = Punct_LBrace then
                  --  §9.3.4 default method: a signature with a body.
                  M.Has_Body := True;
                  Parse_Block_Stmts (C, M.Body_Stmts);
               else
                  Expect (C, Punct_Semi,
                          "';' after trait method signature");
               end if;
               D.Methods.Append (M);
            end;
         end if;
      end loop;
      Expect (C, Punct_RBrace, "'}' to close trait body");
      Traits.Append (D);
   end Parse_Trait_Decl;

   ----------------------------------------------------------------------
   --  Top-level dispatch
   ----------------------------------------------------------------------

   --  struct_declaration = "struct" IDENT "{" field { "," field } "}"
   --  field = IDENT ":" type            (§5.5, bootstrap subset)
   function Parse_Struct_Decl (C : in out Cursor) return Struct_Decl is
      D : Struct_Decl;
   begin
      Expect (C, Kw_Struct, "'struct'");
      D.Name := Take_Ident (C, "struct name");
      Parse_Opt_Generic_Params (C, D.Generic_Params);
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               Fld : Struct_Field;
            begin
               --  §5.5.1 field modifiers — parsed and discarded.
               while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                  Advance (C);
               end loop;
                if C.Cur.Kind = Op_Question then
                   Fld.Name := SU.To_Unbounded_String ("?");
                   Advance (C);
                else
                   Fld.Name := Take_Ident (C, "field name");
                end if;
               Expect (C, Punct_Colon, "':'");
               Fld.Ty := Parse_Type (C);
               --  §5.5.3 optional default-value expression.
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  Fld.Default := Parse_Expr (C);
               end if;
               D.Fields.Append (Fld);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");

      --  Optional `with` clause (§5.11). Recognised items: `repr(packed)`
      --  (§4.11.4) and `align(N)` (§4.11.5) — bare or inside a with-block;
      --  unrecognised items are skipped (balanced) like the enum parser.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         declare
            procedure Parse_Struct_With_Item is
               Item : constant String := SU.To_String (C.Cur.Lexeme);
            begin
               if C.Cur.Kind /= Tok_Ident then
                  raise Syntax_Error with
                    "expected with-item identifier, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               Advance (C);
               if Item = "repr" then
                  Expect (C, Punct_LParen, "'('");
                  declare
                     Arg : constant String :=
                       SU.To_String (Take_Ident (C, "repr argument"));
                  begin
                     if Arg = "packed" then
                        D.Repr_Packed := True;
                     end if;
                     --  `repr(native)` and others: accepted, no effect
                     --  in the bootstrap layout model.
                  end;
                  Expect (C, Punct_RParen, "')'");
               elsif Item = "align" then
                  Expect (C, Punct_LParen, "'('");
                  if C.Cur.Kind /= Tok_Int_Lit or else C.Cur.Int_V <= 0 then
                     raise Syntax_Error with
                       "expected positive integer in align(N) at line"
                       & Positive'Image (C.Cur.Line);
                  end if;
                  D.Align_N := Natural (C.Cur.Int_V);
                  Advance (C);
                  Expect (C, Punct_RParen, "')'");
               else
                  --  Skip a balanced unrecognised item.
                  declare
                     Depth : Natural := 0;
                  begin
                     while not (Depth = 0
                                and then (C.Cur.Kind = Punct_Comma
                                          or else C.Cur.Kind
                                                 = Punct_RBrace
                                          or else C.Cur.Kind
                                                 = Punct_Semi
                                          or else C.Cur.Kind = Tok_EOF))
                     loop
                        if C.Cur.Kind in Punct_LParen | Punct_LBrace then
                           Depth := Depth + 1;
                        elsif C.Cur.Kind in Punct_RParen | Punct_RBrace
                        then
                           Depth := Depth - 1;
                        end if;
                        Advance (C);
                     end loop;
                  end;
               end if;
            end Parse_Struct_With_Item;
         begin
            if C.Cur.Kind = Punct_LBrace then
               --  with_braced (§5.11): the closing brace terminates the
               --  clause; no trailing ';'.
               Advance (C);
               loop
                  exit when C.Cur.Kind = Punct_RBrace;
                  Parse_Struct_With_Item;
                  exit when C.Cur.Kind /= Punct_Comma;
                  Advance (C);
               end loop;
               Expect (C, Punct_RBrace, "'}'");
            else
               --  with_single (§5.11): a terminating ';' is required
               --  (§5.6: `composite_form, with_single, ';'`).
               Parse_Struct_With_Item;
               Expect (C, Punct_Semi,
                 "';' after single-item `with` clause (spec 5.11)");
            end if;
         end;
      end if;
      return D;
   end Parse_Struct_Decl;

   --  enum_declaration = "enum" IDENT "{" variant { "," variant } "}"
   --  variant = IDENT [ "=" integer_literal ]    (§5.6, unit variants)
   --  Discriminants default to 0,1,2,… continuing from the last value.
   function Parse_Enum_Decl (C : in out Cursor) return Enum_Decl is
      D    : Enum_Decl;
      Next : Long_Long_Integer := 0;
   begin
      Expect (C, Kw_Enum, "'enum'");
      D.Name := Take_Ident (C, "enum name");
      Parse_Opt_Generic_Params (C, D.Generic_Params);
      Expect (C, Punct_LBrace, "'{'");
      if C.Cur.Kind /= Punct_RBrace then
         loop
            declare
               V : Enum_Variant;
            begin
               V.Name := Take_Ident (C, "variant name");
               --  Optional payload (§5.6):
               --     struct variant: `{ ident: type, … }`  (named fields)
               --     tuple  variant: `{ [pub|mut|airside]* type, … }`
               --                                          (positional)
               --  Disambiguated by the first non-modifier token sequence:
               --  `ident ':'` -> struct, otherwise -> tuple.
               if C.Cur.Kind = Punct_LBrace then
                  Advance (C);
                  if C.Cur.Kind /= Punct_RBrace then
                     --  Skip leading modifiers to peek the first payload
                     --  token (modifiers themselves are not stored in the
                     --  bootstrap field model).
                     while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside loop
                        Advance (C);
                     end loop;
                     declare
                        Is_Struct_Variant : constant Boolean :=
                          C.Cur.Kind = Tok_Ident
                          and then Peek_Tok (C).Kind = Punct_Colon;
                        Idx : Natural := 0;
                     begin
                        loop
                           declare
                              Fld : Struct_Field;
                           begin
                              if Is_Struct_Variant then
                                 if C.Cur.Kind = Op_Question then
                                    Fld.Name := SU.To_Unbounded_String ("?");
                                    Advance (C);
                                 else
                                    Fld.Name := Take_Ident (C, "payload field name");
                                 end if;
                                 Expect (C, Punct_Colon, "':'");
                                 Fld.Ty := Parse_Type (C);
                              else
                                 --  Synthetic positional name "0", "1", …
                                 declare
                                    Im : constant String := Idx'Image;
                                 begin
                                    Fld.Name := SU.To_Unbounded_String
                                      (Im (Im'First + 1 .. Im'Last));
                                 end;
                                 Fld.Ty := Parse_Type (C);
                                 Idx := Idx + 1;
                              end if;
                              V.Payload.Append (Fld);
                           end;
                           exit when C.Cur.Kind /= Punct_Comma;
                           Advance (C);
                           exit when C.Cur.Kind = Punct_RBrace;
                           while C.Cur.Kind in Kw_Pub | Kw_Mut | Kw_Airside
                           loop
                              Advance (C);
                           end loop;
                        end loop;
                     end;
                  end if;
                  Expect (C, Punct_RBrace, "'}'");
               end if;
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  if C.Cur.Kind = Tok_Hash_Wild then
                     --  `= #wild#` or `= #wild#(V)`: this variant covers
                     --  all otherwise-unlisted discriminant values, with
                     --  optional canonical value V (§4.5, §5.6).
                     Advance (C);
                     V.Is_Wild := True;
                     if C.Cur.Kind = Punct_LParen then
                        Advance (C);
                        declare
                           Neg : Boolean := False;
                        begin
                           if C.Cur.Kind = Op_Minus then
                              Neg := True;
                              Advance (C);
                           end if;
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer in #wild#(...), got "
                                & Image (C.Cur)
                                & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                           V.Value :=
                             (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                        end;
                        V.Wild_Canon := True;
                        Advance (C);
                        Expect (C, Punct_RParen, "')'");
                     else
                        V.Value := Next;
                     end if;
                  elsif C.Cur.Kind = Tok_Int_Lit
                    or else C.Cur.Kind = Op_Minus
                  then
                     --  §4.11.3: a negative explicit value selects a
                     --  signed discriminant type.
                     declare
                        Neg : Boolean := False;
                     begin
                        if C.Cur.Kind = Op_Minus then
                           Neg := True;
                           Advance (C);
                           if C.Cur.Kind /= Tok_Int_Lit then
                              raise Syntax_Error with
                                "expected integer after '-' in "
                                & "discriminant value, got "
                                & Image (C.Cur) & " at line"
                                & Positive'Image (C.Cur.Line);
                           end if;
                        end if;
                        Next := (if Neg then -C.Cur.Int_V else C.Cur.Int_V);
                     end;
                     Advance (C);
                     V.Value := Next;
                     Next := Next + 1;
                  else
                     raise Syntax_Error with
                       "expected discriminant value after '=', got "
                       & Image (C.Cur)
                       & " at line" & Positive'Image (C.Cur.Line);
                  end if;
               else
                  V.Value := Next;
                  Next := Next + 1;
               end if;
               D.Variants.Append (V);
            end;
            exit when C.Cur.Kind /= Punct_Comma;
            Advance (C);
            exit when C.Cur.Kind = Punct_RBrace;
         end loop;
      end if;
      Expect (C, Punct_RBrace, "'}'");

      --  Optional `with` clause (§5.10).
      --     `with contract`                       — bare contract clause
      --     `with { item, item, … }`              — with-block (§4.5, §5.10)
      --  Items recognised by the bootstrap: `contract [-> type]`, `discrim
      --  (type)`. Other items (repr, align, …) are parsed-and-discarded.
      if C.Cur.Kind = Kw_With then
       declare
         Is_Braced : Boolean := False;
       begin
         Advance (C);
         if C.Cur.Kind = Punct_LBrace then
            Is_Braced := True;
            Advance (C);
            loop
               exit when C.Cur.Kind = Punct_RBrace;
               if C.Cur.Kind = Tok_Ident then
                  declare
                     Item : constant String := SU.To_String (C.Cur.Lexeme);
                  begin
                     Advance (C);
                     if Item = "contract" then
                        D.Is_Contract := True;
                        --  Optional `-> inverted_pair_type` (§7.2). The
                        --  inverted pair is parsed and discarded; `!verdict`
                        --  is not yet activated.
                        if C.Cur.Kind = Punct_Arrow then
                           Advance (C);
                           declare
                              Ignore : constant Type_Access := Parse_Type (C);
                              pragma Unreferenced (Ignore);
                           begin null; end;
                        end if;
                     elsif Item = "discrim" then
                        --  §4.11.3: `with discrim(T)` fixes the
                        --  discriminant type (validated by sema).
                        Expect (C, Punct_LParen, "'('");
                        D.Discrim_Ty := Parse_Type (C);
                        Expect (C, Punct_RParen, "')'");
                     else
                        --  Unrecognised with-item: skip balanced tokens up
                        --  to the next ',' or '}'. The bootstrap does not
                        --  semantically use repr/align/lifetime/…
                        declare
                           Depth : Natural := 0;
                        begin
                           while not (Depth = 0
                                      and then (C.Cur.Kind = Punct_Comma
                                                or else C.Cur.Kind
                                                       = Punct_RBrace))
                           loop
                              if C.Cur.Kind in Punct_LParen
                                | Punct_LBrace
                              then
                                 Depth := Depth + 1;
                              elsif C.Cur.Kind in Punct_RParen
                                | Punct_RBrace
                              then
                                 Depth := Depth - 1;
                              end if;
                              Advance (C);
                           end loop;
                        end;
                     end if;
                  end;
               else
                  raise Syntax_Error with
                    "expected with-item identifier, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
               exit when C.Cur.Kind /= Punct_Comma;
               Advance (C);
            end loop;
            Expect (C, Punct_RBrace, "'}'");
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "contract"
         then
            D.Is_Contract := True;
            Advance (C);
         elsif C.Cur.Kind = Tok_Ident
           and then SU.To_String (C.Cur.Lexeme) = "discrim"
         then
            --  Bare form `with discrim(T)` (§4.11.3 example form).
            Advance (C);
            Expect (C, Punct_LParen, "'('");
            D.Discrim_Ty := Parse_Type (C);
            Expect (C, Punct_RParen, "')'");
         else
            raise Syntax_Error with
              "expected 'contract' or '{' after 'with', got " & Image (C.Cur)
              & " at line" & Positive'Image (C.Cur.Line);
         end if;
         --  §5.7 / §5.11: `with_single` requires a terminating ';';
         --  `with_braced` is terminated by its closing brace.
         if not Is_Braced then
            Expect (C, Punct_Semi,
              "';' after single-item `with` clause (spec 5.11)");
         end if;
       end;
      end if;
      return D;
   end Parse_Enum_Decl;

   --  §5.3 `const NAME: T = expr ;` — the type annotation is mandatory.
   function Parse_Const_Decl (C : in out Cursor) return Const_Decl is
      D : Const_Decl;
   begin
      Expect (C, Kw_Const, "'const'");
      D.Name := Take_Ident (C, "const name");
      Expect (C, Punct_Colon, "':' (const type annotation is mandatory, "
              & "spec 5.3)");
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      D.Init := Parse_Expr (C);
      Expect (C, Punct_Semi, "';' after const declaration");
      return D;
   end Parse_Const_Decl;

   --  §5.4 `static [mut] NAME: T = expr ;`.
   function Parse_Static_Decl (C : in out Cursor) return Static_Decl is
      D : Static_Decl;
   begin
      Advance (C);   --  consume the `static` identifier-word
      if C.Cur.Kind = Kw_Mut then
         D.Is_Mut := True;
         Advance (C);
      end if;
      D.Name := Take_Ident (C, "static name");
      Expect (C, Punct_Colon, "':' (static type annotation)");
      D.Ty := Parse_Type (C);
      Expect (C, Punct_Eq, "'='");
      D.Init := Parse_Expr (C);
      Expect (C, Punct_Semi, "';' after static declaration");
      return D;
   end Parse_Static_Decl;

   function Parse_Unit (Lex : in out Kurt.Lexer.Lexer)
      return Translation_Unit
   is
      C : Cursor := (Lex => Lex'Unchecked_Access, others => <>);
      U : Translation_Unit;
   begin
      Advance (C);
      while C.Cur.Kind /= Tok_EOF loop
         --  §5.16: skip any `@[ … ]@` annotations preceding a declaration.
         --  Their content is opaque and unrecognised ones are ignored.
         while C.Cur.Kind = Dir_At_LBracket loop
            Advance (C);
            while C.Cur.Kind /= Dir_At_RBracket loop
               if C.Cur.Kind = Tok_EOF then
                  raise Syntax_Error with
                    "unbalanced `@[` annotation (missing `]@`, spec 5.16)";
               end if;
               Advance (C);
            end loop;
            Advance (C);   --  past `]@`
         end loop;
         exit when C.Cur.Kind = Tok_EOF;
         case C.Cur.Kind is
            when Kw_Fn | Kw_Extern | Kw_Variadic | Kw_Airside
               | Dir_At_Inline | Dir_At_No_Inline   --  §5.14
               | Dir_At_Symbol =>                    --  §5.15
               U.Fns.Append (Parse_Fn_Decl (C));
            when Kw_Pub =>
               --  `pub` heads a subroutine, trait, const, or static. The
               --  bootstrap has no visibility model — `pub` on const /
               --  static is consumed and discarded.
               if Peek_Tok (C).Kind = Kw_Trait then
                  Parse_Trait_Decl (C, U.Traits);
               elsif Peek_Tok (C).Kind = Kw_Const then
                  Advance (C);
                  U.Consts.Append (Parse_Const_Decl (C));
               elsif Peek_Tok (C).Kind = Tok_Ident
                 and then SU.To_String (Peek_Tok (C).Lexeme) = "static"
               then
                  Advance (C);
                  U.Statics.Append (Parse_Static_Decl (C));
               else
                  U.Fns.Append (Parse_Fn_Decl (C));
               end if;
            when Kw_Const =>
               U.Consts.Append (Parse_Const_Decl (C));
            when Dir_At_Dyn =>
               U.Dyns.Append (Parse_Dyn_Decl (C));
            when Kw_Struct =>
               U.Structs.Append (Parse_Struct_Decl (C));
            when Kw_Enum =>
               U.Enums.Append (Parse_Enum_Decl (C));
            when Kw_Impl =>
               Parse_Impl_Decl (C, U.Fns, U.Trait_Impls, U.Gen_Methods);
            when Kw_Trait =>
               Parse_Trait_Decl (C, U.Traits);
            when Tok_Ident =>
               --  §5.4 `static [mut] NAME: T = expr ;` (the word
               --  `static` is not a bootstrap keyword).
               if SU.To_String (C.Cur.Lexeme) = "static" then
                  U.Statics.Append (Parse_Static_Decl (C));
               --  §5.8 `type NAME = type ;` — alias declaration. The
               --  substitution happens at later use sites (Parse_Type),
               --  so nothing is recorded in the translation unit.
               elsif SU.To_String (C.Cur.Lexeme) = "type" then
                  Advance (C);
                  declare
                     A : Alias_Entry;
                  begin
                     A.Name := Take_Ident (C, "alias name after 'type'");
                     if C.Cur.Kind = Punct_Dot
                       and then Peek_Tok (C).Kind = Op_Lt
                     then
                        raise Syntax_Error with
                          "generic type aliases are not supported by "
                          & "the bootstrap (spec 5.8) at line"
                          & Positive'Image (C.Cur.Line);
                     end if;
                     Expect (C, Punct_Eq, "'=' in type alias");
                     A.Target := Parse_Type (C);
                     Expect (C, Punct_Semi, "';' after type alias");
                     C.Aliases.Append (A);
                  end;
               else
                  raise Syntax_Error with
                    "expected top-level declaration, got " & Image (C.Cur)
                    & " at line" & Positive'Image (C.Cur.Line);
               end if;
            when others =>
               raise Syntax_Error with
                 "expected top-level declaration, got " & Image (C.Cur)
                 & " at line" & Positive'Image (C.Cur.Line);
         end case;
      end loop;
      return U;
   end Parse_Unit;

end Kurt.Parser;
