separate (Kurt.Parser)
   procedure Parse_Trait_Decl
     (C : in out Cursor; Traits : in out Trait_Vectors.Vector)
   is
      D : Trait_Decl;
   begin
      if C.Cur.Kind = Kw_Pub then
         D.Is_Pub := True;
         Advance (C);
      end if;
      Expect (C, Kw_Trait, "'trait'");
      D.Name := Take_Ident (C, "trait name");
      --  §9.3.3 supertrait bounds: `with { selftype: Bar + Baz }`.
      if C.Cur.Kind = Kw_With then
         Advance (C);
         Expect (C, Punct_LBrace, "'{' after 'with' on a trait");
         --  Expect `selftype : Trait { '+' Trait }`. (The bootstrap models
         --  only the single `selftype: ...` form.)
         Expect (C, Kw_Selftype, "'selftype' in supertrait bound");
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
         if C.Cur.Kind = Kw_Type then
            --  §9.3.1 associated type: `type Item [= Default];`.
            Advance (C);
            declare
               ATy : Assoc_Type;
            begin
               ATy.Name := Take_Ident (C, "associated type name");
               if C.Cur.Kind = Punct_Eq then
                  Advance (C);
                  ATy.Ty := Parse_Type (C);   --  default
               end if;
               Expect (C, Punct_Semi, "';' after associated type");
               D.Assoc_Types.Append (ATy);
            end;
         elsif C.Cur.Kind = Kw_Const then
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
