separate (Kurt.Sema.Check)
   procedure Check_Fn_Bodies is
         procedure Check_Fn (Fn : Fn_Decl) is
         begin
            Cur_Generics := Fn.Header.Generic_Params;
            Scope.Clear;
            Kurt.Borrow.Clear (Borrows);
            Moved.Clear;
            for J in Fn.Header.Params.First_Index ..
                     Fn.Header.Params.Last_Index
            loop
               declare
                  P : constant Param := Fn.Header.Params.Element (J);
               begin
                  if SU.Length (P.Name) > 0 then
                     Scope.Append ((Name => P.Name, Ty => P.Ty, Is_Mut => P.Is_Mut));
                  end if;
               end;
            end loop;

            if Fn.Header.Return_Type /= null then
               Cur_Ret := Fn.Header.Return_Type;
            elsif Fn.Header.Is_Closure then
               --  §9.9 a closure that omits `-> U` infers its return type
               --  from its body's first `return` (params already in scope).
               declare
                  RT : Type_Access := null;
               begin
                  for S of Fn.Body_Stmts loop
                     if S.Kind = S_Return and then S.R_Val /= null then
                        RT := Infer (S.R_Val, null);
                        exit;
                     end if;
                  end loop;
                  Cur_Ret := (if RT /= null then RT else Mk_Named ("void"));
               end;
            else
               Cur_Ret := Mk_Named ("void");
            end if;

            --  §5.1.1: the whole body of an `airside fn` is an airside
            --  region (§6.1.8 lets `uninit` appear there).
            In_Airside := (if Fn.Header.Is_Airside then 1 else 0);
            for J in Fn.Body_Stmts.First_Index ..
                     Fn.Body_Stmts.Last_Index
            loop
               Check_Stmt (Fn.Body_Stmts.Element (J));
            end loop;
            In_Airside := 0;

            --  §4.10/§7.11: a `-> never` subroutine's body shall diverge —
            --  control shall not be able to reach its end.
            if Fn.Header.Is_Never
              and then not Stmts_Diverge (Fn.Body_Stmts)
            then
               Error ("body of '-> never' subroutine '"
                      & SU.To_String (Fn.Header.Name)
                      & "' can fall through; it shall diverge "
                      & "(spec 4.10/7.11)");
            end if;
         end Check_Fn;
         --  §8.11: type- and borrow-check each `with destruct { ... }` block
         --  as codegen will lower it — with `self` bound to an exclusive
         --  reference to the object being destroyed (`$selftype`). Synthesised
         --  here so the block is held to the same rules as any subroutine.
         procedure Check_Destruct (Nm : String; Block : Stmt_Vectors.Vector) is
            D : Fn_Decl;
            P : Param;
         begin
            if Block.Is_Empty then
               return;
            end if;
            P.Name           := SU.To_Unbounded_String ("self");
            P.Ty             := new AST_Type (Kind => T_Ref);
            P.Ty.Sigil       := R_Excl;
            P.Ty.Target      := new AST_Type (Kind => T_Named);
            P.Ty.Target.Name := SU.To_Unbounded_String (Nm);
            D.Header.Name    := SU.To_Unbounded_String (Nm & "$destruct");
            D.Header.Params.Append (P);
            D.Body_Stmts     := Block;
            Check_Fn (D);
         end Check_Destruct;
      begin
         for I in U.Fns.First_Index .. U.Fns.Last_Index loop
            Check_Fn (U.Fns.Element (I));
         end loop;
         for I in U.Gen_Fns.First_Index .. U.Gen_Fns.Last_Index loop
            Check_Fn (U.Gen_Fns.Element (I));
         end loop;
         for I in U.Structs.First_Index .. U.Structs.Last_Index loop
            if U.Structs.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Structs.Element (I).Name),
                               U.Structs.Element (I).Destruct_Block);
            end if;
         end loop;
         for I in U.Enums.First_Index .. U.Enums.Last_Index loop
            if U.Enums.Element (I).Has_Destruct then
               Check_Destruct (SU.To_String (U.Enums.Element (I).Name),
                               U.Enums.Element (I).Destruct_Block);
            end if;
         end loop;
   end Check_Fn_Bodies;
