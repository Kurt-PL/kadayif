separate (Kurt.Sema.Check)
   procedure Maybe_Move (E : Expr_Access) is
   begin
      if E /= null and then E.Kind = E_Path
        and then Natural (E.Segments.Length) = 1
      then
         declare
            Name : constant String :=
              SU.To_String (E.Segments.Last_Element);
         begin
            if Satisfies_Destruct (Lookup_Scope (Name)) then
               Mark_Moved (Name);
               E.P_Is_Move := True;   --  codegen skips its scope-exit drop
            end if;
         end;
      end if;
   end Maybe_Move;
