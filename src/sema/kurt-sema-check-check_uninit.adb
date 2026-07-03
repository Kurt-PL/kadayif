separate (Kurt.Sema.Check)
   procedure Check_Uninit (Target : Type_Access) is
   begin
      if In_Airside = 0 then
         Error ("`uninit` shall appear only inside an `airside` block or "
                & "`airside fn` body (spec 6.1.8)");
      end if;
      if Target = null then
         Error ("`uninit` requires a known target type; annotate the "
                & "binding (spec 6.1.8)");
      end if;
   end Check_Uninit;
