separate (Kurt.Parser)
   procedure Merge_Unit
     (Into : in out Translation_Unit; From : Translation_Unit) is
   begin
      Into.Fns.Append (From.Fns);
      Into.Dyns.Append (From.Dyns);
      Into.Structs.Append (From.Structs);
      Into.Enums.Append (From.Enums);
      Into.Traits.Append (From.Traits);
      Into.Trait_Impls.Append (From.Trait_Impls);
      Into.Consts.Append (From.Consts);
      Into.Statics.Append (From.Statics);
      Into.Gen_Methods.Append (From.Gen_Methods);
      Into.Gen_Fns.Append (From.Gen_Fns);
      Into.Top_Asm.Append (From.Top_Asm);
      --  §10.6: carry each unit's `module` names into the merged unit so
      --  Kurt.Sema.Check can see them (e.g. for the name-collision check
      --  against sibling fn/struct/enum/... declarations, spec 10.6).
      Into.Module_Names.Append (From.Module_Names);
      Into.Module_Pubs.Append (From.Module_Pubs);
      --  §7.10.1 at most one trap handler across the translation unit.
      if From.Has_Trap_Handler then
         if Into.Has_Trap_Handler then
            raise Syntax_Error with
              "multiple @trap handlers across the translation unit (§7.10.1)";
         end if;
         Into.Has_Trap_Handler := True;
         Into.Trap_Handler := From.Trap_Handler;
      end if;
   end Merge_Unit;
