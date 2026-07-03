separate (Kurt.Parser)
   function Snapshot (U : Translation_Unit) return Rename_From is
      function P1 (N : Natural) return Positive is (Positive (N + 1));
   begin
      return
        (Fns         => P1 (Natural (U.Fns.Length)),
         Gen_Fns     => P1 (Natural (U.Gen_Fns.Length)),
         Structs     => P1 (Natural (U.Structs.Length)),
         Enums       => P1 (Natural (U.Enums.Length)),
         Traits      => P1 (Natural (U.Traits.Length)),
         Trait_Impls => P1 (Natural (U.Trait_Impls.Length)),
         Consts      => P1 (Natural (U.Consts.Length)),
         Statics     => P1 (Natural (U.Statics.Length)),
         Gen_Methods => P1 (Natural (U.Gen_Methods.Length)));
   end Snapshot;
