separate (Kurt.Layout)
   function Synth_Verdict return Enum_Decl is
      D    : Enum_Decl;
      Pass : Enum_Variant;
      Fail : Enum_Variant;
   begin
      D.Name        := SU.To_Unbounded_String ("verdict");
      D.Is_Contract := True;
      D.Discrim_Ty  := Mk_Named ("ui1");
      Pass.Name  := SU.To_Unbounded_String ("Pass");
      Pass.Value := 1;
      Pass.Payload.Append
        ((Name => SU.To_Unbounded_String ("0"), Ty => Mk_Named ("ui1"),
          Default => null, others => <>));
      Fail.Name       := SU.To_Unbounded_String ("Fail");
      Fail.Value      := 0;
      Fail.Is_Wild    := True;
      Fail.Wild_Canon := True;
      Fail.Payload.Append
        ((Name => SU.To_Unbounded_String ("0"), Ty => Mk_Named ("ui1"),
          Default => null, others => <>));
      D.Variants.Append (Pass);
      D.Variants.Append (Fail);
      return D;
   end Synth_Verdict;
