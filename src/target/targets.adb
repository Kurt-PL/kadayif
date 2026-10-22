package body Targets is

   function Arbiter_Of
     (Programme, Translation : Environment) return Environment
   is
      P : Environment renames Programme;
      T : Environment renames Translation;
   begin
      return
        (Platform        => T.Platform,
         Cell_Width      => Positive'Max (P.Cell_Width, T.Cell_Width),
         Address_Width   => Positive'Max (P.Address_Width, T.Address_Width),
         Reference_Width =>
           Positive'Max (P.Reference_Width, T.Reference_Width));
   end Arbiter_Of;

end Targets;
