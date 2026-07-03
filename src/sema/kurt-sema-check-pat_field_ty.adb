separate (Kurt.Sema.Check)
   function Pat_Field_Ty
     (Pat : Kurt.Parser.Pattern; Scrut : Type_Access;
      VN : String; K : Positive) return Type_Access is
   begin
      if K <= Natural (Pat.Bind_Fields.Length)
        and then SU.Length (Pat.Bind_Fields.Element (K)) > 0
      then
         return Kurt.Layout.Variant_Field_Type_By_Name
           (Scrut, VN, SU.To_String (Pat.Bind_Fields.Element (K)));
      end if;
      return Kurt.Layout.Variant_Field_Type (Scrut, VN, K);
   end Pat_Field_Ty;
