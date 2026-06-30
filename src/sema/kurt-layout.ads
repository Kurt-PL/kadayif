--  Kurt.Layout — KSA layout queries (§2.1.2, §4.11).
--
--  Computes size, alignment, and struct field offsets for the types in
--  a translation unit. Both Kurt.Sema and Kurt.Codegen consult this so
--  the layout model is single-sourced.
--
--  The bootstrap keeps a single registered unit's struct table in a
--  package-level variable (one translation unit per run), so queries
--  need not thread the unit through every call.

with Kurt.Parser;

package Kurt.Layout is

   --  Record the unit whose struct declarations subsequent queries use.
   procedure Register (U : Kurt.Parser.Translation_Unit);

   --  Size in cells of a type. A cell is Kurt.Cell_Bits_Exec bits wide;
   --  on this target a cell is a host byte.
   function Size_Of (T : Kurt.Parser.Type_Access) return Natural;

   --  Alignment in cells.
   function Align_Of (T : Kurt.Parser.Type_Access) return Natural;

   --  Whether Name denotes a registered struct type.
   function Is_Struct (Name : String) return Boolean;

   --  §8.11.1: whether T satisfies `destruct` — declared `with destruct`, or
   --  by propagation through struct fields / enum payloads / array elements
   --  / tuple members. References and other forms do not propagate.
   function Satisfies_Destruct
     (T : Kurt.Parser.Type_Access) return Boolean;

   --  §4.7 tuple positional-field queries (structural; no named decl).
   function Tuple_Field_Offset
     (T : Kurt.Parser.Type_Access; Index : Natural) return Natural;
   function Tuple_Field_Type
     (T     : Kurt.Parser.Type_Access;
      Index : Natural) return Kurt.Parser.Type_Access;

   --  Cell offset of Field within struct Struct_Name. Raises if unknown.
   function Field_Offset (Struct_Name, Field : String) return Natural;

   --  Declared type of Field within struct Struct_Name; null if unknown.
   function Field_Type
     (Struct_Name, Field : String) return Kurt.Parser.Type_Access;

   --  §5.5.3 default-value expression for a field; null when it has none.
   function Field_Default
     (Struct_Name, Field : String) return Kurt.Parser.Expr_Access;

   --  Declared field count and the Index-th field name (1-based) of a
   --  struct, for iterating its full field list (e.g. to fill defaults).
   function Struct_Field_Count (Struct_Name : String) return Natural;
   function Struct_Field_Name
     (Struct_Name : String; Index : Positive) return String;

   --  Whether Name denotes a registered enum type.
   function Is_Enum (Name : String) return Boolean;

   --  Discriminant width (cells) chosen for an enum (§4.11.3). 0 means
   --  a void discriminant (at most one variant, no #wild#(V) canonical).
   function Enum_Disc_Size (Name : String) return Natural;

   --  Whether the chosen discriminant type is signed (§4.11.3: explicit
   --  signed `discrim(T)` or any negative declared value).
   function Enum_Disc_Signed (Name : String) return Boolean;

   --  Whether any variant of the enum carries a payload (i.e. the enum
   --  value is larger than its bare discriminant and must live in RAM).
   function Enum_Has_Payload (Name : String) return Boolean;

   --  Whether Enum_Name has a variant called Variant.
   function Has_Variant (Enum_Name, Variant : String) return Boolean;

   --  Whether Enum_Name declares a `#wild#` variant (one that covers all
   --  otherwise-unlisted discriminant values, §4.5). A match on an enum
   --  WITHOUT such a variant requires an explicit `#wild#` arm.
   function Has_Wild_Variant (Enum_Name : String) return Boolean;

   --  Whether the enum was declared `with contract` (§7).
   function Is_Contract_Enum (Name : String) return Boolean;

   --  For a `with contract` enum: the success (truthy, non-`#wild#`)
   --  variant and the failure (`#wild#`) variant names.
   function Contract_Success_Variant (Enum_Name : String) return String;
   function Contract_Fail_Variant (Enum_Name : String) return String;

   --  Discriminant value of Variant in Enum_Name. Raises if unknown.
   function Variant_Value
     (Enum_Name, Variant : String) return Long_Long_Integer;

   --  §6.1.5 the discriminant for `Enum::#wild#` construction: the smallest
   --  non-negative value not assigned to any declared variant.
   function Implicit_Wild_Value (Enum_Name : String) return Long_Long_Integer;

   --  Number of variants, and the Index-th variant's name (1-based),
   --  for exhaustiveness checking.
   function Variant_Count (Enum_Name : String) return Natural;
   function Variant_Name (Enum_Name : String; Index : Positive) return String;

   --  Payload of a variant (named fields). Cell offset is measured from
   --  the start of the enum object (i.e. it already includes the
   --  discriminant + payload-region offset). Field_No is 1-based.
   function Variant_Field_Count (Enum_Name, Variant : String) return Natural;
   function Variant_Field_Offset
     (Enum_Name, Variant : String; Field_No : Positive) return Natural;
   function Variant_Field_Type
     (Enum_Name, Variant : String; Field_No : Positive)
      return Kurt.Parser.Type_Access;
   --  Offset of a payload field by name (or -1 if absent).
   function Variant_Field_Offset_By_Name
     (Enum_Name, Variant, Field : String) return Integer;
   function Variant_Field_Type_By_Name
     (Enum_Name, Variant, Field : String) return Kurt.Parser.Type_Access;

   --  §4.5 Type_Access overloads: for the intrinsic verdict the payload
   --  type/offset come from the type arguments; any other type delegates to
   --  the by-name query. Used by the contract / variant-construction paths.
   function Variant_Field_Offset
     (T : Kurt.Parser.Type_Access; Variant : String; Field_No : Positive)
      return Natural;
   function Variant_Field_Type
     (T : Kurt.Parser.Type_Access; Variant : String; Field_No : Positive)
      return Kurt.Parser.Type_Access;
   function Variant_Field_Offset_By_Name
     (T : Kurt.Parser.Type_Access; Variant, Field : String) return Integer;
   function Variant_Field_Type_By_Name
     (T : Kurt.Parser.Type_Access; Variant, Field : String)
      return Kurt.Parser.Type_Access;

   Layout_Error : exception;

end Kurt.Layout;
