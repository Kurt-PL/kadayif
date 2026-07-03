with Ada.Strings.Unbounded;

package body Kurt.Layout is

   package SU renames Ada.Strings.Unbounded;
   use Kurt.Parser;

   --  The registered unit (bootstrap: one per run).
   The_Unit  : Translation_Unit;
   Have_Unit : Boolean := False;

   procedure Register (U : Kurt.Parser.Translation_Unit) is separate;

   --  ceil(X, A): round X up to the nearest multiple of A (A = 0 => X).
   function Ceil (X, A : Natural) return Natural is
   begin
      if A = 0 then
         return X;
      end if;
      return ((X + A - 1) / A) * A;
   end Ceil;

   --  Locate a struct declaration by name.
   function Find_Struct (Name : String; Found : out Struct_Decl)
      return Boolean
   is
   begin
      if not Have_Unit then
         return False;
      end if;
      for I in The_Unit.Structs.First_Index ..
               The_Unit.Structs.Last_Index
      loop
         if SU.To_String (The_Unit.Structs.Element (I).Name) = Name then
            Found := The_Unit.Structs.Element (I);
            return True;
         end if;
      end loop;
      return False;
   end Find_Struct;

   function Is_Struct (Name : String) return Boolean is
      D : Struct_Decl;
   begin
      return Find_Struct (Name, D);
   end Is_Struct;

   function Mk_Named (N : String) return Type_Access is
     (new AST_Type'(Kind => T_Named,
                    Name => SU.To_Unbounded_String (N), Args => <>));

   --  §4.5: verdict is an intrinsic built-in (like bool / the primitives) —
   --  it is recognised by name, never declared or monomorphised. For the
   --  name-only queries below (variant names/values, discriminant, contract
   --  flags) the shape is constant, so a synthesised declaration suffices.
   --  The payload field *types* here are placeholders: every size/alignment/
   --  field-offset query for verdict is element-type dependent and is served
   --  from the type's arguments instead (see Size_Of, Align_Of, and the
   --  Type_Access-taking Variant_Field_* overloads).
   function Is_Verdict (Name : String) return Boolean is (Name = "verdict");

   function Synth_Verdict return Enum_Decl is separate;

   --  Locate an enum declaration by name.
   function Find_Enum (Name : String; Found : out Enum_Decl) return Boolean is
   begin
      if Is_Verdict (Name) then
         Found := Synth_Verdict;
         return True;
      end if;
      if not Have_Unit then
         return False;
      end if;
      for I in The_Unit.Enums.First_Index .. The_Unit.Enums.Last_Index loop
         if SU.To_String (The_Unit.Enums.Element (I).Name) = Name then
            Found := The_Unit.Enums.Element (I);
            return True;
         end if;
      end loop;
      return False;
   end Find_Enum;

   function Satisfies_Destruct (T : Type_Access) return Boolean is separate;

   function Is_Enum (Name : String) return Boolean is
      D : Enum_Decl;
   begin
      return Find_Enum (Name, D);
   end Is_Enum;

   --  §4.11.3 discriminant width in cells. `with discrim(T)` forces T's
   --  width; at most one variant with no `#wild#(V)` canonical value is
   --  a void discriminant (0 cells); otherwise the smallest unsigned —
   --  or, when any declared value is negative, signed — integer type
   --  holding every value is selected.
   function Enum_Disc_Size (Name : String) return Natural is separate;

   --  §4.11.3: whether the discriminant type is signed (an explicit
   --  signed `discrim(T)`, or any negative declared value).
   function Enum_Disc_Signed (Name : String) return Boolean is separate;

   function Has_Variant (Enum_Name, Variant : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            return True;
         end if;
      end loop;
      return False;
   end Has_Variant;

   function Enum_Has_Payload (Name : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if not D.Variants.Element (I).Payload.Is_Empty then
            return True;
         end if;
      end loop;
      return False;
   end Enum_Has_Payload;

   function Has_Wild_Variant (Enum_Name : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Is_Wild then
            return True;
         end if;
      end loop;
      return False;
   end Has_Wild_Variant;

   function Is_Contract_Enum (Name : String) return Boolean is
      D : Enum_Decl;
   begin
      return Find_Enum (Name, D) and then D.Is_Contract;
   end Is_Contract_Enum;

   function Contract_Success_Variant (Enum_Name : String) return String is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      --  `with contract`: the explicit (non-#wild#) variant is success.
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if not D.Variants.Element (I).Is_Wild then
            return SU.To_String (D.Variants.Element (I).Name);
         end if;
      end loop;
      raise Layout_Error with
        "contract enum '" & Enum_Name & "' has no success variant";
   end Contract_Success_Variant;

   function Contract_Fail_Variant (Enum_Name : String) return String is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Is_Wild then
            return SU.To_String (D.Variants.Element (I).Name);
         end if;
      end loop;
      raise Layout_Error with
        "contract enum '" & Enum_Name & "' has no #wild# (failure) variant";
   end Contract_Fail_Variant;

   function Variant_Value
     (Enum_Name, Variant : String) return Long_Long_Integer
   is separate;

   function Implicit_Wild_Value
     (Enum_Name : String) return Long_Long_Integer
   is separate;

   --  Locate a variant declaration within an enum.
   function Find_Variant
     (Enum_Name, Variant : String; Found : out Enum_Variant) return Boolean
   is separate;

   --  KSA size of a named-field group (a variant payload).
   function Group_Size
     (Fields : Kurt.Parser.Struct_Field_Vectors.Vector) return Natural
   is separate;

   --  Enum alignment: max of discriminant size and every payload field's
   --  alignment.
   function Enum_Align (Name : String) return Natural is separate;

   --  Offset at which the payload region begins (after the discriminant).
   function Payload_Region_Offset (Name : String) return Natural is separate;

   --  Total enum size: discriminant + largest payload, rounded to align.
   function Enum_Size (Name : String) return Natural is separate;

   function Variant_Field_Count
     (Enum_Name, Variant : String) return Natural
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         return 0;
      end if;
      return Natural (V.Payload.Length);
   end Variant_Field_Count;

   function Variant_Field_Offset
     (Enum_Name, Variant : String; Field_No : Positive) return Natural
   is separate;

   function Variant_Field_Type
     (Enum_Name, Variant : String; Field_No : Positive)
      return Kurt.Parser.Type_Access
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         return null;
      end if;
      return V.Payload.Element (V.Payload.First_Index + (Field_No - 1)).Ty;
   end Variant_Field_Type;

   function Variant_Field_Offset_By_Name
     (Enum_Name, Variant, Field : String) return Integer
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         return -1;
      end if;
      for K in V.Payload.First_Index .. V.Payload.Last_Index loop
         if SU.To_String (V.Payload.Element (K).Name) = Field then
            return Variant_Field_Offset
              (Enum_Name, Variant, K - V.Payload.First_Index + 1);
         end if;
      end loop;
      return -1;
   end Variant_Field_Offset_By_Name;

   function Variant_Field_Type_By_Name
     (Enum_Name, Variant, Field : String) return Kurt.Parser.Type_Access
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         return null;
      end if;
      for K in V.Payload.First_Index .. V.Payload.Last_Index loop
         if SU.To_String (V.Payload.Element (K).Name) = Field then
            return V.Payload.Element (K).Ty;
         end if;
      end loop;
      return null;
   end Variant_Field_Type_By_Name;

   --  §4.5 verdict payload accessors, from the type arguments. `Pass` carries
   --  the success type (Args[1]), `Fail` the error type (Args[2]); both sit at
   --  the payload region after the ui1 discriminant.
   function Verdict_Payload_Type
     (T : Type_Access; Variant : String) return Type_Access is
     (if Variant = "Pass" then T.Args.Element (T.Args.First_Index)
      else T.Args.Element (T.Args.First_Index + 1));

   --  Type_Access-taking overloads: for verdict (intrinsic, no declaration)
   --  the payload type/offset come from the arguments; any other type
   --  delegates to the declaration-based query by name.
   function Variant_Field_Type
     (T : Type_Access; Variant : String; Field_No : Positive)
      return Type_Access is
     (if Is_Verdict (SU.To_String (T.Name))
      then Verdict_Payload_Type (T, Variant)
      else Variant_Field_Type (SU.To_String (T.Name), Variant, Field_No));

   function Variant_Field_Offset
     (T : Type_Access; Variant : String; Field_No : Positive) return Natural is
     (if Is_Verdict (SU.To_String (T.Name)) then Ceil (1, Align_Of (T))
      else Variant_Field_Offset (SU.To_String (T.Name), Variant, Field_No));

   function Variant_Field_Type_By_Name
     (T : Type_Access; Variant, Field : String) return Type_Access is
     (if Is_Verdict (SU.To_String (T.Name))
      then Verdict_Payload_Type (T, Variant)
      else Variant_Field_Type_By_Name (SU.To_String (T.Name), Variant, Field));

   function Variant_Field_Offset_By_Name
     (T : Type_Access; Variant, Field : String) return Integer is
     (if Is_Verdict (SU.To_String (T.Name)) then Integer (Ceil (1, Align_Of (T)))
      else Variant_Field_Offset_By_Name
             (SU.To_String (T.Name), Variant, Field));

   function Variant_Count (Enum_Name : String) return Natural is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return 0;
      end if;
      return Natural (D.Variants.Length);
   end Variant_Count;

   function Variant_Name (Enum_Name : String; Index : Positive) return String
   is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      return SU.To_String (D.Variants.Element (Index).Name);
   end Variant_Name;

   ----------------------------------------------------------------------
   --  Size / alignment
   ----------------------------------------------------------------------

   --  §4.11.1: numeric types have align == size; references are pointer
   --  width; structs take the max field alignment.
   function Align_Of (T : Kurt.Parser.Type_Access) return Natural is separate;

   function Size_Of (T : Kurt.Parser.Type_Access) return Natural is separate;

   ----------------------------------------------------------------------
   --  Field queries
   ----------------------------------------------------------------------

   function Tuple_Field_Type
     (T : Kurt.Parser.Type_Access; Index : Natural) return Type_Access is
   begin
      return T.Elems.Element (T.Elems.First_Index + Index);
   end Tuple_Field_Type;

   function Tuple_Field_Offset
     (T : Kurt.Parser.Type_Access; Index : Natural) return Natural
   is
      Off : Natural := 0;
   begin
      for I in 0 .. Index loop
         declare
            FT : constant Type_Access :=
              T.Elems.Element (T.Elems.First_Index + I);
         begin
            Off := Ceil (Off, Align_Of (FT));
            if I = Index then
               return Off;
            end if;
            Off := Off + Size_Of (FT);
         end;
      end loop;
      return Off;
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Tuple_Field_Offset;

   function Field_Offset (Struct_Name, Field : String) return Natural is
      D   : Struct_Decl;
      Off : Natural := 0;
   begin
      if not Find_Struct (Struct_Name, D) then
         raise Layout_Error with "unknown struct '" & Struct_Name & "'";
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         declare
            FT : constant Type_Access := D.Fields.Element (I).Ty;
         begin
            --  §4.11.4: a packed struct has no inter-field padding.
            if not D.Repr_Packed then
               Off := Ceil (Off, Align_Of (FT));
            end if;
            if SU.To_String (D.Fields.Element (I).Name) = Field then
               return Off;
            end if;
            Off := Off + Size_Of (FT);
         end;
      end loop;
      raise Layout_Error with
        "struct '" & Struct_Name & "' has no field '" & Field & "'";
   exception
      when Constraint_Error =>
         raise Layout_Error with
           "type size exceeds the representable address range " &
           "(§4.7: size overflow is a translation failure)";
   end Field_Offset;

   function Field_Type
     (Struct_Name, Field : String) return Kurt.Parser.Type_Access
   is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return null;
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         if SU.To_String (D.Fields.Element (I).Name) = Field then
            return D.Fields.Element (I).Ty;
         end if;
      end loop;
      return null;
   end Field_Type;

   --  §5.5.1 `mut` field modifier: True when the named field is mut.
   function Field_Is_Mut (Struct_Name, Field : String) return Boolean is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return False;
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         if SU.To_String (D.Fields.Element (I).Name) = Field then
            return D.Fields.Element (I).Is_Mut;
         end if;
      end loop;
      return False;
   end Field_Is_Mut;

   --  §5.5.3 default-value expression for a field, or null when none.
   function Field_Default
     (Struct_Name, Field : String) return Kurt.Parser.Expr_Access
   is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return null;
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         if SU.To_String (D.Fields.Element (I).Name) = Field then
            return D.Fields.Element (I).Default;
         end if;
      end loop;
      return null;
   end Field_Default;

   function Struct_Field_Count (Struct_Name : String) return Natural is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return 0;
      end if;
      return Natural (D.Fields.Length);
   end Struct_Field_Count;

   function Struct_Field_Name
     (Struct_Name : String; Index : Positive) return String
   is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return "";
      end if;
      return SU.To_String
        (D.Fields.Element (D.Fields.First_Index + (Index - 1)).Name);
   end Struct_Field_Name;

end Kurt.Layout;
