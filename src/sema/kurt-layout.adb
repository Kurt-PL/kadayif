with Ada.Strings.Unbounded;
with Ada.Strings.Fixed;

package body Kurt.Layout is

   package SU renames Ada.Strings.Unbounded;
   use Kurt.Parser;

   --  The registered unit (bootstrap: one per run).
   The_Unit  : Translation_Unit;
   Have_Unit : Boolean := False;

   procedure Register (U : Kurt.Parser.Translation_Unit) is separate;

   --  §10.2/§10.3 source-unit provenance — see Kurt.Layout.ads.
   File_Prefixes : Path_Segments.Vector;

   procedure Register_File_Prefix (Prefix : String) is
   begin
      File_Prefixes.Append (SU.To_Unbounded_String (Prefix));
   end Register_File_Prefix;

   --  The registered file prefix that mangled Name's leading '$'-segment
   --  matches, or "" (the root unit) when none does.
   function Unit_Tag (Name : String) return String is
      Dollar : constant Natural := Ada.Strings.Fixed.Index (Name, "$");
      Head   : constant String :=
        (if Dollar = 0 then Name else Name (Name'First .. Dollar - 1));
   begin
      for P of File_Prefixes loop
         if SU.To_String (P) = Head then
            return Head;
         end if;
      end loop;
      return "";
   end Unit_Tag;

   function Same_Source_Unit (A, B : String) return Boolean is
   begin
      return Unit_Tag (A) = Unit_Tag (B);
   end Same_Source_Unit;

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

   function Wild_Has_Canon (Enum_Name : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Is_Wild then
            return D.Variants.Element (I).Wild_Canon;
         end if;
      end loop;
      return False;
   end Wild_Has_Canon;

   function Is_Wild_Variant (Enum_Name, Variant : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            return D.Variants.Element (I).Is_Wild;
         end if;
      end loop;
      return False;
   end Is_Wild_Variant;

   function Wild_Variant_Name (Enum_Name : String) return String is
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
        "enum '" & Enum_Name & "' has no #wild# variant";
   end Wild_Variant_Name;

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
      --  §7.2 `with contract`: the explicit (non-#wild#) variant is
      --  success; `with !contract`: polarity exchanged -- #wild# is
      --  success.
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Is_Wild = D.Contract_Inv then
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
         if D.Variants.Element (I).Is_Wild /= D.Contract_Inv then
            return SU.To_String (D.Variants.Element (I).Name);
         end if;
      end loop;
      raise Layout_Error with
        "contract enum '" & Enum_Name & "' has no failure variant";
   end Contract_Fail_Variant;

   function Contract_Is_Inverted (Enum_Name : String) return Boolean is
      D : Enum_Decl;
   begin
      return Find_Enum (Enum_Name, D) and then D.Contract_Inv;
   end Contract_Is_Inverted;

   function Contract_Inv_Type_Name (Enum_Name : String) return String is
      D : Enum_Decl;
   begin
      if Find_Enum (Enum_Name, D) and then D.Inv_Type /= null
        and then D.Inv_Type.Kind = T_Named
      then
         return SU.To_String (D.Inv_Type.Name);
      end if;
      return "";
   end Contract_Inv_Type_Name;

   function Contract_Inv_Type
     (T : Kurt.Parser.Type_Access) return Kurt.Parser.Type_Access
   is
      D : Enum_Decl;
   begin
      if T = null or else T.Kind /= T_Named
        or else not Find_Enum (SU.To_String (T.Name), D)
        or else D.Inv_Type = null
      then
         return null;
      end if;
      --  §7.2/§5.9: the declared inverted-pair type is written against
      --  D's OWN (still-generic) parameter names, e.g. `switch_inv.<T>`
      --  inside `switch.<T>`. Substitute each of D's generic parameter
      --  names, positionally, with T's actual type arguments -- the same
      --  positional-substitution model used for template instantiation
      --  elsewhere (Kurt.Mono).
      declare
         function Subst (N : Kurt.Parser.Type_Access)
           return Kurt.Parser.Type_Access
         is
            R : Kurt.Parser.Type_Access;
         begin
            if N = null then
               return null;
            end if;
            if N.Kind = T_Named and then N.Args.Is_Empty then
               for I in D.Generic_Params.First_Index ..
                        D.Generic_Params.Last_Index
               loop
                  if SU.To_String (D.Generic_Params.Element (I).Name)
                       = SU.To_String (N.Name)
                    and then I - D.Generic_Params.First_Index
                               < Natural (T.Args.Length)
                  then
                     return T.Args.Element
                       (T.Args.First_Index
                          + (I - D.Generic_Params.First_Index));
                  end if;
               end loop;
            end if;
            R := new Kurt.Parser.AST_Type'(N.all);
            if N.Kind = T_Named then
               R.Args.Clear;
               for I in N.Args.First_Index .. N.Args.Last_Index loop
                  R.Args.Append (Subst (N.Args.Element (I)));
               end loop;
            end if;
            return R;
         end Subst;
      begin
         return Subst (D.Inv_Type);
      end;
   end Contract_Inv_Type;

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

   --  KSA size of a named-field group (a variant payload). §4.11.3 `Packed`
   --  suppresses inter-field padding and forces align 1.
   function Group_Size
     (Fields : Kurt.Parser.Struct_Field_Vectors.Vector;
      Packed : Boolean := False) return Natural
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

   function Variant_Field_Name
     (Enum_Name, Variant : String; Field_No : Positive) return String
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V)
        or else Field_No > Natural (V.Payload.Length)
      then
         return "";
      end if;
      return SU.To_String
        (V.Payload.Element (V.Payload.First_Index + (Field_No - 1)).Name);
   end Variant_Field_Name;

   function Variant_Field_Offset
     (Enum_Name, Variant : String; Field_No : Positive) return Natural
   is separate;

   function Variant_Field_Is_Airside
     (Enum_Name, Variant : String; Field_No : Positive) return Boolean
   is
      V : Enum_Variant;
   begin
      if not Find_Variant (Enum_Name, Variant, V)
        or else Field_No > Natural (V.Payload.Length)
      then
         return False;
      end if;
      return V.Payload.Element
        (V.Payload.First_Index + (Field_No - 1)).Is_Airside;
   end Variant_Field_Is_Airside;

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

   --  §5.5.1 `pub`/`airside` field modifiers.
   function Field_Is_Pub (Struct_Name, Field : String) return Boolean is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return False;
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         if SU.To_String (D.Fields.Element (I).Name) = Field then
            return D.Fields.Element (I).Is_Pub;
         end if;
      end loop;
      return False;
   end Field_Is_Pub;

   function Field_Is_Airside (Struct_Name, Field : String) return Boolean is
      D : Struct_Decl;
   begin
      if not Find_Struct (Struct_Name, D) then
         return False;
      end if;
      for I in D.Fields.First_Index .. D.Fields.Last_Index loop
         if SU.To_String (D.Fields.Element (I).Name) = Field then
            return D.Fields.Element (I).Is_Airside;
         end if;
      end loop;
      return False;
   end Field_Is_Airside;

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

   --  §8.4.2: a field's effective lifetime identifier — its explicit
   --  reference annotation (`&'a T`) when present and not permanent
   --  ('static/'const, §8.4.1), otherwise the field name (the implicit
   --  lifetime identifier).
   function Life_Id (F : Struct_Field) return String is
   begin
      if F.Ty /= null and then F.Ty.Kind = T_Ref
        and then SU.Length (F.Ty.R_Life) > 0
        and then SU.To_String (F.Ty.R_Life) /= "static"
        and then SU.To_String (F.Ty.R_Life) /= "const"
      then
         return SU.To_String (F.Ty.R_Life);
      end if;
      return SU.To_String (F.Name);
   end Life_Id;

   --  §8.4.3: position of Name (a field's lifetime identifier, §8.4.2)
   --  within whichever chain of Chains mentions it (1 = longest in that
   --  chain), or 0 when Name appears in none.
   function Lifetime_Chain_Pos
     (Chains : Lifetime_Chain_Vectors.Vector; Name : String) return Natural
   is
   begin
      for Ch of Chains loop
         for P in Ch.First_Index .. Ch.Last_Index loop
            if SU.To_String (Ch.Element (P)) = Name then
               return P;
            end if;
         end loop;
      end loop;
      return 0;
   end Lifetime_Chain_Pos;

   --  §8.4.3: whether NA and NB both appear in a common chain of Chains.
   function Lifetime_Same_Chain
     (Chains : Lifetime_Chain_Vectors.Vector; NA, NB : String) return Boolean
   is
   begin
      for Ch of Chains loop
         declare
            Has_A, Has_B : Boolean := False;
         begin
            for P in Ch.First_Index .. Ch.Last_Index loop
               if SU.To_String (Ch.Element (P)) = NA then
                  Has_A := True;
               end if;
               if SU.To_String (Ch.Element (P)) = NB then
                  Has_B := True;
               end if;
            end loop;
            if Has_A and then Has_B then
               return True;
            end if;
         end;
      end loop;
      return False;
   end Lifetime_Same_Chain;

   --  §8.4.3: destroy A before B? A common chain relates them: the one
   --  whose name sits later in the chain is shorter-lived and destroyed
   --  first. Otherwise (unrelated / no chain): reverse declaration order,
   --  same as the pre-existing no-chain default.
   function Lifetime_Destroy_Before
     (Chains : Lifetime_Chain_Vectors.Vector;
      NA, NB : String; IA, IB : Positive) return Boolean
   is
   begin
      if Lifetime_Same_Chain (Chains, NA, NB) then
         return Lifetime_Chain_Pos (Chains, NA) >
                Lifetime_Chain_Pos (Chains, NB);
      end if;
      return IA > IB;
   end Lifetime_Destroy_Before;

   function Struct_Destroy_Order (Struct_Name : String) return Field_Order is
      D : Struct_Decl;
      N : Natural;
   begin
      if not Find_Struct (Struct_Name, D) then
         return (1 .. 0 => 1);
      end if;
      N := Natural (D.Fields.Length);
      declare
         Order : Field_Order (1 .. N);

         function Name_Of (Idx : Positive) return String is
           (Life_Id (D.Fields.Element (D.Fields.First_Index + Idx - 1)));
      begin
         for I in 1 .. N loop
            Order (I) := I;
         end loop;
         --  insertion sort: Order ends up in destruction order.
         for I in 2 .. N loop
            declare
               Key : constant Positive := Order (I);
               KN  : constant String := Name_Of (Key);
               J : Integer := I - 1;
            begin
               while J >= 1 and then Lifetime_Destroy_Before
                       (D.Lifetime_Chains, KN, Name_Of (Order (J)),
                        Key, Order (J))
               loop
                  Order (J + 1) := Order (J);
                  J := J - 1;
               end loop;
               Order (J + 1) := Key;
            end;
         end loop;
         return Order;
      end;
   end Struct_Destroy_Order;

   function Variant_Destroy_Order
     (Enum_Name, Variant : String) return Field_Order
   is
      ED : Enum_Decl;
      VD : Enum_Variant;
      N  : Natural;
   begin
      if not Find_Enum (Enum_Name, ED)
        or else not Find_Variant (Enum_Name, Variant, VD)
      then
         return (1 .. 0 => 1);
      end if;
      N := Natural (VD.Payload.Length);
      declare
         Order : Field_Order (1 .. N);

         function Name_Of (Idx : Positive) return String is
           (Life_Id (VD.Payload.Element (VD.Payload.First_Index + Idx - 1)));
      begin
         for I in 1 .. N loop
            Order (I) := I;
         end loop;
         for I in 2 .. N loop
            declare
               Key : constant Positive := Order (I);
               KN  : constant String := Name_Of (Key);
               J : Integer := I - 1;
            begin
               while J >= 1 and then Lifetime_Destroy_Before
                       (ED.Lifetime_Chains, KN, Name_Of (Order (J)),
                        Key, Order (J))
               loop
                  Order (J + 1) := Order (J);
                  J := J - 1;
               end loop;
               Order (J + 1) := Key;
            end;
         end loop;
         return Order;
      end;
   end Variant_Destroy_Order;

end Kurt.Layout;
