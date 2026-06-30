with Ada.Strings.Unbounded;

package body Kurt.Layout is

   package SU renames Ada.Strings.Unbounded;
   use Kurt.Parser;

   --  The registered unit (bootstrap: one per run).
   The_Unit  : Translation_Unit;
   Have_Unit : Boolean := False;

   procedure Register (U : Kurt.Parser.Translation_Unit) is
   begin
      The_Unit  := U;
      Have_Unit := True;
   end Register;

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
          Default => null));
      Fail.Name       := SU.To_Unbounded_String ("Fail");
      Fail.Value      := 0;
      Fail.Is_Wild    := True;
      Fail.Wild_Canon := True;
      Fail.Payload.Append
        ((Name => SU.To_Unbounded_String ("0"), Ty => Mk_Named ("ui1"),
          Default => null));
      D.Variants.Append (Pass);
      D.Variants.Append (Fail);
      return D;
   end Synth_Verdict;

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

   function Satisfies_Destruct (T : Type_Access) return Boolean is
   begin
      if T = null then
         return False;
      end if;
      case T.Kind is
         when T_Named =>
            declare
               N  : constant String := SU.To_String (T.Name);
               SD : Struct_Decl;
               ED : Enum_Decl;
            begin
               if Find_Struct (N, SD) then
                  if SD.Has_Destruct then
                     return True;
                  end if;
                  for F of SD.Fields loop
                     if Satisfies_Destruct (F.Ty) then
                        return True;
                     end if;
                  end loop;
                  return False;
               elsif Find_Enum (N, ED) then
                  if ED.Has_Destruct then
                     return True;
                  end if;
                  for V of ED.Variants loop
                     for F of V.Payload loop
                        if Satisfies_Destruct (F.Ty) then
                           return True;
                        end if;
                     end loop;
                  end loop;
                  return False;
               end if;
               return False;
            end;
         when T_Array =>
            return Satisfies_Destruct (T.Elem);
         when T_Tuple =>
            for E of T.Elems loop
               if Satisfies_Destruct (E) then
                  return True;
               end if;
            end loop;
            return False;
         when others =>
            return False;
      end case;
   end Satisfies_Destruct;

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
   function Enum_Disc_Size (Name : String) return Natural is
      D   : Enum_Decl;
      Min : Long_Long_Integer := 0;
      Max : Long_Long_Integer := 0;
   begin
      if not Find_Enum (Name, D) then
         return 1;
      end if;
      if D.Discrim_Ty /= null then
         return Size_Of (D.Discrim_Ty);
      end if;
      declare
         Has_Canon : Boolean := False;
      begin
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            if D.Variants.Element (I).Wild_Canon then
               Has_Canon := True;
            end if;
         end loop;
         if Natural (D.Variants.Length) <= 1 and then not Has_Canon then
            return 0;
         end if;
      end;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         Min := Long_Long_Integer'Min (Min, D.Variants.Element (I).Value);
         Max := Long_Long_Integer'Max (Max, D.Variants.Element (I).Value);
      end loop;
      if Min < 0 then
         if Min >= -128 and then Max <= 127 then
            return 1;
         elsif Min >= -32768 and then Max <= 32767 then
            return 2;
         elsif Min >= -(2 ** 31) and then Max <= 2 ** 31 - 1 then
            return 4;
         else
            return 8;
         end if;
      elsif Max <= 255 then
         return 1;
      elsif Max <= 65535 then
         return 2;
      elsif Max <= 4294967295 then
         return 4;
      else
         return 8;
      end if;
   end Enum_Disc_Size;

   --  §4.11.3: whether the discriminant type is signed (an explicit
   --  signed `discrim(T)`, or any negative declared value).
   function Enum_Disc_Signed (Name : String) return Boolean is
      D : Enum_Decl;
   begin
      if not Find_Enum (Name, D) then
         return False;
      end if;
      if D.Discrim_Ty /= null then
         if D.Discrim_Ty.Kind = T_Named then
            declare
               N : constant String := SU.To_String (D.Discrim_Ty.Name);
            begin
               return (N'Length >= 2
                         and then N (N'First) = 's'
                         and then N (N'First + 1) = 'i')
                   or else N = "saddr";
            end;
         end if;
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if D.Variants.Element (I).Value < 0 then
            return True;
         end if;
      end loop;
      return False;
   end Enum_Disc_Signed;

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
   is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            --  The result is the *stored* discriminant bit pattern,
            --  zero-extended to 64 bits: every consumer (construction
            --  stores, match/contract compares) operates on the
            --  discriminant width with zero-extended loads, so negative
            --  values are masked here once (§4.11.3).
            declare
               DS : constant Natural := Enum_Disc_Size (Enum_Name);
               V  : constant Long_Long_Integer :=
                 D.Variants.Element (I).Value;
            begin
               case DS is
                  when 0      => return 0;
                  when 1 | 2 | 4 =>
                     return V mod (2 ** (8 * DS));
                  when others => return V;
               end case;
            end;
         end if;
      end loop;
      raise Layout_Error with
        "enum '" & Enum_Name & "' has no variant '" & Variant & "'";
   end Variant_Value;

   function Implicit_Wild_Value
     (Enum_Name : String) return Long_Long_Integer
   is
      D : Enum_Decl;
      Candidate : Long_Long_Integer := 0;
   begin
      if not Find_Enum (Enum_Name, D) then
         raise Layout_Error with "unknown enum '" & Enum_Name & "'";
      end if;
      --  Smallest non-negative value not used by a declared variant.
      loop
         declare
            Used : Boolean := False;
         begin
            for I in D.Variants.First_Index .. D.Variants.Last_Index loop
               if D.Variants.Element (I).Value = Candidate then
                  Used := True;
               end if;
            end loop;
            exit when not Used;
            Candidate := Candidate + 1;
         end;
      end loop;
      return Candidate;
   end Implicit_Wild_Value;

   --  Locate a variant declaration within an enum.
   function Find_Variant
     (Enum_Name, Variant : String; Found : out Enum_Variant) return Boolean
   is
      D : Enum_Decl;
   begin
      if not Find_Enum (Enum_Name, D) then
         return False;
      end if;
      for I in D.Variants.First_Index .. D.Variants.Last_Index loop
         if SU.To_String (D.Variants.Element (I).Name) = Variant then
            Found := D.Variants.Element (I);
            return True;
         end if;
      end loop;
      return False;
   end Find_Variant;

   --  KSA size of a named-field group (a variant payload).
   function Group_Size
     (Fields : Kurt.Parser.Struct_Field_Vectors.Vector) return Natural
   is
      Off : Natural := 0;
      Aln : Natural := 1;
   begin
      for I in Fields.First_Index .. Fields.Last_Index loop
         declare
            FT : constant Kurt.Parser.Type_Access := Fields.Element (I).Ty;
         begin
            Off := Ceil (Off, Align_Of (FT));
            Off := Off + Size_Of (FT);
            Aln := Natural'Max (Aln, Align_Of (FT));
         end;
      end loop;
      if Off = 0 then
         return 0;
      end if;
      return Ceil (Off, Aln);
   end Group_Size;

   --  Enum alignment: max of discriminant size and every payload field's
   --  alignment.
   function Enum_Align (Name : String) return Natural is
      D : Enum_Decl;
      --  A void discriminant (width 0) contributes no alignment.
      A : Natural := Natural'Max (1, Enum_Disc_Size (Name));
   begin
      if Find_Enum (Name, D) then
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            declare
               P : constant Kurt.Parser.Struct_Field_Vectors.Vector :=
                 D.Variants.Element (I).Payload;
            begin
               for J in P.First_Index .. P.Last_Index loop
                  A := Natural'Max (A, Align_Of (P.Element (J).Ty));
               end loop;
            end;
         end loop;
      end if;
      return A;
   end Enum_Align;

   --  Offset at which the payload region begins (after the discriminant).
   function Payload_Region_Offset (Name : String) return Natural is
   begin
      return Ceil (Enum_Disc_Size (Name), Enum_Align (Name));
   end Payload_Region_Offset;

   --  Total enum size: discriminant + largest payload, rounded to align.
   function Enum_Size (Name : String) return Natural is
      D      : Enum_Decl;
      Max_PL : Natural := 0;
   begin
      if Find_Enum (Name, D) then
         for I in D.Variants.First_Index .. D.Variants.Last_Index loop
            Max_PL := Natural'Max
              (Max_PL, Group_Size (D.Variants.Element (I).Payload));
         end loop;
      end if;
      if Max_PL = 0 then
         return Enum_Disc_Size (Name);
      end if;
      return Ceil (Payload_Region_Offset (Name) + Max_PL, Enum_Align (Name));
   end Enum_Size;

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
   is
      V   : Enum_Variant;
      Off : Natural := 0;
   begin
      if not Find_Variant (Enum_Name, Variant, V) then
         raise Layout_Error with
           "unknown variant '" & Variant & "' of '" & Enum_Name & "'";
      end if;
      for K in V.Payload.First_Index .. V.Payload.Last_Index loop
         declare
            FT : constant Kurt.Parser.Type_Access := V.Payload.Element (K).Ty;
         begin
            Off := Ceil (Off, Align_Of (FT));
            if K = V.Payload.First_Index + (Field_No - 1) then
               return Payload_Region_Offset (Enum_Name) + Off;
            end if;
            Off := Off + Size_Of (FT);
         end;
      end loop;
      raise Layout_Error with "payload field index out of range";
   end Variant_Field_Offset;

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
   function Align_Of (T : Kurt.Parser.Type_Access) return Natural is
   begin
      if T = null then
         return 8;
      end if;
      case T.Kind is
         when T_Ref =>
            return 8;
         when T_Array =>
            --  §4.6: an array aligns as its element type.
            return Align_Of (T.Elem);
         when T_Range =>
            --  §4.8: { start: T, end: T } aligns as T.
            return Align_Of (T.Rng_Elem);
         when T_Fn =>
            --  §4.10: a subroutine pointer is pointer-sized/aligned.
            return Kurt.Address_Cells;
         when T_Dyn =>
            --  §9.5: a bare `dyn Trait` is unsized; only `&dyn Trait`
            --  (a fat ref) is sized. Align as a pointer pair.
            return 8;
         when T_Tuple =>
            declare
               A : Natural := 1;
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  A := Natural'Max (A, Align_Of (T.Elems.Element (I)));
               end loop;
               return A;
            end;
         when T_Named =>
            declare
               N : constant String := SU.To_String (T.Name);
               D : Struct_Decl;
            begin
               if Is_Verdict (N) then
                  --  §4.5: max of the discriminant (1) and the alignments of
                  --  the payload element types.
                  declare
                     A : Natural := 1;
                  begin
                     for I in T.Args.First_Index .. T.Args.Last_Index loop
                        A := Natural'Max (A, Align_Of (T.Args.Element (I)));
                     end loop;
                     return A;
                  end;
               elsif Find_Struct (N, D) then
                  declare
                     A : Natural := 1;
                  begin
                     --  §4.11.4: a packed struct has alignment 1.
                     if not D.Repr_Packed then
                        for I in D.Fields.First_Index ..
                                 D.Fields.Last_Index
                        loop
                           A := Natural'Max
                             (A, Align_Of (D.Fields.Element (I).Ty));
                        end loop;
                     end if;
                     --  §4.11.5: align(N) raises the minimum alignment.
                     return Natural'Max (A, D.Align_N);
                  end;
               elsif Is_Enum (N) then
                  return Enum_Align (N);
               else
                  return Size_Of (T);  --  numeric: align == size
               end if;
            end;
      end case;
   end Align_Of;

   function Size_Of (T : Kurt.Parser.Type_Access) return Natural is
   begin
      if T = null then
         return 8;
      end if;
      case T.Kind is
         when T_Ref =>
            --  §9.5 / §4.6: a fat reference is two pointers — a reference
            --  to a trait object (ptr + dtable) or to a slice `[T]`
            --  (ptr + len). A thin reference is one pointer.
            if T.Target /= null
              and then (T.Target.Kind = T_Dyn
                        or else (T.Target.Kind = T_Array
                                 and then T.Target.Len = 0))
            then
               return 16;
            end if;
            return 8;  --  pointer width (host arm64)
         when T_Array =>
            --  §4.6: N elements at the element stride. Every Kurt type's
            --  size is a multiple of its alignment, so stride = size.
            --  An unsized slice (Len = 0) has no value size of its own.
            return T.Len * Size_Of (T.Elem);
         when T_Range =>
            --  §4.8: two T fields; size = 2*size(T) (size is a multiple of
            --  align, so `end` sits exactly at size(T)).
            return 2 * Size_Of (T.Rng_Elem);
         when T_Dyn =>
            --  §9.5: `dyn Trait` is unsized (a placeholder); a reference
            --  to it is the fat pair handled in Ref-size code. Report the
            --  fat-pair size so a stray query is harmless.
            return 16;
         when T_Fn =>
            --  §4.10: a subroutine pointer equals `(&raw void)@size`.
            return Kurt.Address_Cells;
         when T_Tuple =>
            --  §4.7 / §4.11: positional fields, KSA-packed.
            declare
               Off : Natural := 0;
               Aln : Natural := 1;
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  declare
                     FT : constant Type_Access := T.Elems.Element (I);
                  begin
                     Off := Ceil (Off, Align_Of (FT)) + Size_Of (FT);
                     Aln := Natural'Max (Aln, Align_Of (FT));
                  end;
               end loop;
               return Ceil (Off, Aln);
            end;
         when T_Named =>
            declare
               N : constant String := SU.To_String (T.Name);
               D : Struct_Decl;
            begin
               --  §4.2.2: uiN/siN occupy N cells (N * cellbits bits).
               if N = "ui1" or else N = "si1" then return 1;
               elsif N = "ui2" or else N = "si2" then return 2;
               elsif N = "ui4" or else N = "si4" then return 4;
               elsif N = "ui8" or else N = "si8" then return 8;
               elsif N = "ui16" or else N = "si16" then return 16;
               elsif N = "ui32" or else N = "si32" then return 32;
               --  Floating-point types (§4): size = (1 + e + m) bits / 8.
               elsif N = "fe5m10" or else N = "fe8m7" then return 2;
               elsif N = "fe8m23" then return 4;
               elsif N = "fe11m52" then return 8;
               elsif N = "fe15m112" then return 16;
               elsif N = "fe19m236" then return 32;
               elsif N = "uaddr" or else N = "saddr" then
                  return Kurt.Address_Cells;
               elsif N = "bool" then return 1;
               elsif N = "void" then return 0;
               elsif Is_Verdict (N) then
                  --  §4.5 verdict.<Ok, Err>: ui1 discriminant + the larger
                  --  payload, from the type arguments.
                  declare
                     A   : constant Natural := Align_Of (T);
                     POf : constant Natural := Ceil (1, A);
                     PSz : Natural := 0;
                  begin
                     for I in T.Args.First_Index .. T.Args.Last_Index loop
                        PSz := Natural'Max (PSz, Size_Of (T.Args.Element (I)));
                     end loop;
                     if PSz = 0 then
                        return Ceil (1, A);   --  e.g. verdict.<void, void>
                     end if;
                     return Ceil (POf + PSz, A);
                  end;
               elsif Is_Enum (N) then
                  return Enum_Size (N);
               elsif Find_Struct (N, D) then
                  --  §4.11.2 struct layout (§4.11.4 packed: no
                  --  inter-field padding; §4.11.5 align(N) raises the
                  --  minimum alignment, which rounds the total size).
                  declare
                     Off : Natural := 0;
                     Aln : Natural := 1;
                  begin
                     for I in D.Fields.First_Index .. D.Fields.Last_Index
                     loop
                        declare
                           FT : constant Type_Access :=
                             D.Fields.Element (I).Ty;
                        begin
                           if not D.Repr_Packed then
                              Off := Ceil (Off, Align_Of (FT));
                              Aln := Natural'Max (Aln, Align_Of (FT));
                           end if;
                           Off := Off + Size_Of (FT);
                        end;
                     end loop;
                     if D.Repr_Packed then
                        Aln := 1;
                     end if;
                     Aln := Natural'Max (Aln, D.Align_N);
                     return Ceil (Off, Aln);
                  end;
               else
                  return 8;  --  unknown named type
               end if;
            end;
      end case;
   end Size_Of;

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
