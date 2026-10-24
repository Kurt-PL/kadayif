package body KSA is

   use Types;

   --  Kurt standard alignment으로 한 필드를 놓는다: Off는 지금까지의 끝,
   --  Placed는 그 필드의 오프셋
   procedure Place
     (Field_Size, Field_Align : Natural;
      Off      : in out Natural;
      Max_Algn : in out Natural;
      Placed   : out Natural) is
   begin
      Placed := Round_Up (Off, Field_Align);
      Off := Placed + Field_Size;
      Max_Algn := Natural'Max (Max_Algn, Field_Align);
   end Place;

   function Packed (A, Pack : Natural) return Natural is
     (if Pack = 0 then A else Natural'Min (A, Pack));

   --  필드 열을 구조체로 배치하고 오프셋을 기록한다
   procedure Lay_Out_Fields
     (Fields : in out Field_Vectors.Vector;
      Pack   : Natural;
      S, A   : out Natural)
   is
      Off : Natural := 0;
   begin
      A := 0;
      for I in Fields.First_Index .. Fields.Last_Index loop
         declare
            F : Field_Info := Fields (I);
         begin
            Place (Size (F.Ty), Packed (Align (F.Ty), Pack), Off, A,
                   F.Offset);
            Fields.Replace_Element (I, F);
         end;
      end loop;
      S := Round_Up (Off, A);
   end Lay_Out_Fields;

   procedure Lay_Out (T : Type_Id) is
      C : Composite_Info := Info (T);
   begin
      if C.State = Laid_Out then
         return;
      elsif C.State = Laying_Out then
         raise Layout_Cycle;
      end if;
      C.State := Laying_Out;
      Set_Info (T, C);

      if C.Kind = Struct_Type then
         Lay_Out_Fields (C.Fields, C.Pack, C.Size, C.Align);
      else
         --  [판별자 타입, 변형 구조체들의 최대] (§5.11.2)
         declare
            V_Size, V_Align : Natural := 0;
            Off, A          : Natural := 0;
         begin
            for I in C.Variants.First_Index .. C.Variants.Last_Index loop
               declare
                  V : Variant_Info := C.Variants (I);
               begin
                  Lay_Out_Fields (V.Fields, C.Pack, V.Size, V.Align);
                  C.Variants.Replace_Element (I, V);
                  V_Size := Natural'Max (V_Size, V.Size);
                  V_Align := Natural'Max (V_Align, V.Align);
               end;
            end loop;
            V_Size := Round_Up (V_Size, V_Align);
            declare
               Disc_Off : Natural;
            begin
               Place (Size (C.Disc), Align (C.Disc), Off, A, Disc_Off);
               Place (V_Size, V_Align, Off, A, C.Payload_Offset);
            end;
            C.Align := A;
            C.Size := Round_Up (Off, A);
         end;
      end if;

      if C.Min_Align > 0 then
         C.Align := Natural'Max (C.Align, C.Min_Align);
         C.Size := Round_Up (C.Size, C.Align);
      end if;
      C.State := Laid_Out;
      Set_Info (T, C);
   exception
      when Layout_Cycle =>
         C.State := Not_Laid_Out;
         Set_Info (T, C);
         raise;
   end Lay_Out;

   --  verdict[T, F]: 판별자 ui1, 변형마다 필드 하나 (§5.6)
   procedure Verdict_Layout (T : Type_Id; S, A, Payload : out Natural) is
      R       : constant Type_Rec := Get (T);
      V_Align : constant Natural :=
        Natural'Max (Align (R.Pass), Align (R.Fail));
      V_Size  : constant Natural := Round_Up
        (Natural'Max (Round_Up (Size (R.Pass), Align (R.Pass)),
                      Round_Up (Size (R.Fail), Align (R.Fail))), V_Align);
      Off     : Natural := 0;
      Disc    : Natural;
   begin
      A := 0;
      Place (1, 1, Off, A, Disc);
      Place (V_Size, V_Align, Off, A, Payload);
      S := Round_Up (Off, A);
   end Verdict_Layout;

   procedure Anon_Layout
     (T : Type_Id; Index : Natural; S, A, Field_Off : out Natural)
   is
      Off : Natural := 0;
      Pos : Natural;
   begin
      A := 0;
      Field_Off := 0;
      for I in 1 .. Natural (Get (T).Params.Length) loop
         declare
            F : constant Type_Id := Get (T).Params (I);
         begin
            Place (Size (F), Align (F), Off, A, Pos);
            if I = Index then
               Field_Off := Pos;
            end if;
         end;
      end loop;
      S := Round_Up (Off, A);
   end Anon_Layout;

   function Size (T : Type_Id) return Natural is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error => return 1;
         when Ty_Void | Ty_Never => return 0;
         when Ty_Int => return R.Cells;
         when Ty_Ref | Ty_Fn => return Reference_Cells;
         when Ty_Slice => return 2 * Reference_Cells;
         when Ty_Array => return R.Length * Size (R.Target);
         when Ty_Verdict =>
            declare
               S, A, P : Natural;
            begin
               Verdict_Layout (T, S, A, P);
               return S;
            end;
         when Ty_Anon =>
            declare
               S, A, F : Natural;
            begin
               Anon_Layout (T, 0, S, A, F);
               return S;
            end;
         when Ty_Composite =>
            Lay_Out (T);
            return Info (T).Size;
      end case;
   end Size;

   function Align (T : Type_Id) return Natural is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error => return 1;
         when Ty_Void | Ty_Never => return 0;
         when Ty_Int => return R.Cells;
         when Ty_Ref | Ty_Fn | Ty_Slice => return Reference_Cells;
         when Ty_Array => return Align (R.Target);
         when Ty_Verdict =>
            declare
               S, A, P : Natural;
            begin
               Verdict_Layout (T, S, A, P);
               return A;
            end;
         when Ty_Anon =>
            declare
               S, A, F : Natural;
            begin
               Anon_Layout (T, 0, S, A, F);
               return A;
            end;
         when Ty_Composite =>
            Lay_Out (T);
            return Info (T).Align;
      end case;
   end Align;

   function Field_Offset (T : Type_Id; Index : Positive) return Natural is
   begin
      if Kind (T) = Ty_Anon then
         declare
            S, A, F : Natural;
         begin
            Anon_Layout (T, Index, S, A, F);
            return F;
         end;
      end if;
      Lay_Out (T);
      return Field (T, Index).Offset;
   end Field_Offset;

   function Disc_Type (T : Type_Id) return Type_Id is
     (if Kind (T) = Ty_Verdict then Int (False, 1) else Info (T).Disc);

   function Variant_Field_Offset
     (T : Type_Id; Variant, Field : Positive) return Natural
   is
   begin
      if Kind (T) = Ty_Verdict then
         declare
            S, A, P : Natural;
         begin
            Verdict_Layout (T, S, A, P);
            return P;
         end;
      end if;
      Lay_Out (T);
      declare
         V : constant Variant_Info := Types.Variant (T, Variant);
      begin
         return Info (T).Payload_Offset + V.Fields (Field).Offset;
      end;
   end Variant_Field_Offset;

end KSA;
