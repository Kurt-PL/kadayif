with Ada.Strings.Fixed;
with Ada.Strings.Unbounded;

package body Types is

   type Natural_Array is array (Positive range <>) of Natural;

   package Rec_Vectors is new Ada.Containers.Vectors (Positive, Type_Rec);
   Table : Rec_Vectors.Vector;

   function Same (L, R : Type_Rec) return Boolean is
      use type Type_Vectors.Vector;
      use type Idents.Ident;
   begin
      if L.Kind /= R.Kind then
         return False;
      end if;
      case L.Kind is
         when Ty_Error | Ty_Void | Ty_Never =>
            return True;
         when Ty_Int =>
            return L.Signed = R.Signed and then L.Cells = R.Cells
              and then L.Addr = R.Addr;
         when Ty_Ref | Ty_Slice =>
            return L.Ref_Tribe = R.Ref_Tribe and then L.Mods = R.Mods
              and then L.Target = R.Target;
         when Ty_Array =>
            return L.Target = R.Target and then L.Length = R.Length;
         when Ty_Verdict =>
            return L.Pass = R.Pass and then L.Fail = R.Fail;
         when Ty_Composite =>
            return L.Composite = R.Composite;
         when Ty_Anon =>
            return L.Params = R.Params;
         when Ty_Fn =>
            return L.Params = R.Params and then L.Ret = R.Ret
              and then L.Variadic = R.Variadic
              and then L.Airside = R.Airside
              and then L.Invocation = R.Invocation;
      end case;
   end Same;

   function Make (R : Type_Rec) return Type_Id is
   begin
      for I in Table.First_Index .. Table.Last_Index loop
         if Same (Table (I), R) then
            return Type_Id (I);
         end if;
      end loop;
      Table.Append (R);
      return Type_Id (Table.Last_Index);
   end Make;

   function Get (T : Type_Id) return Type_Rec is (Table (Positive (T)));

   function Kind (T : Type_Id) return Type_Kind is
     (if T = No_Type then Ty_Error else Table (Positive (T)).Kind);

   function Simple (K : Type_Kind) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := K;
      return Make (R);
   end Simple;

   function Error_Type return Type_Id is (Simple (Ty_Error));
   function Void return Type_Id is (Simple (Ty_Void));
   function Never return Type_Id is (Simple (Ty_Never));

   function Int (Signed : Boolean; Cells : Positive) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := Ty_Int;
      R.Signed := Signed;
      R.Cells := Cells;
      return Make (R);
   end Int;

   --  주소 폭은 프로그램 기계의 것 (AArch64: 64비트 = 8셀)
   function Addr_Int (Signed : Boolean) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := Ty_Int;
      R.Signed := Signed;
      R.Cells := 8;
      R.Addr := True;
      return Make (R);
   end Addr_Int;

   function Uaddr return Type_Id is (Addr_Int (False));
   function Saddr return Type_Id is (Addr_Int (True));

   function Verdict (Pass, Fail : Type_Id) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := Ty_Verdict;
      R.Pass := Pass;
      R.Fail := Fail;
      return Make (R);
   end Verdict;

   function Bool return Type_Id is (Verdict (Void, Void));

   function Ref (Of_Type : Type_Id; T : Tribe; M : Modifiers := (others => <>))
                 return Type_Id
   is
      R : Type_Rec;
   begin
      R.Kind := Ty_Ref;
      R.Ref_Tribe := T;
      R.Mods := M;
      R.Target := Of_Type;
      return Make (R);
   end Ref;

   function Array_Of (Elem : Type_Id; Length : Natural) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := Ty_Array;
      R.Target := Elem;
      R.Length := Length;
      return Make (R);
   end Array_Of;

   function New_Composite (Info : Composite_Info) return Type_Id is
      R : Type_Rec;
   begin
      Composites.Append (Info);
      R.Kind := Ty_Composite;
      R.Composite := Composites.Last_Index;
      return Make (R);
   end New_Composite;

   function Info (T : Type_Id) return Composite_Info is
     (Composites (Get (T).Composite));

   function Field (T : Type_Id; Index : Positive) return Field_Info is
      C : constant Composite_Info := Info (T);
   begin
      return C.Fields (Index);
   end Field;

   function Variant (T : Type_Id; Index : Positive) return Variant_Info is
      C : constant Composite_Info := Info (T);
   begin
      return C.Variants (Index);
   end Variant;

   procedure Set_Info (T : Type_Id; Info : Composite_Info) is
   begin
      Composites.Replace_Element (Get (T).Composite, Info);
   end Set_Info;

   function Anon (Fields : Type_Vectors.Vector) return Type_Id is
      R : Type_Rec;
   begin
      R.Kind := Ty_Anon;
      R.Params := Fields;
      return Make (R);
   end Anon;

   function Is_Contract (T : Type_Id) return Boolean is
     (Kind (T) = Ty_Verdict
      or else (Kind (T) = Ty_Composite
               and then Info (T).Kind = Contract_Type));

   function Is_Variant (T : Type_Id) return Boolean is
     (Kind (T) = Ty_Verdict
      or else (Kind (T) = Ty_Composite and then Info (T).Kind /= Struct_Type));

   function Is_Copyable (T : Type_Id) return Boolean is
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error | Ty_Void | Ty_Never | Ty_Int | Ty_Fn =>
            return True;
         when Ty_Ref | Ty_Slice =>
            --  §8.2: 배타 참조는 복사할 수 없다
            return R.Ref_Tribe /= Exclusive;
         when Ty_Array =>
            return Is_Copyable (R.Target);
         when Ty_Anon =>
            return (for all P of R.Params => Is_Copyable (P));
         when Ty_Verdict =>
            return Is_Copyable (R.Pass) and then Is_Copyable (R.Fail);
         when Ty_Composite =>
            declare
               C : constant Composite_Info := Info (T);
            begin
               if not C.Copyable or else C.State = Laying_Out then
                  return False;
               end if;
               for F of C.Fields loop
                  if not F.Pad and then not Is_Copyable (F.Ty) then
                     return False;
                  end if;
               end loop;
               for V of C.Variants loop
                  for F of V.Fields loop
                     if not F.Pad and then not Is_Copyable (F.Ty) then
                        return False;
                     end if;
                  end loop;
               end loop;
               return True;
            end;
      end case;
   end Is_Copyable;

   function Builtin (Name : String) return Type_Id is
   begin
      if Name = "void" then
         return Void;
      elsif Name = "uaddr" then
         return Uaddr;
      elsif Name = "saddr" then
         return Saddr;
      elsif Name'Length in 3 .. 4 and then Name (Name'First + 1) = 'i'
        and then Name (Name'First) in 'u' | 's'
      then
         declare
            Digits_Part : constant String :=
              Name (Name'First + 2 .. Name'Last);
         begin
            for Cells of Natural_Array'(1, 2, 4, 8, 16, 32) loop
               if Digits_Part = Ada.Strings.Fixed.Trim
                 (Cells'Image, Ada.Strings.Left)
               then
                  return Int (Name (Name'First) = 's', Cells);
               end if;
            end loop;
         end;
      end if;
      return No_Type;
   end Builtin;

   function Tribe_Image (T : Tribe) return String is
     (case T is
        when Shared    => "&",
        when Exclusive => "$",
        when Unmanaged => "%");

   function Mods_Image (M : Modifiers) return String is
     ((if M.Volatile then "volatile " else "")
      & (if M.Mut then "mut " else "")
      & (if M.Atomic then "atomic " else "")
      & (if M.Guard then "guard " else ""));

   function Trim (N : Integer) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   function Image (T : Type_Id) return String is
      use Ada.Strings.Unbounded;
      R : constant Type_Rec := Get (T);
   begin
      case R.Kind is
         when Ty_Error => return "<error>";
         when Ty_Void  => return "void";
         when Ty_Never => return "!";
         when Ty_Int =>
            if R.Addr then
               return (if R.Signed then "saddr" else "uaddr");
            end if;
            return (if R.Signed then "si" else "ui") & Trim (R.Cells);
         when Ty_Ref =>
            return Tribe_Image (R.Ref_Tribe) & Mods_Image (R.Mods)
              & Image (R.Target);
         when Ty_Slice =>
            return Tribe_Image (R.Ref_Tribe) & Mods_Image (R.Mods)
              & "[" & Image (R.Target) & "]";
         when Ty_Array =>
            return "[" & Image (R.Target) & "; " & Trim (R.Length) & "]";
         when Ty_Verdict =>
            return "verdict[" & Image (R.Pass) & ", " & Image (R.Fail)
              & "]";
         when Ty_Composite =>
            return Idents.Image (Info (T).Name);
         when Ty_Anon =>
            declare
               Fields : Unbounded_String;
            begin
               for P of R.Params loop
                  if Length (Fields) > 0 then
                     Append (Fields, ", ");
                  end if;
                  Append (Fields, Image (P));
               end loop;
               return ".{" & To_String (Fields) & "}";
            end;
         when Ty_Fn =>
            declare
               Params : Unbounded_String;
            begin
               for P of R.Params loop
                  if Length (Params) > 0 then
                     Append (Params, ", ");
                  end if;
                  Append (Params, Image (P));
               end loop;
               return (if R.Airside then "airside " else "") & "fn("
                 & To_String (Params) & ") -> " & Image (R.Ret);
            end;
      end case;
   end Image;

end Types;
