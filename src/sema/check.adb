with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;
with Diagnostics;
with Idents;
with Names;
with Symbols;
with Tokens;
with Types;

package body Check is

   use Ada.Numerics.Big_Numbers.Big_Integers;
   use Ada.Strings.Unbounded;
   use AST;
   use Symbols;
   use Tokens;
   use Types;
   use type Idents.Ident;

   ---------------------------------------------------------------------
   --  분석 상태

   type Loop_Entry is record
      Node  : Node_Id;
      Label : Idents.Ident;
   end record;
   package Loop_Vectors is new Ada.Containers.Vectors (Positive, Loop_Entry);

   Fn_Ret        : Type_Id := No_Type;
   Airside_Depth : Natural := 0;
   Loops         : Loop_Vectors.Vector;

   function Get (N : Node_Id) return Node is (Nodes (Positive (N)));

   procedure Set_Type (N : Node_Id; T : Type_Id) is
   begin
      Nodes (Positive (N)).Ty := Natural (T);
   end Set_Type;

   function Type_Of (N : Node_Id) return Type_Id is
     (Type_Id (Nodes (Positive (N)).Ty));

   procedure Error (N : Node_Id; Message : String) is
   begin
      Diagnostics.Error (Get (N).Pos, Message);
   end Error;

   procedure Unimplemented (N : Node_Id; What : String) is
   begin
      Diagnostics.Unimplemented (Get (N).Pos, What);
   end Unimplemented;

   function Quote (T : Type_Id) return String is ("'" & Image (T) & "'");

   ---------------------------------------------------------------------
   --  정수 리터럴 값 (§3.5.1)

   function Digit_Value (C : Character) return Natural is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when others     => Character'Pos (C) - Character'Pos ('A') + 10);

   function Int_Value (N : Node_Id) return Big_Integer is
      Text  : constant String := To_String (Get (N).Text);
      Neg   : constant Boolean := Text (Text'First) = '-';
      First : Positive := Text'First + (if Neg then 1 else 0);
      Base  : Positive := 10;
      V     : Big_Integer := 0;
   begin
      if Get (N).Kind = N_Char_Lit then
         return To_Big_Integer (Character'Pos (Text (Text'First)));
      end if;
      if Text'Last >= First + 1 and then Text (First) = '0' then
         case Text (First + 1) is
            when 'b' | 'B' => Base := 2;
            when 'q' | 'Q' => Base := 4;
            when 'o' | 'O' => Base := 8;
            when 'x' | 'X' => Base := 16;
            when others    => null;
         end case;
         if Base /= 10 then
            First := First + 2;
         end if;
      end if;
      for C of Text (First .. Text'Last) loop
         if C /= '_' then
            V := V * To_Big_Integer (Base)
              + To_Big_Integer (Digit_Value (C));
         end if;
      end loop;
      return (if Neg then -V else V);
   end Int_Value;

   function Fits (V : Big_Integer; T : Type_Id) return Boolean is
      Bits : constant Natural := 8 * Get (T).Cells;
   begin
      if Get (T).Signed then
         return V >= -(2 ** (Bits - 1)) and then V < 2 ** (Bits - 1);
      end if;
      return V >= 0 and then V < 2 ** Bits;
   end Fits;

   ---------------------------------------------------------------------
   --  타입 해석

   function Resolve_Type (N : Node_Id) return Type_Id;

   function Resolve_Path_Type (N : Node_Id) return Type_Id is
      Path : constant Node := Get (N);
   begin
      if Path.List.Count /= 1 then
         Unimplemented (N, "qualified type paths (§10.7)");
         return Error_Type;
      end if;
      declare
         Seg  : constant Node := Get (Item (Path.List, 1));
         Name : constant String := Idents.Image (Seg.Name);
         T    : constant Type_Id := Builtin (Name);
      begin
         if Name = "verdict" then
            if Seg.List.Count /= 2 then
               Error (N, "'verdict' takes two generic arguments");
               return Error_Type;
            end if;
            return Verdict (Resolve_Type (Item (Seg.List, 1)),
                            Resolve_Type (Item (Seg.List, 2)));
         elsif Seg.List.Count > 0 then
            Unimplemented (N, "generic arguments (§4.10)");
            return Error_Type;
         elsif T /= No_Type then
            return T;
         elsif Name'Length > 2 and then Name (Name'First .. Name'First + 1)
           = "fe"
         then
            Unimplemented
              (N, "floating radix point number types (§5.4)");
            return Error_Type;
         elsif Names.Lookup (Seg.Name) /= No_Symbol then
            Unimplemented (N, "declared types (§4.7, §4.8, §4.9)");
            return Error_Type;
         end if;
         Error (N, "unknown type '" & Name & "'");
         return Error_Type;
      end;
   end Resolve_Path_Type;

   function Ref_Tribe (Op : Token_Kind) return Tribe is
     (case Op is
        when P_Dollar  => Exclusive,
        when P_Percent => Unmanaged,
        when others    => Shared);

   function Mods_Of (N : Node) return Modifiers is
     ((Volatile => N.Flags (F_Volatile), Mut => N.Flags (F_Mut),
       Atomic => N.Flags (F_Atomic), Guard => N.Flags (F_Guard)));

   --  §8.2.1: atomic과 guard는 함께 오지 못하고, $에는 mut, atomic,
   --  guard가 오지 못한다.
   function Valid_Mods (N : Node_Id; T : Tribe; M : Modifiers)
                        return Boolean is
   begin
      if M.Atomic and then M.Guard then
         Error (N, "a reference shall not carry both atomic and guard");
         return False;
      elsif T = Exclusive and then (M.Mut or else M.Atomic or else M.Guard)
      then
         Error (N, "an exclusive reference shall not carry mut, atomic,"
                & " or guard");
         return False;
      elsif M.Atomic or else M.Guard then
         Unimplemented (N, "atomic references (§8.4)");
         return False;
      end if;
      return True;
   end Valid_Mods;

   function Resolve_Type (N : Node_Id) return Type_Id is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Path =>
            return Resolve_Path_Type (N);
         when N_Ref_Type | N_Slice_Type =>
            if R.Op = T_EOF then
               Error (N, "a slice type appears only as a reference");
               return Error_Type;
            end if;
            declare
               T : constant Tribe := Ref_Tribe (R.Op);
               M : constant Modifiers := Mods_Of (R);
               Target : constant Type_Id := Resolve_Type (R.A);
               Rec : Type_Rec;
            begin
               if not Valid_Mods (N, T, M) then
                  return Error_Type;
               end if;
               Rec.Kind := (if R.Kind = N_Slice_Type then Ty_Slice
                            else Ty_Ref);
               Rec.Ref_Tribe := T;
               Rec.Mods := M;
               Rec.Target := Target;
               return Make (Rec);
            end;
         when N_Array_Type =>
            declare
               Elem : constant Type_Id := Resolve_Type (R.A);
            begin
               if Kind (R.B) /= N_Int_Lit or else Get (R.B).A /= No_Node
               then
                  Unimplemented
                    (R.B, "array lengths other than an unsuffixed integer"
                     & " literal (§6.11)");
                  return Error_Type;
               end if;
               Set_Type (R.B, Uaddr);
               if not Fits (Int_Value (R.B), Uaddr)
                 or else Int_Value (R.B) > To_Big_Integer (Integer'Last)
               then
                  Error (R.B, "array length out of range");
                  return Error_Type;
               end if;
               return Array_Of
                 (Elem, To_Integer (Int_Value (R.B)));
            end;
         when N_Never_Type =>
            return Never;
         when N_Infer_Type =>
            Unimplemented (N, "the inferred type '?' (§5.12)");
            return Error_Type;
         when others =>
            Error (N, "expected type");
            return Error_Type;
      end case;
   end Resolve_Type;

   ---------------------------------------------------------------------
   --  선언 수집 (§10.2 3단계)

   function Fn_Type (N : Node_Id; Airside : Boolean) return Type_Id is
      R   : constant Node := Get (N);
      Rec : Type_Rec;
   begin
      Rec.Kind := Ty_Fn;
      for I in 1 .. R.List.Count loop
         Rec.Params.Append (Resolve_Type (Get (Item (R.List, I)).A));
      end loop;
      Rec.Ret := (if R.A = No_Node then Void else Resolve_Type (R.A));
      Rec.Variadic := R.Flags (F_Variadic);
      Rec.Airside := Airside;
      Rec.Invocation := R.Name2;
      return Make (Rec);
   end Fn_Type;

   function New_Fn_Symbol (N : Node_Id; Dyn : Boolean) return Symbol_Id is
      R : constant Node := Get (N);
      S : Symbol;
   begin
      if R.Name2 /= Idents.No_Ident
        and then Idents.Image (R.Name2) /= "native"
      then
         Error (N, "unknown invocation interface '"
                & Idents.Image (R.Name2) & "'");
      end if;
      S.Kind := Sym_Fn;
      S.Name := R.Name;
      S.Pos := R.Pos;
      S.Decl := Natural (N);
      S.Dyn := Dyn;
      S.Pub := R.Flags (F_Pub);
      --  #dyn 블록의 서브루틴은 airside fn이다 (§10.5)
      S.Ty := Natural (Fn_Type (N, R.Flags (F_Airside) or else Dyn));
      if Dyn or else R.Flags (F_Extern) then
         S.Link_Name := To_Unbounded_String (Idents.Image (R.Name));
      end if;
      return Add (S);
   end New_Fn_Symbol;

   procedure Collect (Unit : Node_Id) is
      U : constant Node := Get (Unit);
   begin
      for I in 1 .. U.List.Count loop
         declare
            N : constant Node_Id := Item (U.List, I);
            R : constant Node := Get (N);
         begin
            if Names.Clash (R.Name) /= No_Symbol then
               Names.Report_Clash (R.Pos, R.Name);
            end if;
            case R.Kind is
               when N_Fn =>
                  declare
                     S : constant Symbol_Id := New_Fn_Symbol (N, False);
                  begin
                     Nodes (Positive (N)).Sym := Natural (S);
                     Names.Declare_Global (R.Name, S);
                  end;
               when N_Dyn =>
                  if R.Flags (F_Xlat) then
                     Unimplemented (N, "#dyn xlat (§10.5)");
                  end if;
                  declare
                     NS_Rec : Symbol;
                     NS     : Symbol_Id;
                  begin
                     NS_Rec.Kind := Sym_Namespace;
                     NS_Rec.Name := R.Name;
                     NS_Rec.Pos := R.Pos;
                     NS_Rec.Decl := Natural (N);
                     NS := Add (NS_Rec);
                     Nodes (Positive (N)).Sym := Natural (NS);
                     Names.Declare_Global (R.Name, NS);
                     for J in 1 .. R.List.Count loop
                        declare
                           M  : constant Node_Id := Item (R.List, J);
                           MR : constant Node := Get (M);
                           S  : Symbol_Id;
                        begin
                           if Names.Lookup_Member (NS, MR.Name) /= No_Symbol
                           then
                              Names.Report_Clash (MR.Pos, MR.Name);
                           end if;
                           S := New_Fn_Symbol (M, True);
                           Nodes (Positive (M)).Sym := Natural (S);
                           Names.Declare_Member (NS, MR.Name, S);
                        end;
                     end loop;
                  end;
               when others =>
                  null;
            end case;
         end;
      end loop;
   end Collect;

   ---------------------------------------------------------------------
   --  식 검사

   function Check_Expr (N : Node_Id; Expected : Type_Id) return Type_Id;

   --  N을 검사하고 그 타입이 Expected에 배정될 수 있는지 본다 (§6.8)
   procedure Check_Against (N : Node_Id; Expected : Type_Id) is
      T : constant Type_Id := Check_Expr (N, Expected);
   begin
      if T /= Expected and then Kind (T) not in Ty_Error | Ty_Never
        and then Kind (Expected) /= Ty_Error
      then
         Error (N, "expected " & Quote (Expected) & ", found " & Quote (T));
      end if;
   end Check_Against;

   --  합성으로 타입이 정해지지 않는 식: 접미사 없는 정수 리터럴과 그
   --  부호 붙임, 그런 피연산자끼리의 산술 (§5.12)
   function Undetermined (N : Node_Id) return Boolean is
      R : constant Node := (if N = No_Node then (others => <>) else Get (N));
   begin
      case R.Kind is
         when N_Int_Lit =>
            return R.A = No_Node;
         when N_Unary =>
            return R.Op in P_Minus | P_Plus | P_Bang
              and then Undetermined (R.A);
         when N_Binary =>
            return R.Op in P_Plus | P_Minus | P_Star | P_Slash | P_Percent
                         | P_Amp | P_Pipe | P_Caret
              and then Undetermined (R.A) and then Undetermined (R.B);
         when others =>
            return False;
      end case;
   end Undetermined;

   --  범위 검사 없이 리터럴의 타입만 정한다
   function Literal_Type (N : Node_Id; Expected : Type_Id) return Type_Id
   is
      R : constant Node := Get (N);
      T : Type_Id;
   begin
      if R.A /= No_Node then
         T := Resolve_Type (R.A);
         if Kind (T) = Ty_Error then
            return T;
         elsif not Is_Int (T) then
            Error (N, "the type suffix of an integer literal shall name an"
                   & " integer type");
            return Error_Type;
         end if;
      elsif Is_Int (Expected) then
         T := Expected;
      elsif Expected = No_Type then
         T := Saddr;
         Diagnostics.Warn (R.Pos, "default type 'saddr' applied to integer"
                           & " literal");
      elsif Kind (Expected) = Ty_Error then
         return Expected;
      else
         Error (N, "an integer literal cannot have type " & Quote (Expected));
         return Error_Type;
      end if;
      return T;
   end Literal_Type;

   function Check_Int_Literal (N : Node_Id; Expected : Type_Id)
                               return Type_Id
   is
      T : constant Type_Id := Literal_Type (N, Expected);
   begin
      if Is_Int (T) and then not Fits (Int_Value (N), T) then
         Error (N, "value does not fit in " & Quote (T));
         return Error_Type;
      end if;
      return T;
   end Check_Int_Literal;

   --  airside 안에서만 허용되는 연산 (§2.7)
   procedure Require_Airside (N : Node_Id; What : String) is
   begin
      if Airside_Depth = 0 then
         Error (N, What & " requires airside");
      end if;
   end Require_Airside;

   --  이름 식이 가리키는 심볼
   function Resolve_Name (N : Node_Id) return Symbol_Id is
      Path : constant Node := Get (Get (N).A);
      S    : Symbol_Id;
   begin
      S := Names.Lookup (Get (Item (Path.List, 1)).Name);
      if S = No_Symbol then
         Error (N, "unknown name '"
                & Idents.Image (Get (Item (Path.List, 1)).Name) & "'");
         return No_Symbol;
      end if;
      for I in 2 .. Path.List.Count loop
         declare
            Seg : constant Node := Get (Item (Path.List, I));
         begin
            if Symbols.Get (S).Kind /= Sym_Namespace then
               Error (N, "'" & Idents.Image (Symbols.Get (S).Name)
                      & "' is not a namespace");
               return No_Symbol;
            end if;
            S := Names.Lookup_Member (S, Seg.Name);
            if S = No_Symbol then
               Error (N, "unknown name '" & Idents.Image (Seg.Name) & "'");
               return No_Symbol;
            end if;
         end;
      end loop;
      for I in 1 .. Path.List.Count loop
         if Get (Item (Path.List, I)).List.Count > 0 then
            Unimplemented (N, "generic arguments (§4.10)");
            return No_Symbol;
         end if;
      end loop;
      Nodes (Positive (N)).Sym := Natural (S);
      return S;
   end Resolve_Name;

   --  저장할 수 있는 객체 식인가 (§6.8)
   procedure Check_Place (N : Node_Id) is
      R : constant Node := Get (N);
   begin
      case R.Kind is
         when N_Name =>
            if R.Sym /= 0 then
               declare
                  S : constant Symbol := Symbols.Get (Symbol_Id (R.Sym));
               begin
                  if S.Kind not in Sym_Local | Sym_Param then
                     Error (N, "'" & Idents.Image (S.Name)
                            & "' is not an object");
                  elsif not S.Mutable then
                     Error (N, "'" & Idents.Image (S.Name)
                            & "' is a single-assignment binding");
                  end if;
               end;
            end if;
         when N_Unary =>
            if R.Op = P_Star then
               declare
                  RT : constant Type_Id := Type_Of (R.A);
               begin
                  if Kind (RT) = Ty_Ref
                    and then not Get (RT).Mods.Mut
                    and then Get (RT).Ref_Tribe /= Exclusive
                  then
                     Error (N, "a store through " & Quote (RT)
                            & " is not permitted");
                  end if;
               end;
            else
               Error (N, "expected an object expression");
            end if;
         when others =>
            Error (N, "expected an object expression");
      end case;
   end Check_Place;

   function Check_Call (N : Node_Id) return Type_Id is
      R      : constant Node := Get (N);
      S      : Symbol_Id;
      Fn     : Type_Rec;
      Params : Natural;
   begin
      if Kind (R.A) /= N_Name then
         Unimplemented (N, "invocation through a subroutine pointer"
                        & " (§6.3.1)");
         return Error_Type;
      end if;
      S := Resolve_Name (R.A);
      if S = No_Symbol then
         return Error_Type;
      elsif Symbols.Get (S).Kind /= Sym_Fn then
         Unimplemented (N, "invocation through a subroutine pointer"
                        & " (§6.3.1)");
         return Error_Type;
      end if;
      Fn := Get (Type_Id (Symbols.Get (S).Ty));
      Set_Type (R.A, Type_Id (Symbols.Get (S).Ty));
      Params := Natural (Fn.Params.Length);

      if R.List.Count < Params
        or else (R.List.Count > Params and then not Fn.Variadic)
      then
         Error (N, "'" & Idents.Image (Symbols.Get (S).Name) & "' takes"
                & Params'Image & " argument"
                & (if Params = 1 then "" else "s") & ", given"
                & R.List.Count'Image);
      end if;

      for I in 1 .. R.List.Count loop
         declare
            Arg : constant Node_Id := Item (R.List, I);
         begin
            if I <= Params then
               Check_Against (Arg, Fn.Params.Element (I));
            else
               --  가변 인자: variadic bound를 만족하는 타입 (§9.7.5)
               declare
                  T : constant Type_Id := Check_Expr (Arg, No_Type);
               begin
                  if Kind (T) not in Ty_Int | Ty_Ref | Ty_Error then
                     Unimplemented (Arg, "variadic arguments of type "
                                    & Quote (T) & " (§9.7.5)");
                  end if;
               end;
            end if;
         end;
      end loop;

      if Fn.Airside then
         Require_Airside (N, "invoking an airside subroutine");
      end if;
      return Fn.Ret;
   end Check_Call;

   function Check_Unary (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
   begin
      case R.Op is
         when P_Minus | P_Plus =>
            --  음수 리터럴: '-'와 리터럴이 함께 부정을 나타낸다 (§3.5.1)
            if R.Op = P_Minus and then Kind (R.A) = N_Int_Lit then
               declare
                  T : constant Type_Id := Literal_Type (R.A, Expected);
               begin
                  Set_Type (R.A, T);
                  if Is_Int (T) and then Fits (-Int_Value (R.A), T) then
                     declare
                        Folded : Node := Get (N);
                     begin
                        Folded.Kind := N_Int_Lit;
                        Folded.Text := "-" & Get (R.A).Text;
                        Folded.A := Get (R.A).A;
                        Nodes.Replace_Element (Positive (N), Folded);
                     end;
                     return T;
                  elsif Is_Int (T) and then not Fits (Int_Value (R.A), T)
                  then
                     Error (R.A, "value does not fit in " & Quote (T));
                     return Error_Type;
                  end if;
                  --  부정이 맞지 않으면 리터럴은 제 값을 나타내고 '-'는
                  --  보통의 단항 부정이다
                  return T;
               end;
            end if;
            declare
               T : constant Type_Id :=
                 Check_Expr (R.A, (if Is_Int (Expected) then Expected
                                   else No_Type));
            begin
               if Kind (T) /= Ty_Error and then not Is_Int (T) then
                  Error (N, "operand of '" & Spelling (R.Op)
                         & "' shall be an integer");
                  return Error_Type;
               end if;
               return T;
            end;

         when P_Bang =>
            declare
               T : constant Type_Id :=
                 Check_Expr (R.A, (if Is_Int (Expected) then Expected
                                   else No_Type));
            begin
               if Kind (T) = Ty_Verdict then
                  --  극성 반전: verdict[T, F] → verdict[F, T] (§7.2.1)
                  return Verdict (Get (T).Fail, Get (T).Pass);
               elsif Kind (T) /= Ty_Error and then not Is_Int (T) then
                  Error (N, "operand of '!' shall be an integer or a"
                         & " contract");
                  return Error_Type;
               end if;
               return T;
            end;

         when P_Star =>
            declare
               T : constant Type_Id := Check_Expr (R.A, No_Type);
            begin
               if Kind (T) = Ty_Error then
                  return T;
               elsif Kind (T) /= Ty_Ref then
                  Error (N, "operand of '*' shall be a thin reference");
                  return Error_Type;
               end if;
               if Get (T).Ref_Tribe = Unmanaged then
                  Require_Airside
                    (N, "dereferencing an unmanaged reference");
               end if;
               return Get (T).Target;
            end;

         when P_Percent =>
            declare
               T : constant Type_Id := Check_Expr (R.A, No_Type);
               M : constant Modifiers := Mods_Of (R);
            begin
               if Kind (R.A) = N_Name and then Get (R.A).Sym /= 0
                 and then Symbols.Get (Symbol_Id (Get (R.A).Sym)).Kind
                          in Sym_Local | Sym_Param
               then
                  null;
               elsif Kind (R.A) = N_Unary and then Get (R.A).Op = P_Star then
                  null;
               else
                  Unimplemented
                    (N, "references to value expressions (§6.4.4)");
                  return Error_Type;
               end if;
               if Kind (T) = Ty_Error or else not Valid_Mods (N, Unmanaged, M)
               then
                  return Error_Type;
               end if;
               return Ref (T, Unmanaged, M);
            end;

         when P_Amp | P_Dollar =>
            Unimplemented (N, "managed reference creation and the derivation"
                           & " chain (§6.4.4, §8.1.1)");
            return Error_Type;

         when others =>
            Error (N, "unknown unary operator");
            return Error_Type;
      end case;
   end Check_Unary;

   function Check_Binary (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
      L, Rt : Type_Id;

      --  두 피연산자를 같은 타입으로 맞춘다. 앞쪽이 합성되지 않으면
      --  뒤쪽을 먼저 본다 (검사 순서일 뿐, 평가 순서는 아니다).
      procedure Operands (Hint : Type_Id) is
      begin
         if Undetermined (R.A) and then not Undetermined (R.B) then
            Rt := Check_Expr (R.B, No_Type);
            L := Check_Expr (R.A, Rt);
         else
            L := Check_Expr (R.A, (if Undetermined (R.A) then Hint
                                   else No_Type));
            Rt := Check_Expr (R.B, L);
         end if;
         if L /= Rt and then Kind (L) /= Ty_Error
           and then Kind (Rt) /= Ty_Error
         then
            Error (N, "operands of '" & Spelling (R.Op) & "' have types "
                   & Quote (L) & " and " & Quote (Rt));
            L := Error_Type;
         end if;
      end Operands;

   begin
      case R.Op is
         when P_Plus | P_Minus | P_Star | P_Slash | P_Percent
            | P_Amp | P_Pipe | P_Caret =>
            Operands (if Is_Int (Expected) then Expected else No_Type);
            if Kind (L) /= Ty_Error and then not Is_Int (L) then
               if Kind (L) = Ty_Ref and then R.Op in P_Plus | P_Minus then
                  Unimplemented (N, "unmanaged reference arithmetic (§8.5)");
               else
                  Error (N, "operands of '" & Spelling (R.Op)
                         & "' shall be integers");
               end if;
               return Error_Type;
            end if;
            return L;

         when P_Plus_Pipe | P_Minus_Pipe | P_Star_Pipe | P_Slash_Pipe =>
            Unimplemented (N, "saturating integer arithmetic (§6.5.2)");
            return Error_Type;
         when P_Plus_At | P_Star_At =>
            Unimplemented (N, "widening integer arithmetic (§6.5.3)");
            return Error_Type;
         when P_Shl | P_Shr =>
            Unimplemented (N, "shift operators (§6.6.2)");
            return Error_Type;

         when P_Eq_Eq | P_Ne | P_Lt | P_Gt | P_Le | P_Ge =>
            Operands (No_Type);
            if Kind (L) /= Ty_Error and then not Is_Int (L) then
               Unimplemented (N, "comparison of " & Quote (L) & " (§6.7)");
               return Error_Type;
            end if;
            return Bool;

         when K_And | K_Or | K_Xor =>
            L := Check_Expr (R.A, No_Type);
            Rt := Check_Expr (R.B, No_Type);
            if Kind (L) not in Ty_Verdict | Ty_Error
              or else Kind (Rt) not in Ty_Verdict | Ty_Error
            then
               Error (N, "operands of '" & Spelling (R.Op)
                      & "' shall be of a contract type");
            end if;
            return Bool;

         when others =>
            Error (N, "unknown binary operator");
            return Error_Type;
      end case;
   end Check_Binary;

   function Check_Assign (N : Node_Id) return Type_Id is
      R : constant Node := Get (N);
      L : constant Type_Id := Check_Expr (R.A, No_Type);
   begin
      Check_Place (R.A);
      if R.Op = P_Eq then
         Check_Against (R.B, L);
      elsif R.Op in P_Plus_Eq | P_Minus_Eq | P_Star_Eq | P_Slash_Eq
                  | P_Percent_Eq | P_Amp_Eq | P_Pipe_Eq | P_Caret_Eq
      then
         if Kind (L) /= Ty_Error and then not Is_Int (L) then
            Error (N, "operands of '" & Spelling (R.Op)
                   & "' shall be integers");
         end if;
         Check_Against (R.B, L);
      else
         Unimplemented (N, "compound assignment '" & Spelling (R.Op)
                        & "' (§6.8.2)");
      end if;
      return Void;
   end Check_Assign;

   function Check_Cast (N : Node_Id) return Type_Id is
      R      : constant Node := Get (N);
      Target : constant Type_Id := Resolve_Type (R.B);
      Source : constant Type_Id := Check_Expr (R.A, No_Type);
   begin
      if R.Flags (F_Reinterpret) then
         Unimplemented (N, "bitwise reinterpretation (§6.9.8)");
         return Error_Type;
      elsif Kind (Source) = Ty_Error or else Kind (Target) = Ty_Error then
         return Error_Type;
      elsif Is_Int (Source) and then Is_Int (Target) then
         return Target;
      elsif Kind (Source) in Ty_Ref | Ty_Slice and then Target = Uaddr then
         return Target;
      elsif Source = Uaddr and then Kind (Target) = Ty_Ref then
         if Get (Target).Ref_Tribe /= Unmanaged then
            Error (N, "a cast from 'uaddr' reaches only an unmanaged"
                   & " reference");
            return Error_Type;
         end if;
         return Target;
      end if;
      Unimplemented (N, "cast from " & Quote (Source) & " to "
                     & Quote (Target) & " (§6.9, §8.2.3)");
      return Error_Type;
   end Check_Cast;

   function Check_Field (N : Node_Id) return Type_Id is
      R    : constant Node := Get (N);
      Base : Type_Id := Check_Expr (R.A, No_Type);
      Name : constant String := Idents.Image (R.Name);
   begin
      if Kind (Base) = Ty_Error then
         return Base;
      end if;
      --  참조 투명성: 참조를 한 번 거쳐 가리키는 객체에 적용 (§6.3.5)
      if Kind (Base) = Ty_Ref then
         Base := Get (Base).Target;
      end if;
      if Kind (Base) = Ty_Array and then Name = "ptr" then
         --  투영 (§8.2.5). 공유 참조를 거치면 mut이 붙지 않는다.
         return Ref (Get (Base).Target, Unmanaged);
      elsif Kind (Base) = Ty_Array and then Name = "len" then
         return Uaddr;
      end if;
      Unimplemented (N, "field expressions on " & Quote (Base) & " (§6.3.2)");
      return Error_Type;
   end Check_Field;

   procedure Check_Let (N : Node_Id) is
      R    : constant Node := Get (N);
      T    : Type_Id;
      Sym  : Symbol;
   begin
      if R.B = No_Node then
         Unimplemented (N, "deferred initialization (§4.3)");
         T := (if R.A = No_Node then Error_Type else Resolve_Type (R.A));
      elsif R.A /= No_Node then
         T := Resolve_Type (R.A);
         Check_Against (R.B, T);
      else
         T := Check_Expr (R.B, No_Type);
         if Kind (T) in Ty_Void | Ty_Never then
            Error (N, "a binding cannot hold " & Quote (T));
         end if;
      end if;
      if Names.Clash (R.Name) /= No_Symbol then
         Names.Report_Clash (R.Pos, R.Name);
      end if;
      Sym.Kind := Sym_Local;
      Sym.Name := R.Name;
      Sym.Pos := R.Pos;
      Sym.Ty := Natural (T);
      Sym.Decl := Natural (N);
      Sym.Mutable := R.Flags (F_Mut);
      Nodes (Positive (N)).Sym := Natural (Add (Sym));
      Nodes (Positive (N)).Ty := Natural (T);
      Names.Declare_Local (R.Name, Symbol_Id (Get (N).Sym));
   end Check_Let;

   function Find_Loop (N : Node_Id) return Node_Id is
      Label : constant Idents.Ident := Get (N).Name;
   begin
      for I in reverse Loops.First_Index .. Loops.Last_Index loop
         if Label = Idents.No_Ident or else Loops (I).Label = Label then
            return Loops (I).Node;
         end if;
      end loop;
      if Label = Idents.No_Ident then
         Error (N, "'" & Spelling (if Get (N).Kind = N_Break then K_Break
                                   else K_Continue)
                & "' outside a loop");
      else
         Error (N, "unknown label '" & Idents.Image (Label) & "'");
      end if;
      return No_Node;
   end Find_Loop;

   procedure Check_Condition (N : Node_Id) is
      T : constant Type_Id := Check_Expr (N, No_Type);
   begin
      if Kind (T) not in Ty_Verdict | Ty_Error | Ty_Never then
         Error (N, "a condition shall be of a contract type, found "
                & Quote (T));
      end if;
   end Check_Condition;

   function Check_Expr (N : Node_Id; Expected : Type_Id) return Type_Id is
      R : constant Node := Get (N);
      T : Type_Id := Void;
   begin
      case R.Kind is
         when N_Int_Lit =>
            T := Check_Int_Literal (N, Expected);
         when N_Char_Lit =>
            if Length (R.Text) /= 1 then
               Error (N, "a character literal shall denote one cell");
            end if;
            T := Int (False, 1);
         when N_Float_Lit =>
            Unimplemented
              (N, "floating radix point number literals (§3.5.2)");
            T := Error_Type;
         when N_String_Lit =>
            T := Ref (Array_Of (Int (False, 1), Length (R.Text)), Shared);
         when N_Name =>
            declare
               S : constant Symbol_Id := Resolve_Name (N);
            begin
               if S = No_Symbol then
                  T := Error_Type;
               else
                  case Symbols.Get (S).Kind is
                     when Sym_Local | Sym_Param =>
                        T := Type_Id (Symbols.Get (S).Ty);
                     when Sym_Fn =>
                        Unimplemented (N, "subroutine values (§5.10)");
                        T := Error_Type;
                     when Sym_Namespace =>
                        Error (N, "a namespace is not a value");
                        T := Error_Type;
                  end case;
               end if;
            end;
         when N_Call =>
            T := Check_Call (N);
         when N_Unary =>
            T := Check_Unary (N, Expected);
         when N_Binary =>
            T := Check_Binary (N, Expected);
         when N_Assign =>
            T := Check_Assign (N);
         when N_Cast =>
            T := Check_Cast (N);
         when N_Field =>
            T := Check_Field (N);

         when N_Block =>
            if R.Name /= Idents.No_Ident then
               Unimplemented (N, "labelled blocks (§7.9)");
            end if;
            Names.Push_Scope;
            for I in 1 .. R.List.Count loop
               declare
                  Item_N : constant Node_Id := Item (R.List, I);
               begin
                  if Kind (Item_N) = N_Let then
                     Check_Let (Item_N);
                  else
                     declare
                        Ignored : constant Type_Id :=
                          Check_Expr (Item_N, No_Type);
                     begin
                        null;
                     end;
                  end if;
               end;
            end loop;
            Names.Pop_Scope;

         when N_Airside =>
            Airside_Depth := Airside_Depth + 1;
            T := Check_Expr (R.A, No_Type);
            Airside_Depth := Airside_Depth - 1;

         when N_If =>
            Check_Condition (R.A);
            if Kind (R.B) = N_Block then
               T := Check_Expr (R.B, No_Type);
               if R.C /= No_Node then
                  T := Check_Expr (R.C, No_Type);
               end if;
               T := Void;
            else
               declare
                  TB : constant Type_Id := Check_Expr (R.B, Expected);
                  TC : constant Type_Id :=
                    Check_Expr (R.C, (if Kind (TB) = Ty_Never then Expected
                                      else TB));
               begin
                  T := (if Kind (TB) = Ty_Never then TC else TB);
                  if TB /= TC and then Kind (TB) not in Ty_Never | Ty_Error
                    and then Kind (TC) not in Ty_Never | Ty_Error
                  then
                     Error (R.C, "expected " & Quote (TB) & ", found "
                            & Quote (TC));
                  end if;
               end;
            end if;

         when N_While | N_Loop =>
            if R.Kind = N_While then
               Check_Condition (R.A);
            end if;
            Loops.Append (Loop_Entry'(N, R.Name));
            T := Check_Expr ((if R.Kind = N_While then R.B else R.A),
                             No_Type);
            Loops.Delete_Last;
            T := (if R.Kind = N_Loop and then Get (N).Sym = 0 then Never
                  else Void);

         when N_Break | N_Continue =>
            declare
               Target : constant Node_Id := Find_Loop (N);
            begin
               Nodes (Positive (N)).Sym := Natural (Target);
               if R.Kind = N_Break and then Target /= No_Node then
                  --  loop가 끝날 수 있음을 표시 (Sym = 1)
                  Nodes (Positive (Target)).Sym := 1;
               end if;
            end;
            T := Never;

         when N_Return =>
            if Kind (Fn_Ret) = Ty_Never then
               Error (N, "a subroutine that returns '!' shall not return");
            elsif R.A /= No_Node then
               Check_Against (R.A, Fn_Ret);
            elsif Fn_Ret /= Void then
               Error (N, "expected a return value of type " & Quote (Fn_Ret));
            end if;
            T := Never;

         when others =>
            Error (N, "expected expression");
            T := Error_Type;
      end case;
      Set_Type (N, T);
      return T;
   end Check_Expr;

   ---------------------------------------------------------------------
   --  도달성 (§2.4)

   function Diverges (N : Node_Id) return Boolean is
   begin
      if N = No_Node then
         return False;
      end if;
      declare
         R : constant Node := Get (N);
      begin
         case R.Kind is
            when N_Return | N_Break | N_Continue =>
               return True;
            when N_Loop =>
               return R.Sym = 0;
            when N_Block =>
               return (for some I in 1 .. R.List.Count =>
                         Diverges (Item (R.List, I)));
            when N_Airside =>
               return Diverges (R.A);
            when N_Let =>
               return Diverges (R.B);
            when N_If =>
               return Diverges (R.A)
                 or else (R.C /= No_Node and then Diverges (R.B)
                          and then Diverges (R.C));
            when N_While =>
               return Diverges (R.A);
            when N_Call =>
               return Kind (Type_Id (R.Ty)) = Ty_Never
                 or else (for some I in 1 .. R.List.Count =>
                            Diverges (Item (R.List, I)));
            when N_Binary =>
               return Diverges (R.A)
                 or else (R.Op not in K_And | K_Or and then Diverges (R.B));
            when N_Assign =>
               return Diverges (R.A) or else Diverges (R.B);
            when N_Unary | N_Cast | N_Field =>
               return Diverges (R.A);
            when others =>
               return False;
         end case;
      end;
   end Diverges;

   ---------------------------------------------------------------------
   --  본문 분석 (§10.2 4단계)

   procedure Analyse_Fn (N : Node_Id) is
      R  : constant Node := Get (N);
      FT : constant Type_Rec := Get (Type_Id (Symbols.Get
                                  (Symbol_Id (R.Sym)).Ty));
   begin
      Fn_Ret := FT.Ret;
      Airside_Depth := (if R.Flags (F_Airside) then 1 else 0);
      Names.Push_Scope;
      for I in 1 .. R.List.Count loop
         declare
            P   : constant Node_Id := Item (R.List, I);
            PR  : constant Node := Get (P);
            Sym : Symbol;
         begin
            if Names.Clash (PR.Name) /= No_Symbol then
               Names.Report_Clash (PR.Pos, PR.Name);
            end if;
            Sym.Kind := Sym_Param;
            Sym.Name := PR.Name;
            Sym.Pos := PR.Pos;
            Sym.Ty := Natural (FT.Params.Element (I));
            Sym.Decl := Natural (P);
            Sym.Mutable := PR.Flags (F_Mut);
            Sym.Index := I;
            Nodes (Positive (P)).Sym := Natural (Add (Sym));
            Nodes (Positive (P)).Ty := Natural (FT.Params.Element (I));
            Names.Declare_Local (PR.Name, Symbol_Id (Get (P).Sym));
         end;
      end loop;

      declare
         Ignored : constant Type_Id := Check_Expr (R.B, No_Type);
      begin
         null;
      end;
      if Fn_Ret /= Void and then not Diverges (R.B) then
         Diagnostics.Error
           (R.Pos, "the end of the body of '" & Idents.Image (R.Name)
            & "' is reachable, but it returns " & Quote (Fn_Ret));
      end if;
      Names.Pop_Scope;
   end Analyse_Fn;

   procedure Analyse (Unit : Node_Id) is
      U : constant Node := Get (Unit);
   begin
      for I in 1 .. U.List.Count loop
         if Kind (Item (U.List, I)) = N_Fn then
            Analyse_Fn (Item (U.List, I));
         end if;
      end loop;
   end Analyse;

end Check;
