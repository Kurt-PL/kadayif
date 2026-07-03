separate (Kurt.Mono)
   function Mangle (T : Type_Access) return String is
   begin
      if T = null then
         return "void";
      end if;
      case T.Kind is
         when T_Named =>
            declare
               S : SU.Unbounded_String := T.Name;
            begin
               for I in T.Args.First_Index .. T.Args.Last_Index loop
                  SU.Append (S, "$");
                  SU.Append (S, Mangle (T.Args.Element (I)));
               end loop;
               return SU.To_String (S);
            end;
         when T_Ref =>
            return (case T.Sigil is
                       when R_Shared => "pref",
                       when R_Excl   => "pexc",
                       when R_Raw    => "praw")
                   & (if T.R_Volatile then "v" else "")
                   & (case T.R_Store is
                         when RS_None   => "",
                         when RS_Mut    => "m",
                         when RS_Atomic => "a",
                         when RS_Guard  => "g")
                   & "_" & Mangle (T.Target);
         when T_Tuple =>
            declare
               S : SU.Unbounded_String := SU.To_Unbounded_String ("tup");
            begin
               for I in T.Elems.First_Index .. T.Elems.Last_Index loop
                  SU.Append (S, "$");
                  SU.Append (S, Mangle (T.Elems.Element (I)));
               end loop;
               return SU.To_String (S);
            end;
         when T_Array =>
            declare
               Img : constant String := T.Len'Image;
            begin
               return "arr" & Img (Img'First + 1 .. Img'Last)
                 & "_" & Mangle (T.Elem);
            end;
         when T_Dyn =>
            return "dyn_" & SU.To_String (T.Trait_Name);
         when T_Fn =>
            declare
               S : SU.Unbounded_String := SU.To_Unbounded_String ("fnptr");
            begin
               for I in T.Fn_Params.First_Index .. T.Fn_Params.Last_Index loop
                  SU.Append (S, "$" & Mangle (T.Fn_Params.Element (I)));
               end loop;
               if T.Fn_Ret /= null then
                  SU.Append (S, "$ret$" & Mangle (T.Fn_Ret));
               end if;
               return SU.To_String (S);
            end;
      end case;
   end Mangle;
