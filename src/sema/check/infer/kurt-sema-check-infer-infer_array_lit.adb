separate (Kurt.Sema.Check.Infer)
   function Infer_Array_Lit return Type_Access is
   begin
            --  §6.1.6: element list or repeat form. The element type is
            --  steered by the expected array type when present.
            declare
               Exp_Elem : constant Type_Access :=
                 (if Expected /= null and then Expected.Kind = T_Array
                  then Expected.Elem else null);
               ET  : Type_Access := null;
               Arr : constant Type_Access :=
                 new AST_Type (Kind => T_Array);
            begin
               for I in E.AL_Elems.First_Index .. E.AL_Elems.Last_Index
               loop
                  declare
                     T : constant Type_Access :=
                       Infer (E.AL_Elems.Element (I),
                              (if ET = null then Exp_Elem else ET));
                  begin
                     --  §9.5: a `[&dyn Trait; N]` literal coerces each
                     --  `&U` element (U implements Trait) to `&dyn Trait`.
                     if Is_Dyn_Ref (Exp_Elem) and then Is_Ref (T)
                       and then T.Target /= null
                       and then T.Target.Kind = T_Named
                       and then Type_Implements
                         (SU.To_String (T.Target.Name),
                          SU.To_String (Exp_Elem.Target.Trait_Name))
                     then
                        declare
                           DC : constant Expr_Access :=
                             new Expr_Node (Kind => E_Dyn_Cast);
                        begin
                           DC.DC_Inner := E.AL_Elems.Element (I);
                           DC.DC_Conc  := T.Target.Name;
                           DC.DC_Trait := Exp_Elem.Target.Trait_Name;
                           DC.Sem_Ty   := Exp_Elem;
                           E.AL_Elems.Replace_Element (I, DC);
                        end;
                        ET := Exp_Elem;
                     elsif ET = null then
                        ET := T;
                     elsif not Same_Type (ET, T) then
                        Error ("array literal elements have differing "
                               & "types: '" & Image (ET) & "' vs '"
                               & Image (T) & "'");
                     end if;
                     --  §8.8.2 an element supplied by a `destruct`-typed
                     --  binding is transferred into the array (its
                     --  scope-exit drop is suppressed). Only the element-
                     --  list form transfers; the repeat form `[e; N]`
                     --  would copy `e` N times.
                     if E.AL_Repeat = 0 then
                        Maybe_Move (E.AL_Elems.Element (I));
                     end if;
                  end;
               end loop;
               Arr.Elem := ET;
               Arr.Len  :=
                 (if E.AL_Repeat > 0 then E.AL_Repeat
                  else Natural (E.AL_Elems.Length));
               if Expected /= null and then Expected.Kind = T_Array
                 and then Expected.Len /= Arr.Len
               then
                  Error ("array literal has" & Arr.Len'Image
                         & " elements but the expected type '"
                         & Image (Expected) & "' has"
                         & Expected.Len'Image);
               end if;
               E.Sem_Ty := Arr;
               return Arr;
            end;

   end Infer_Array_Lit;
