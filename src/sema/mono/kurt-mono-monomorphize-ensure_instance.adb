separate (Kurt.Mono.Monomorphize)
   procedure Ensure_Instance (Inst : Type_Access; Mangled : String) is
      Orig : constant String := SU.To_String (Inst.Name);
      SD   : Struct_Decl;
      ED   : Enum_Decl;
   begin
      if Already_Generated (Mangled) then
         return;
      end if;

      if Find_Gen_Struct (Orig, SD) then
         if Natural (SD.Generic_Params.Length)
              /= Natural (Inst.Args.Length)
         then
            raise Mono_Error with
              "wrong number of type arguments for '" & Orig & "'";
         end if;
         declare
            New_D : Struct_Decl;
         begin
            New_D.Name := SU.To_Unbounded_String (Mangled);
            for I in SD.Fields.First_Index .. SD.Fields.Last_Index loop
               New_D.Fields.Append
                 ((Name    => SD.Fields.Element (I).Name,
                   Ty      => Subst (SD.Fields.Element (I).Ty,
                                     SD.Generic_Params, Inst.Args),
                   Default => Copy_Expr (SD.Fields.Element (I).Default,
                                         SD.Generic_Params, Inst.Args),
                   Is_Mut     => SD.Fields.Element (I).Is_Mut,
                   Is_Pub     => SD.Fields.Element (I).Is_Pub,
                   Is_Airside => SD.Fields.Element (I).Is_Airside));
            end loop;
            U.Structs.Append (New_D);
         end;
         Generated.Append (SU.To_Unbounded_String (Mangled));

      elsif Find_Gen_Enum (Orig, ED) then
         if Natural (ED.Generic_Params.Length)
              /= Natural (Inst.Args.Length)
         then
            raise Mono_Error with
              "wrong number of type arguments for '" & Orig & "'";
         end if;
         declare
            New_D : Enum_Decl;
         begin
            New_D.Name        := SU.To_Unbounded_String (Mangled);
            New_D.Is_Contract := ED.Is_Contract;
            for I in ED.Variants.First_Index .. ED.Variants.Last_Index
            loop
               declare
                  V  : constant Enum_Variant := ED.Variants.Element (I);
                  NV : Enum_Variant;
               begin
                  NV.Name    := V.Name;
                  NV.Value   := V.Value;
                  NV.Is_Wild := V.Is_Wild;
                  for J in V.Payload.First_Index .. V.Payload.Last_Index
                  loop
                     NV.Payload.Append
                       ((Name    => V.Payload.Element (J).Name,
                         Ty      => Subst (V.Payload.Element (J).Ty,
                                           ED.Generic_Params, Inst.Args),
                         Default => Copy_Expr
                                      (V.Payload.Element (J).Default,
                                       ED.Generic_Params, Inst.Args),
                         others => <>));
                  end loop;
                  New_D.Variants.Append (NV);
               end;
            end loop;
            U.Enums.Append (New_D);
         end;
         Generated.Append (SU.To_Unbounded_String (Mangled));

      else
         raise Mono_Error with
           "instantiation of unknown generic type '" & Orig & "'";
      end if;
   end Ensure_Instance;
