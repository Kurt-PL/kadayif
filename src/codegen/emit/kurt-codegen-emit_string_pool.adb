separate (Kurt.Codegen)
   procedure Emit_String_Pool
     (F : IO.File_Type; Pool : String_Pool)
   is
   begin
      if Pool.Is_Empty then
         return;
      end if;
      --  __TEXT,__const is a generic read-only section: the linker does
      --  not merge entries head-to-tail (unlike __cstring), so each Kurt
      --  string literal keeps its exact byte sequence. The bytes are
      --  laid out faithfully — a trailing NUL is present iff the source
      --  literal contains `\0`.
      IO.Put_Line (F, ".section __TEXT,__const");
      for I in Pool.First_Index .. Pool.Last_Index loop
         IO.Put_Line (F, "Lstr" & Img (I) & ":");
         declare
            B  : constant String := SU.To_String (Pool.Element (I).Bytes);
            Bs : Boolean := False;
         begin
            if B'Length = 0 then
               IO.Put_Line (F, "    .byte 0");
            else
               IO.Put (F, "    .byte ");
               for C of B loop
                  if Bs then
                     IO.Put (F, ", ");
                  end if;
                  IO.Put (F, Img (Integer (Character'Pos (C))));
                  Bs := True;
               end loop;
               IO.New_Line (F);
            end if;
         end;
      end loop;
   end Emit_String_Pool;
