with Ada.Characters.Handling;
with Ada.Strings.Fixed;
with Ada.Text_IO;

package body Diagnostics is

   Failure_Count : Natural := 0;

   function Image (N : Positive) return String is
     (Ada.Strings.Fixed.Trim (N'Image, Ada.Strings.Left));

   procedure Emit (Sev : Severity; Message : String) is
   begin
      if Sev in Halt | Error then
         Failure_Count := Failure_Count + 1;
      end if;
      Ada.Text_IO.Put_Line
        (Ada.Text_IO.Standard_Error,
         Ada.Characters.Handling.To_Lower (Sev'Image) & " - " & Message);
   end Emit;

   procedure Report
     (Sev : Severity; Pos : Source_Map.Source_Pos; Message : String)
   is
      use type Source_Map.Source_Id;
      Line, Col : Positive;
   begin
      if Pos.Source = Source_Map.No_Source then
         Emit (Sev, Message);
         return;
      end if;
      Source_Map.Line_Col (Pos, Line, Col);
      Emit
        (Sev,
         Message & " at " & Source_Map.Path (Pos.Source) & " on "
         & Image (Line) & ":" & Image (Col));
   end Report;

   procedure Report (Sev : Severity; Message : String) is
   begin
      Emit (Sev, Message);
   end Report;

   procedure Error (Pos : Source_Map.Source_Pos; Message : String) is
   begin
      Report (Error, Pos, Message);
   end Error;

   procedure Warn (Pos : Source_Map.Source_Pos; Message : String) is
   begin
      Report (Warning, Pos, Message);
   end Warn;

   procedure Unimplemented (Pos : Source_Map.Source_Pos; What : String) is
   begin
      Report (Error, Pos, "unimplemented: " & What);
   end Unimplemented;

   function Failures return Natural is (Failure_Count);

end Diagnostics;
