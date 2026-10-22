with Ada.Strings.Unbounded;

package body Listing is

   use Ada.Strings.Unbounded;

   Buffer : Unbounded_String;

   procedure Clear is
   begin
      Buffer := Null_Unbounded_String;
   end Clear;

   procedure Put_Line (S : String) is
   begin
      Append (Buffer, S);
      Append (Buffer, ASCII.LF);
   end Put_Line;

   procedure Instr (S : String) is
   begin
      Put_Line (ASCII.HT & S);
   end Instr;

   function Contents return String is (To_String (Buffer));

end Listing;
