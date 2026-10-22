--  식별자 인터닝: 같은 문자열은 같은 Ident
package Idents is

   type Ident is new Natural;
   No_Ident : constant Ident := 0;

   function Intern (S : String) return Ident;
   function Image (Id : Ident) return String;

end Idents;
