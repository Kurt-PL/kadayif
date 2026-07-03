with Ada.Strings.Unbounded;
with Ada.Strings.Fixed;
with Ada.Strings;

package body Kurt.Mono is

   package SU renames Ada.Strings.Unbounded;
   use Kurt.Parser;

   ----------------------------------------------------------------------
   --  Mangle an instantiated type into a flat identifier.
   --     verdict.<si4, si4>  ->  "verdict$si4$si4"
   --     &raw ui1            ->  "praw_ui1"
   ----------------------------------------------------------------------
   function Mangle (T : Type_Access) return String is separate;

   ----------------------------------------------------------------------
   --  Deep copy of a type with generic parameters substituted by the
   --  corresponding argument. Params and Args are positionally matched.
   ----------------------------------------------------------------------
   function Subst
     (T      : Type_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Type_Access
   is separate;

   ----------------------------------------------------------------------
   --  Deep copy of an expression / statement tree with generic
   --  parameters substituted in every embedded type annotation. Used by
   --  fn-template instantiation (§5.9.3): the template itself was
   --  already checked under type erasure, so the copy is a semantics-
   --  preserving specialisation.
   ----------------------------------------------------------------------

   function Copy_Expr
     (E      : Expr_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Expr_Access;

   function Copy_Stmt
     (S      : Stmt_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Access;

   function Copy_Block
     (V      : Stmt_Vectors.Vector;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Vectors.Vector
   is
      R : Stmt_Vectors.Vector;
   begin
      for I in V.First_Index .. V.Last_Index loop
         R.Append (Copy_Stmt (V.Element (I), Params, Args));
      end loop;
      return R;
   end Copy_Block;

   function Copy_Expr
     (E      : Expr_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Expr_Access
   is separate;

   function Copy_Stmt
     (S      : Stmt_Access;
      Params : Path_Segments.Vector;
      Args   : Type_Vectors.Vector) return Stmt_Access
   is separate;

   ----------------------------------------------------------------------
   procedure Monomorphize (U : in out Kurt.Parser.Translation_Unit) is separate;

end Kurt.Mono;
