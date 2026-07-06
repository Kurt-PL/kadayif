--  Kurt.Mono — monomorphisation of generic types (§5.9).
--
--  §5.9: an instantiation `G.<A, B>` denotes the concrete type "as if it
--  had been written with the type arguments substituted throughout", and
--  distinct arguments yield distinct types. This pass realises that: for
--  every generic instance used in the unit it generates a concrete
--  struct/enum declaration (parameters substituted), names it by mangling
--  the arguments (e.g. `verdict$si4$si4`), and rewrites the instance type
--  nodes to refer to the generated declaration. The generic template
--  declarations themselves are removed, so the layout and codegen passes
--  only ever see fully concrete declarations.
--
--  Runs after parsing and before Kurt.Layout.Register / Kurt.Sema.

with Kurt.Parser;

package Kurt.Mono is

   procedure Monomorphize (U : in out Kurt.Parser.Translation_Unit);

   Mono_Error : exception;

end Kurt.Mono;
