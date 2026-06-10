--  Kadaif L0 bootstrap codegen.
--
--  Target: arm64 Apple Darwin (Mach-O).
--  Strategy: brain-dead 1:1 lowering, zero optimisation, zero register
--  allocator. Each statement emits a self-contained instruction sequence.
--
--  Spec note: this matches §2.5 (uniformity rule) trivially because we
--  perform no transformation. The signal sequence emitted is identical to
--  the source order.

with Kurt.Parser;

package Kurt.Codegen is

   --  Emit assembly text for the unit. The output file is overwritten if
   --  it exists. Symbol naming follows the Darwin convention: every
   --  Kurt-level function `name` is emitted as `_name`.
   procedure Emit (U : Kurt.Parser.Translation_Unit; Out_Path : String);

end Kurt.Codegen;
