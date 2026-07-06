package Kurt is
   pragma Pure;

   --  §4.3.1 cellbits — environment cell width, in bits. A cell is the
   --  minimum addressable unit; cellbits is the fundamental unit from which
   --  the uiN/siN type widths derive (N cells = N * cellbits bits). On this
   --  host/target the translation and execution environments share a cell
   --  width, so cellbits::exec and cellbits::xlat are equal, and the
   --  unqualified xlatime value max(exec, xlat) is that same value. These
   --  are the documented values the spec's §4.3.1 implementation
   --  requirement asks a conforming implementation to record.
   Cell_Bits_Exec : constant := 8;   --  cellbits::exec
   Cell_Bits_Xlat : constant := 8;   --  cellbits::xlat

   --  §4.3.2 uaddr/saddr are address-width. They occupy
   --  Address_Bits / cellbits::exec cells.
   Address_Bits  : constant := 64;
   Address_Cells : constant := Address_Bits / Cell_Bits_Exec;

   --  §3.5.7 a `\xH` escape consumes exactly ceil(cellbits::exec / 4)
   --  hexadecimal digits.
   Hex_Escape_Digits : constant := (Cell_Bits_Exec + 3) / 4;

   --  §4.7 layout quantities — sizes, alignments, offsets, and array
   --  lengths, measured in cells (or elements). 64-bit signed, matching
   --  the width of the spec's `uaddr` on this target, so layouts past
   --  Natural's 2**31 - 1 cells are representable. Arithmetic that
   --  overflows the 63-bit magnitude raises Constraint_Error, which the
   --  layout engine reports as the §4.7 translation failure rather than
   --  wrapping. Sentinel-returning queries (-1 = absent) use the base
   --  Long_Long_Integer instead.
   subtype Cell_Count is Long_Long_Integer range 0 .. Long_Long_Integer'Last;

end Kurt;
