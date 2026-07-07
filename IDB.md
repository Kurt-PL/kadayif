# Implementation-defined behaviour (KPLSS 0.1 §1.4(4))

KPLSS 0.1 §1.4(4) requires a conforming implementation to document all
implementation-defined behaviours. This is kadayif's register. Each entry cites
the spec clause that delegates the choice to the implementation.

## Execution environment

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Target | `aarch64+Apple` (Mach-O), linked against `libSystem` | §1.3 |
| Cell bit-width `cellbits::exec` | `8` (byte-addressed); `Cell_Bits_Exec` in `kurt.ads` | §2.1.1, §4.1 |
| Cell bit-width `cellbits::xlat` | `8`; `Cell_Bits_Xlat` in `kurt.ads` | §2.1.1 |
| Address width | 8 cells (64-bit); `Address_Cells` | §4.2.1 |
| Byte/cell order | little-endian (aarch64) | §2.1.1 |

## Lexical

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Line-ending set | LF (`U+000A`) only; CR / CRLF are not recognised line endings | §3.1 |
| Source encoding | UTF-8 | §3.1 |
| `\xH` escape digit count | `ceil(cellbits/4)` = 2 hex digits; value bounded by the cell value set | §3.5.5, §3.5.7 |

## Types and layout

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Per-type alignment | numeric `T@align == T@size`; composites: max field align; `&raw`/refs pointer-aligned (8) | §2.2.3, §4.11.1 |
| Default `repr` field order | declaration order, contiguous ascending, each field rounded up to its own `@align` | §2.2.3, §4.11 |
| Auto discriminant type | smallest unsigned (`ui1…ui8`) covering all values; smallest signed if any value is negative; `void` when ≤1 variant and no `#wild#(V)` | §4.11.3 |
| Unsuffixed integer-literal default type | `saddr` (§3.5.x default) | §3.4.1 |
| Layout quantity range | sizes/offsets/array lengths are 64-bit (`Cell_Count` in `kurt.ads`, 0 .. 2⁶³−1 cells); a size computation exceeding it is the §4.7 translation failure | §4.7 |
| Signalling-NaN operand behaviour / FP environment | No additional behaviour: `@trap` is never invoked and a signalling NaN operand does not alter control flow — every operation yields exactly its defined result (§4.4.4 canonical quiet NaN). Kadayif translates under the assumption that the programme runs in the **default floating-point environment** — exceptions masked — and that the **exception status flags are not read** (the stance of C `FENV_ACCESS "off"` / Clang `-ffp-exception-behavior=ignore`; the analogue of GCC's default `-fno-signaling-nans`). The lowering does not preserve exception semantics: comparison issues no FP instruction at all, a NaN-producing sequence may raise flags the abstract operation would not (and vice versa), so FPSR contents observed through inline `asm` (§6.11) or an fenv binding via `@dyn` are unspecified. Unmasking FP traps through such channels voids the no-control-flow-alteration property | §4.4.4 |

## Translation limits / restrictions (bootstrap)

These are *bootstrap restrictions* — a conforming program kadayif rejects, not a
delegated choice — but are documented here for completeness. The non-optimizing,
program-order code generator satisfies the §2 uniformity-rule obligations
vacuously (it performs no reordering or speculative transforms).

| Restriction | Note |
|---|---|
| `if let` / `while let` / let-else / `if e -> v` / `while -> v` scrutinee | must be a binding (a place), not an arbitrary expression |
| `xlatime` blocks, inline `asm`, multi-unit `@add`, `@flag*` | not yet implemented (see ROADMAP) |
