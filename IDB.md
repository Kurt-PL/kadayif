# Implementation-defined behaviour (KPLSS 0.1 §1.4(4))

KPLSS 0.1 §1.4(4) requires a conforming implementation to document all
implementation-defined behaviours. This is kadayif's register. Each entry cites
the clause that delegates the choice; behaviour the specification itself fixes
(KSA field order, per-type alignment, automatic discriminant sizing, literal
default types, ...) is deliberately absent — it is not a choice.

## Execution environment

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Target | `aarch64+Apple` (Mach-O), linked against `libSystem` | §1.3 |
| Cell width / value set | `cellbits::exec` = `cellbits::xlat` = 8 (byte-addressed; a cell holds the 2⁸ bit patterns); `Cell_Bits_*` in `kurt.ads` | §2.1.1, §4.1 |
| Address / reference width | 8 cells (64-bit); `Address_Cells` | §4.2.1 |
| Byte/cell order | little-endian (aarch64) | §2.1.1 |
| Automatic-object storage mechanism | fixed-size, 16-byte-aligned stack frames anchored at `x29`; every binding occupies a frame slot at its natural (§4.2/§4.11) alignment | §2.2.3 |
| Built-in alignments (documentation duty) | exactly the §4.2 formula instantiated with the parameters above: numeric / thin-reference / subroutine-pointer `T@align == T@size` (1/2/4/8/16/32); fat references 8 | §2.2.3 |
| Oversized-store high bits | does not arise: every built-in bit width *W* is a multiple of `cellbits`, so `T@size × cellbits == W` throughout | §4.2 |
| Stored representation of references | thin: the referent's address, one 8-cell word (`&raw` ↔ `uaddr` bit-identical); fat (`&[T]`, `&dyn Trait`): two 8-cell words — the address, then the length / dispatch-table address | §4.9 |
| Atomic widths | 1, 2, 4, 8 cells (`ldaxr`/`stlxr` family); wider `&atomic`/`&guard` targets are rejected | §8.5.2 |
| `@trap` default behaviour | dispatch to the registered handler when one exists; the default divergence executes `udf #0`, terminating the process on the resulting illegal-instruction signal. It does not return | §2.9.2, §7.10 |
| Signalling-NaN operand behaviour / FP environment | No additional behaviour: `@trap` is never invoked and a signalling NaN operand does not alter control flow — every operation yields exactly its defined result (§4.4.4 canonical quiet NaN). Kadayif translates under the assumption that the programme runs in the **default floating-point environment** — exceptions masked — and that the **exception status flags are not read** (the stance of C `FENV_ACCESS "off"` / Clang `-ffp-exception-behavior=ignore`; the analogue of GCC's default `-fno-signaling-nans`). The lowering does not preserve exception semantics: comparison issues no FP instruction at all, a NaN-producing sequence may raise flags the abstract operation would not (and vice versa), so FPSR contents observed through inline `asm` (§6.11) or an fenv binding via `@dyn` are unspecified. Unmasking FP traps through such channels voids the no-control-flow-alteration property | §4.4.4 |

## Lexical

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Source encoding | UTF-8; a character is one Unicode scalar value (so its bit width varies, 8–32); illegal sequences (orphan continuation, overlong, surrogate) are §3.1 diagnostics | §3.1 |
| Line-ending set | LF (`U+000A`) only; CR / CRLF are not recognised line endings | §3.1 |
| Source value of the escaped `"` | `0x22` (its UTF-8 encoding) | §3.5.5 |

## Types and layout

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Additional `repr` identifiers | none — `packed` and `native` only | §4.11 |
| `repr(native)` layout | identical to the KSA default, which for the supported field types coincides with the Apple aarch64 (AAPCS64) C struct layout | §4.11 |

## Translation-time evaluation, `asm`

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| `xlatime` evaluation limit | expression folding is bounded at depth 64 (`Kurt.Parser.Fold_Int_Expr.Max_Depth`); exceeding it is a translation failure | §6.10 |
| `asm` instruction syntax | the Apple aarch64 assembler dialect; non-`'`-operand text passes verbatim to the system assembler (inline §6.11 and top-level §5.13 alike, including its symbol-defining directives) | §5.13, §6.11 |
| `asm` resource / `clobber` identifiers | aarch64 register names (`x0`–`x30`, `w0`–`w30`, `v`/`d`/`s` registers, `sp`) | §6.11 |

## Names, linking, programme structure

| Behaviour | kadayif's choice | Spec |
|---|---|---|
| Non-`extern` name in opaque code | namespace segments joined with `$` — file prefix, `module` names, owner type, trait, item, mangled generic arguments (`Box$si4`, `point$Ord$cmp`) — plus the Mach-O leading `_` | §5.1.2 |
| Logical external name representation | the `extern` identifier (or the `@symbol` string, verbatim, at definition and call sites alike) with the Mach-O leading `_`; no other transformation | §5.1.2, §5.15 |
| Invocation interfaces beyond `native` | recognised for type identity only (e.g. `extern(efi)` is a distinct subroutine-pointer type); every call lowers through the native (Apple aarch64) interface — see restrictions | §5.1.2 |
| Annotations `@[ ... ]@` | none recognised; a balanced annotation is skipped whole (an unbalanced one is a §5.16 diagnostic) | §5.16 |
| Source-unit location | the canonical absolute filesystem path; duplicate inclusion is detected by that path | §10.1 |
| Source-path resolution | relative to the containing source unit's directory, or to the `@path` base when the path is prefixed; no fallback search | §10.2 |
| External flag mechanism | `-f NAME` command-line options (space-separated, applied to every source unit) | §10.7 |
| Opaque code | Mach-O: objects via the system assembler, executables linked against `libSystem` via the system linker; interface-source generation is not provided | §10.9 |
| Unbound `@dyn` resolution failure | surfaces as a system-linker error; the translation is reported failed | §10.4 |

## Translation limits / restrictions (bootstrap)

These are *bootstrap restrictions* — conforming programmes kadayif rejects (or
delegated behaviour it does not yet provide) — documented for completeness. The
non-optimizing, program-order code generator satisfies the §2 uniformity-rule
obligations vacuously (it performs no reordering or speculative transforms).

| Restriction | Note |
|---|---|
| Layout quantities | sizes/offsets/array lengths are 64-bit (`Cell_Count`, 0 .. 2⁶³−1 cells); a computation exceeding that range is reported as the §4.7 translation failure |
| `if let` / `while let` / let-else / `if e -> v` / `while -> v` scrutinee | must be a binding (a place), not an arbitrary expression; their payload clauses accept plain binds/renames only (nested / `#` sub-patterns are `match`-only) |
| `T@name` | not implemented (§6.12 intrinsics: `@size`/`@align`/`@offset` only) |
| `with variadic` internals | the type parses, but the §4.11.5 iteration interface and rest-argument materialization are not provided |
| Bound-form `@dyn` symbol verification | the §10.4 translation-time presence check is not performed (resolution defers to the linker) |
| Invocation interfaces | calls always lower through the native interface, whatever the declared `extern(...)` identifier |
| Translation-environment `asm` dialect | `asm` inside `xlatime` contexts is not evaluated at translation time |
| `const` initialisers | translation-time subroutine calls are not evaluable (no interpreter); literals, intrinsics, consts, and pure operators over those are |
