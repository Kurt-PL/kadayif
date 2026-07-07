# Kurt implementation-defined behaviour

KPLSS 0.1 §1.4(4) requires a conforming implementation to document its choice
of behaviour in each of the areas that are designated *implementation
defined*. This file is kadayif's register of those choices. Each entry quotes
the delegating requirement, abridged, with the clause it comes from, followed
by kadayif's choice.

Kadayif translates for exactly one configuration — aarch64+Apple, producing
Mach-O opaque code linked against `libSystem` — and several answers below
simply record what that target determines: a cell is the target's 8-bit byte,
multi-cell values are little-endian, and addresses and references are 8 cells
wide. These are listed as "determined by the target" where the delegation
allows nothing else once the target is fixed.

Behaviour the specification fixes itself — KSA field order and per-type
alignment (§4.2, §4.11), automatic discriminant sizing (§4.11.2), literal
default types (§3.5.1) — is deliberately absent from this register: it is not
a choice.

## Abstract machine (§2)

*"The number of distinct bit patterns a cell may hold is implementation
defined."* (§2.1.1)

2⁸. `cellbits::exec` and `cellbits::xlat` are both 8 (`Cell_Bits_Exec`,
`Cell_Bits_Xlat` in `kurt.ads`); determined by the target.

*"The physical storage mechanism used to implement automatic object layout is
implementation defined. A conforming implementation shall document the
alignment of the execution environment for each built-in type."* (§2.2.3)

Automatic objects live in fixed-size, 16-byte-aligned stack frames anchored at
`x29`; every binding occupies a frame slot at its natural alignment. The
alignment of each built-in type is exactly the §4.2 formula instantiated with
`cellbits` = 8: numeric, thin-reference, and subroutine-pointer types have
`T@align == T@size` (1, 2, 4, 8, 16, or 32 cells); fat references align to 8.

*"... dispatching to either a registered handler or the implementation defined
default behaviour."* (§2.9.2) — *"If no handler is registered, the default
behaviour is implementation defined. The default shall diverge — it shall not
return."* (§7.10)

The default divergence executes `udf #0`; the process terminates on the
resulting illegal-instruction signal. It does not return.

## Lexical structure (§3)

*"... the source encoding — including the set of permitted characters, their
bit width, the mapping from characters to the lexical elements of the Kurt
grammar, and the character sequence or sequences that constitute a line
ending — is implementation defined."* (§3.1)

UTF-8. A character is one Unicode scalar value, so its width is 8 to 32 bits;
letters and digits classify per the Unicode categories. The line ending is LF
(`U+000A`) alone — CR and CRLF are not line endings. An ill-formed sequence
(orphan continuation byte, overlong form, surrogate) is a §3.1 diagnostic.

*"The source-encoding value that corresponds to this character [the double
quotation mark] is implementation defined."* (§3.5.5)

`0x22`, its UTF-8 encoding.

## Types (§4)

*"The content of the remaining `T@size × cellbits − W` bits of greatest
weight, when a value is stored, is implementation defined."* (§4.2)

Does not arise: every built-in bit width *W* is a multiple of `cellbits`, so
`T@size × cellbits == W` throughout.

*"The implementation's behaviour upon a signalling NaN operand, other than
the arithmetic result, is implementation defined and may include invoking
`@trap`; absent such a behaviour, the operand's presence shall not alter
control flow."* (§4.4.4)

None: `@trap` is never invoked and control flow is unaffected — every
operation yields exactly its defined result. Kadayif translates as though the
floating-point exception status flags are never read and floating-point
exceptions stay masked (the stance of C `FENV_ACCESS` "off"). The lowering
does not preserve exception semantics — comparison issues no floating-point
instruction at all, and a NaN-canonicalising sequence may raise flags the
abstract operation would not — so FPSR contents observed through inline `asm`
or an fenv binding via `@dyn` are unspecified, and unmasking floating-point
traps through such channels voids the no-control-flow-alteration property.

*"The stored representation of a reference type is implementation defined."*
(§4.9)

A thin reference is the referent's address in one 8-cell word; `&raw T` and
`uaddr` are bit-identical. A fat reference (`&[T]`, `&dyn Trait`) is two
8-cell words: the address, then the length or dispatch-table address.

*"A conforming implementation shall support at least the following
identifiers; additional identifiers are implementation defined."* (§4.11)

None beyond `packed` and `native`.

*"[`repr(native)`:] The exact layout is implementation defined, but shall
match the native invocation interface of the execution environment."* (§4.11)

Identical to the KSA default, which for the supported field types coincides
with the Apple aarch64 (AAPCS64) C struct layout.

*"The internal fields, the iteration interface, and the argument promotion
rules of each `with variadic` type are implementation defined."* (§4.11.5)

Not provided. The declaration parses, but the iteration interface and
rest-argument materialization are absent; see the restrictions below.

## Declarations (§5)

*"A declaration without `extern` has an implementation defined name in the
opaque code."* — *"The mangling scheme ... [is] implementation defined."*
(§5.1.2)

Namespace segments joined with `$`: source-unit prefix, `module` names, owner
type, trait, item, and mangled generic arguments (`Box$si4`,
`point$Ord$cmp`), with the Mach-O leading `_`.

*"How the logical external name is represented in the opaque code is
implementation defined."* (§5.1.2)

The `extern` identifier — or the `@symbol` string (§5.15), verbatim, at
definition and call sites alike — with the Mach-O leading `_` and no other
transformation.

*"Other identifier values [invocation interfaces beyond `native`] are
implementation defined."* (§5.1.2)

Recognised for type identity only: `extern(efi)` and friends give distinct
subroutine-pointer types, but every call lowers through the native (Apple
aarch64) interface. See the restrictions below.

*"The instruction syntax, implementation-defined directives, and the set of
supported execution environments for top-level `asm` are implementation
defined."* (§5.13)

The system assembler's aarch64+Apple syntax; the block passes to it verbatim,
so its directives define linker-visible symbols exactly as written. The sole
supported execution environment is the target.

*"The interpretation of the string literal [of `@symbol`] ... is
implementation defined."* (§5.15)

The string is the linker symbol.

*"The content between `@[` and `]@` is a sequence of tokens whose structure
and interpretation are entirely implementation defined."* (§5.16)

No annotations are recognised; a balanced annotation is skipped whole. An
unbalanced one is a §5.16 diagnostic.

## Expressions (§6)

*"Recursion within `xlatime` blocks is permitted but bounded by an
implementation defined evaluation limit."* (§6.10)

Translation-time expression folding is bounded at depth 64
(`Kurt.Parser.Fold_Int_Expr.Max_Depth`); exceeding it is a translation
failure.

*"Resource identifiers, resource classes, and instruction syntax are
implementation defined."* (§6.11)

As for top-level `asm` (§5.13 above): the aarch64+Apple assembler dialect,
passed verbatim. Resource and `clobber` identifiers are the aarch64 register
names (`x0`–`x30`, `w0`–`w30`, the `v`/`d`/`s` views, `sp`).

*"The instruction dialect of the translation environment accepted within
`xlatime` contexts is implementation defined."* (§6.11)

None; `asm` is not evaluated at translation time.

*"`T@name` yields the name of the type ... The format of the string is
implementation defined."* (§6.12.2)

Not provided; see the restrictions below.

## References and resource management (§8)

*"The set of widths for which atomic operations are available is
implementation defined."* (§8.5.2)

1, 2, 4, and 8 cells (the `ldaxr`/`stlxr` family).

## Programme structure and translation (§10)

*"Each source unit has a location, which is an implementation-defined value
that uniquely identifies the source unit."* (§10.1)

The canonical absolute filesystem path. Duplicate inclusion is detected by
that path.

*"The source path resolution strategy for `@add`, including any fallback
search, is implementation defined ... The mechanism for determining canonical
source unit locations is implementation defined."* (§10.2)

A path resolves relative to the containing source unit's directory, or to the
`@path` base when the path is prefixed. There is no fallback search.
Canonicalisation is the filesystem's real path.

*"... the behaviour when a symbol cannot be resolved is implementation
defined."* (§10.4)

An unbound symbol surfaces as a system-linker error and the translation is
reported failed. (The bound form's translation-time presence check is not yet
performed; see the restrictions below.)

*"Flags may be introduced from ... the implementation-defined external
mechanism."* (§10.7)

`-f NAME` command-line options, applied to every source unit of the
translation.

*"The form of the opaque code is implementation defined."* — *"The mechanism
by which an interface source is generated, and whether it is generated
automatically or on request, is implementation defined."* (§10.9)

Mach-O: object files via the system assembler, executables linked against
`libSystem` via the system linker. Interface-source generation is not
provided.

## Translation limits and bootstrap restrictions

These are not §1.4(4) delegations but the bootstrap's own limits — conforming
programmes kadayif rejects, or delegated machinery it does not yet provide —
kept here so the register is complete. The non-optimizing, program-order code
generator satisfies the §2 uniformity-rule obligations vacuously: it performs
no reordering or speculative transforms.

- Layout quantities (sizes, offsets, array lengths) are 64-bit
  (`Cell_Count`, 0 .. 2⁶³−1 cells); a computation exceeding that range is
  reported as the §4.7 translation failure.
- The scrutinee of `if let` / `while let` / let-else / `if e -> v` /
  `while -> v` must be a binding, and their payload clauses accept plain
  binds and renames only — nested and `#` sub-patterns are `match`-only.
- `T@name` is not implemented (§6.12 intrinsics: `@size`, `@align`,
  `@offset` only).
- `with variadic` internals: the iteration interface and rest-argument
  materialization are not provided.
- The bound-form `@dyn` translation-time symbol-presence check (§10.4) is
  not performed; resolution defers to the linker.
- Calls always lower through the native invocation interface, whatever the
  declared `extern(...)` identifier.
- `const` initialisers cannot contain translation-time subroutine calls (no
  interpreter); literals, intrinsics, consts, and pure operators over those
  are evaluable.
