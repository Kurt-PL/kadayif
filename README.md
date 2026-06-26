# Kadayif

The brainless reference implementation of the Kurt programming language.

Kadayif is a bootstrap compiler for Kurt, written in Ada. It
translates a single `.kr` source file all the way to a native
`arm64-apple-darwin` executable: lex → parse → semantic analysis → assembly,
then it shells out to the system `as` and `ld` to assemble and link.

> [!WARNING]
> **Full disclosure.** This thing is being vibe-coded with Claude Code and the
> Antigravity CLI by some mf who has zero idea about compiler theory — never
> took a compilers course, couldn't tell you what an SSA is, the works. So
> there's no clever IR, no optimization passes, no register allocator worth the
> name — just a brain-dead, zero-cleverness 1:1 splat to assembly. It's
> "brainless" on purpose *and* by necessity. Said mf is also genuinely bad at
> documentation, so this README and the docs next to it are best treated as
> vibes with a confidence interval. If anything here makes a real compiler
> engineer wince: yeah, sorry, that tracks. It does pass its tests, though. That
> part is real.

The name: **K**urt + **Ada** → **Kada** → **Kadayif**, which also happens to be
a dessert. Don't like it? Tough.

And if you're wondering why this compiler is named `kadayif` rather than just
`kurt` — when, exactly, did you start to be under the impression that a
programming language could have only *one* compiler?

> [!NOTE]
> **Platform.** Right now this only runs on **arm64 macOS**. It emits Mach-O
> arm64 assembly and leans on the host `as`/`ld` (plus `xcrun` for the SDK
> path). The AAPCS64 calling convention is only **partly** implemented — the
> common integer/aggregate and variadic cases work, but HFAs and a pile of edge
> cases don't yet, so that's still on the to-do list. No other OS or
> architecture exists. Portability is a TODO, not a feature.

## Status

Kadayif targets **Kurt 0.1** (the Kurt programming language standard
specification — preliminary edition 1), kept in
[`std-spec`](https://github.com/Kurt-PL/std-spec). It is a bootstrap,
so it implements a growing subset of the language rather than the whole
thing.

What works today (non-exhaustive): functions and recursion, `let`/`mut`,
integer/float/bool/char/string literals, the full operator set (wrapping,
saturating, widening, bitwise, comparison, contract logic), `if`/`while`/
`loop` with labels, `match`, structs and enums with payloads and default
fields, tuples, fixed arrays and slices, references and the airside/landside
split, atomics and compare-and-swap, generics (type-erasure checking +
monomorphisation), traits with `dyn` dispatch, contract control flow
(`verdict`, `?`, `<-`, `if e -> v`), ranges, `if let`, `uninit`, `@dyn` FFI,
`@symbol`, `@inline`, casts, and translation-time layout intrinsics.

## Building

Requires [Alire](https://alire.ada.dev/) (it pulls in `gnat_native` and
`gprbuild`; no system GNAT needed).

```sh
cd kadayif
alr build
```

The compiler is built to `bin/main`. Kadayif sticks to **strict Ada 2012** —
no GNAT-specific packages. The one place it touches the OS (running `as`/`ld`)
goes through a standard `Interfaces.C` binding to C `system(3)`.

## Usage

A conventional compiler command-line interface:

```sh
bin/main hello.kr            # translate, assemble, and link -> a.out
bin/main hello.kr -o hello   # ... to a named executable
bin/main -c hello.kr         # translate + assemble -> hello.o (no link)
bin/main -S hello.kr         # emit assembly -> hello.s (stop)
bin/main -y hello.kr         # semantic check only; no output
bin/main -h                  # usage      (also -v version, -a licence)
```

Default output (no phase option) is an executable, `a.out` on this platform.
Assembling and linking are delegated to the host toolchain (`as`/`ld`).

## Testing

```sh
cd kadayif/tests
./run.sh
```

`run.sh` builds every `NN_name.kr` with the compiler itself, runs the resulting
binary, and prints its exit code and stdout. All tests are expected to pass.

## Layout

```
kadayif/
  src/
    lexer/      Kurt.Lexer    — tokeniser
    parser/     Kurt.Parser   — recursive-descent / Pratt parser + AST
    sema/       Kurt.Sema     — type inference & checking
                Kurt.Layout   — KSA size/align/offset
                Kurt.Mono     — generic monomorphisation
    codegen/    Kurt.Codegen  — direct arm64 assembly emitter
    main.adb    command-line entry point
  tests/        regression tests + run.sh
```

## Contributing

Honestly? Not looking for code. What I'd actually love instead: tell me which
**compiler to read as a textbook** — a real, well-structured codebase I can
study — and which **courses or lectures** to watch to stop being the mf from the
disclaimer. Recommendations on compiler theory, language implementation, type
systems, codegen, whatever — open an issue. That's the contribution I need.

One rule: **do not pitch me LLVM.** LLVM is specialized for serving C's
semantics, and Kurt thinks that is *fucking dogshit*. The entire point of the
language — no UB, the airside/landside split, contract types, the reference
model — is a deliberate rejection of the C-shaped world LLVM bakes into its IR.
"Just use LLVM" isn't advice here, it's a category error. (Same energy for "just
rewrite it in [your framework].")

(Bug reports and "this is wrong because X" are welcome too. PRs I'll look at,
but the education is the priority.)

## Licence

ISC. See [`LICENCE`](LICENCE).
