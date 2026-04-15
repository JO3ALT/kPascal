# kpascal

[日本語版 README](README.ja.md)

A practical Pascal-to-Forth compiler prototype written in Rust.

This project started from Pascal/0 and now targets a 32-bit Forth VM with a Standard Pascal-oriented core plus integrated kPascal extensions.

## Features

- Pascal-like parser (`pest`) and semantic checker
- 32-bit scalar types: `integer`, `boolean`, `char` (UTF-32 code point)
- `TYPE`, `RECORD`, variant records, fixed-size `ARRAY` (arbitrary dimensions)
- Multi-dimensional conformant array parameters
- `real` (single-precision floating point), subranges, enums, and `set of`
- Aggregate assignment for compatible `record/array`
- Control flow: `if`, `case`, `while`, `repeat`, `for`
- `with`, pointers, `new`, `dispose`, `nil`
- Procedures/functions with value and `var` (by-reference) parameters
- Include directive: `(* $I filename *)` (Turbo Pascal v3 style)
- Built-ins: `Read`, `ReadLn`, `Write`, `WriteLn`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `UpCase`, `IntToHex`, `HexToInt`, `Addr`, `SetAddr`, `Ord`, `Chr`, `Length`, `Low`, `High`, `Abs`, `Sqr`, `Round`, `Trunc`, `Succ`, `Pred`, `Odd`
- `math.pas` include library
- `selfhost/string_utils.pas` include library for fixed-size `array[...] of char` text handling
- Extensions integrated on top of the Standard Pascal core: typed `const`, `imut`, `option of`, `result of`, `record of`, `cond(...)`, named constructors, sum-case destructuring, record updates, array updates, list/functional built-ins

## Repository Layout

- `src/ast.rs`: AST definitions
- `src/kpascal.pest`: grammar
- `src/main.rs`: pipeline + include preprocessing
- `src/sema.rs`: semantic analysis and type checks
- `src/codegen.rs`: Forth code generator
- `math.pas`: Pascal math library
- `selfhost/string_utils.pas`: Pascal string helper library for fixed-size char arrays
- `tests/`: compiler and end-to-end tests
- `AVAILABLE_WORDS.txt`: allowed target Forth words

## Build and Test

```bash
cargo build
cargo test -q
cargo clippy -- -D warnings
```

Implementation assumptions and current integration notes are recorded in `STANDARD_PASCAL_PRECONDITIONS.md`.

Native end-to-end tests use `kforthc`:

```bash
cargo test --test e2e_kforth -- --nocapture
```

Sample regression tests compile and run the programs under `tests/samples/`:

```bash
cargo test --test sample_regression -- --nocapture
```

Compile from stdin:

```bash
cargo run -q < tests/fixtures/all_features.pas
```

Run generated Forth with kforth (from this repository root):

```bash
(cargo run -q < tests/fixtures/all_features.pas; echo BYE) \
  | cat ../kforth/bootstrap.fth - \
  | ../kforth/build/kforth
```

## Notes

- This is a practical subset, not full ISO Pascal compatibility.
- Floating-point source syntax uses `real` only. The old `float` type/function spelling is not accepted.
- The current Standard Pascal-oriented core does not include the removed helper I/O extensions `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, or `WriteHex`.
- Strings are represented as `array[...] of char`; there is no separate `string` type.
- String operations treat `array[...] of char` as C-style null-terminated text.
- String literal assignment writes characters up to `len - 1` and always stores `#0` in the last written slot; overflow is truncated rather than rejected.
- `Write(s)` / `WriteLn(s)`, `Read(s, max_len)`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `HexToInt`, and `IntToHex` all operate on `#0`-terminated text.
- `Copy`, `Concat`, `Insert`, and `Pos` accept either `array[...] of char` values or string literals.
- Whole-array assignment `dst := src` is still a fixed-size aggregate copy, not a `#0`-stopping string copy.
- `Addr(x)` returns the concrete target address of an lvalue as an `integer`, and `SetAddr(p, addr)` stores a raw address into a pointer variable. These are non-standard extensions intended for memory-mapped I/O style access on branches that expose them.
- `SetAddr` is intentionally unsafe: the compiler checks only that the destination is a pointer lvalue and the address is an integer. It does not validate whether the address is mapped, aligned, readable, writable, or appropriate for the pointed type.
- A memory-mapped I/O style usage example is:
  `var reg: ^integer;`
  `SetAddr(reg, $FFFF0000);`
  `reg^ := 1;`
- `dispose(p)` currently does not reclaim memory; it only stores `nil` back into `p`.
- Current scope rules are strict (no-shadowing policy).
- `case` over an `enum` must be exhaustive unless it includes `else`.
- `math.pas` provides `real`-based math helpers (`abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil`).
- `selfhost/string_utils.pas` provides fixed-size char-array helpers aimed at compiler-style text processing: `ClearStr`, `AppendChar`, `AppendStr`, `StrCopy`, `StrEq`, `StrEqLit`, `StrEqIgnoreCase`, `StrEqIgnoreCaseLit`, `HasNameEqIgnoreCase`, `StrCmp`, `StartsWith`, `TrimLeft`, `TrimRight`, and `ParseInt`.
- Typical comparison usage with fixed buffers is:
  `name := 'Pascal'; lit := 'Pascal';`
  `WriteLn(StrEqLit(name, lit));`
  `WriteLn(StrEqIgnoreCaseLit(name, lit));`
  `WriteLn(HasNameEqIgnoreCase(name, lit));`
- For an initial self-hosting compiler, the current language surface is broadly sufficient if you stay within a single-process, stdin/stdout, fixed-buffer design. What is still intentionally missing is mainly `forward`, true deallocation in `dispose`, and Pascal file I/O.
- Additional selfhost implementation rules: string literal to `array[...] of char` must stay as normal `:=` assignment semantics, ordinary text copying should use `StrCopy`, duplicate wrappers should not be added, and source handling should stay stdin-streaming oriented.
- Selfhost parser work must remain in 1:1 correspondence with `expanded.rs`; if Pascal lacks a direct construct, add helper procedures/functions instead of inventing a differently-shaped parser.
- In selfhost Pascal, every `if ... then` branch and every `else` branch must use `begin ... end`, even for a single statement. The same rule applies to `else if`.
- The test suite currently covers compiler, kforth end-to-end, and restored Standard Pascal sample regressions on `main`.
- In this repository, self-hosting should be considered complete for the Standard Pascal-oriented core. Concretely, the completion claim means the selfhost compiler path can compile and run the restored Standard Pascal sample set; the integrated kPascal extensions are outside that completion claim unless a document explicitly says otherwise.
- Current selfhost validation also checks `stage1 -> stage2 -> stage3` bootstrap progression, verifies that emitted `stage3` Forth stays native-backend clean, and regression-tests the `stage3` compiler against the restored `tests/samples` corpus.
- Self-hosting work also covers an external preprocessing path: `scripts/prekpascal` uses `sed + m4` to flatten `selfhost/kpsc_main.pas` into a single source file without relying on Pascal file I/O. `scripts/preprocess_selfhost.sh` remains as a compatibility wrapper to `prekpascal`.

## License

MIT License. See `LICENSE`.

## kforthc Output Contract
- The intended backend contract is the bootstrap-style runtime supported by `kforthc`.
- Prefer `PWRITE-I32`, `PWRITE-BOOL`, `PWRITE-CHAR`, `TYPE`, `PWRITELN`, and `PWRITE-HEX` in generated Forth.
- `.` and `EMIT` are only aliases for integer and char output.
- `S" ..."` is only assumed to be supported when immediately followed by `TYPE`, `READ-F32`, or `FNUMBER?`.
- Generate `TYPE` for string output: use `S" ..." TYPE`.
- `PWRITE-HEX` is expected to emit uppercase 8-digit hexadecimal text such as `000000FF`.
