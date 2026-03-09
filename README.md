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
- Extensions integrated on top of the Standard Pascal core: typed `const`, `imut`, `option of`, `result of`, `record of`, `cond(...)`, named constructors, sum-case destructuring, record updates, array updates, list/functional built-ins

## Repository Layout

- `src/ast.rs`: AST definitions
- `src/kpascal.pest`: grammar
- `src/main.rs`: pipeline + include preprocessing
- `src/sema.rs`: semantic analysis and type checks
- `src/codegen.rs`: Forth code generator
- `math.pas`: Pascal math library
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
- The test suite currently covers compiler, kforth end-to-end, and restored Standard Pascal sample regressions on `main`.

## License

MIT License. See `LICENSE`.
