# kpascal

[日本語版 README](README.ja.md)

A practical Pascal-to-Forth compiler prototype written in Rust.

This project started from Pascal/0 and now targets a 32-bit Forth VM with a Standard Pascal-oriented core plus branch-specific extensions.

## Features

The exact feature surface depends on the branch. The items below describe the shared public direction of the project; branch-specific restrictions or additions should be documented alongside that branch.

- Pascal-like parser (`pest`) and semantic checker
- 32-bit scalar types: `integer`, `boolean`, `char` (UTF-32 code point)
- `TYPE`, `RECORD`, variant records, fixed-size `ARRAY` (arbitrary dimensions)
- Multi-dimensional conformant array parameters
- `real`, subranges, enums, and `set of`
- Aggregate assignment for compatible `record/array`
- Control flow: `if`, `case`, `while`, `repeat`, `for`
- `with`, pointers, `new`, `dispose`, `nil`
- Procedures/functions with value and `var` (by-reference) parameters
- Include directive: `(* $I filename *)` (Turbo Pascal v3 style)
- Built-ins: `Read`, `ReadLn`, `Write`, `WriteLn`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `UpCase`, `IntToHex`, `HexToInt`, `Addr`, `SetAddr`, `Ord`, `Chr`, `Length`, `Low`, `High`, `Abs`, `Sqr`, `Round`, `Trunc`, `Succ`, `Pred`, `Odd`
- `math.pas` include library (integer/fixed-point approximations)

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

Standard Pascal branch assumptions are recorded in `STANDARD_PASCAL_PRECONDITIONS.md`.

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
- The exact language surface is branch-specific. This branch keeps the public README generic; branch-local policy should live in branch-specific documents such as `STANDARD_PASCAL_PRECONDITIONS.md`.
- Strings are represented as `array[...] of char`; there is no separate `string` type.
- String operations treat `array[...] of char` as C-style null-terminated text.
- String literal assignment writes characters up to `len - 1` and always stores `#0` in the last written slot; overflow is truncated rather than rejected.
- `Write(s)` / `WriteLn(s)`, `Read(s, max_len)`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `HexToInt`, and `IntToHex` all operate on `#0`-terminated text.
- `Copy`, `Concat`, `Insert`, and `Pos` accept either `array[...] of char` values or string literals.
- Whole-array assignment `dst := src` is still a fixed-size aggregate copy, not a `#0`-stopping string copy.
- `Addr(x)` returns the concrete target address of an lvalue as an `integer`, and `SetAddr(p, addr)` stores a raw address into a pointer variable. These are non-standard extensions intended for memory-mapped I/O style access on branches that expose them.
- A memory-mapped I/O style usage example is:
  `var reg: ^integer;`
  `SetAddr(reg, $FFFF0000);`
  `reg^ := 1;`
- Current scope rules are strict (no-shadowing policy).
- Trigonometric/log functions in `math.pas` are integer/fixed-point approximations.

## License

MIT License. See `LICENSE`.
