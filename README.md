# kpascal

[日本語版 README](README.ja.md)

A practical Pascal-to-Forth compiler prototype written in Rust.

This project started from Pascal/0 and now includes `TYPE`, `RECORD`, arrays (up to 3 dimensions), nested procedures/functions, and typed I/O utilities targeting a 32-bit Forth VM.

## Features

- Pascal-like parser (`pest`) and semantic checker
- 32-bit scalar types: `integer`, `boolean`, `char` (UTF-32 code point)
- `TYPE`, `RECORD`, fixed-size `ARRAY` (1D to 3D)
- Aggregate assignment for compatible `record/array`
- Control flow: `if`, `case`, `while`, `repeat`, `for`
- Procedures/functions with value and `var` (by-reference) parameters
- Include directive: `(* $I filename *)` (Turbo Pascal v3 style)
- Built-ins: `Read`, `ReadLn`, `Write`, `WriteLn`, `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, `WriteHex`, `Ord`, `Chr`, `Length`, `Low`, `High`
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
- Current scope rules are strict (no-shadowing policy).
- Trigonometric/log functions in `math.pas` are integer/fixed-point approximations.

## License

MIT License. See `LICENSE`.
