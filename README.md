# kpascal

[日本語版 README](README.ja.md)

A Rust-friendly Pascal-to-Forth compiler prototype written in Rust.

This project started from Pascal/0 and has grown into a Rust-friendly Pascal with pragmatic extensions for porting structured Rust code to a 32-bit Forth VM.

## Project Positioning

- This is not a full ISO Pascal implementation.
- This is also not a pure/complete functional language.
- The goal is a Rust-friendly Pascal: a practical Pascal subset/extension set that preserves straightforward control flow, data layout, and explicit typing for porting code into a Forth-targeted environment.

## Features

- Pascal-like parser (`pest`) and semantic checker
- 32-bit scalar types: `integer`, `boolean`, `char`, `float` (IEEE754 binary32 bits on target cell)
- `TYPE`, `RECORD`, fixed-size `ARRAY` (1D to 3D)
- `enum` types (`type color = (red, green, blue);`) lowered to ordinal constants
- `result of T, E` type sugar (`ok(...)` / `err(...)` constructors)
- Aggregate assignment for compatible `record/array`
- Copy-update expressions for aggregates (`p with (x := 1)`, `xs with [i := v]`)
- Control flow: `if`, `case`, `while`, `repeat`, `for`
- Procedures/functions with value and `var` (by-reference) parameters
- Include directive: `(* $I filename *)` (Turbo Pascal v3 style)
- Typed scalar `const`: `const x: integer = 1;`
- Built-ins: `Read`, `ReadLn`, `Write`, `WriteLn`, `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, `WriteHex`, `Ord`, `Chr`, `Length`, `Low`, `High`
- List functional-style built-ins (list pointer ABI): `Map`, `Filter`, `Fold`
- `math.pas` include library (float math utilities such as `abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil`)
- `math_fixed.pas` include library (integer/fixed-point approximations; `fx_*`)

## Repository Layout

- `src/ast.rs`: AST definitions
- `src/kpascal.pest`: grammar
- `src/main.rs`: pipeline + include preprocessing
- `src/sema.rs`: semantic analysis and type checks
- `src/codegen.rs`: Forth code generator
- `math.pas`: Pascal float math library (`abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil`)
- `math_fixed.pas`: Pascal fixed-point math library (`fx_sqrt`, `fx_sin`, `fx_cos`, `fx_tan`, `fx_asin`, `fx_acos`, `fx_atan`, `fx_ln`, `fx_log`)
- `math_float.pas`: deprecated compatibility alias that includes `math.pas`
- `tests/`: compiler and end-to-end tests
- `AVAILABLE_WORDS.txt`: allowed target Forth words

## Build and Test

```bash
cargo build
cargo test -q --test e2e_kforth
cargo test -q --test auto_fixture_e2e
scripts/verify_backends.py
```

Note: this repository disables Rust incremental compilation for `dev`/`test` in `.cargo/config.toml` to avoid occasional corrupted incremental artifact warnings in this environment.

`scripts/verify_backends.py` runs all `tests/fixtures/*.pas` on both `kforth` and `kFORTHc(native)`.
It passes on exact output match, or on Python-oracle-equivalent math results for native `libm`-backed math paths.
It requires sibling repos `../kforth`, `../kFORTHc`, plus `llc` and `clang` (native link uses `-lm`).

Compile from stdin:

```bash
cargo run -q < tests/fixtures/all_features.pas
```

Run generated Forth with kforth (from this repository root):

```bash
(cargo run -q < tests/fixtures/all_features.pas; echo BYE) \
  | cat ../kforth/bootstrap.fth - \
  | ( ../kforth/build/kforth 2>/dev/null || ../kforth/kforth )
```

Extension showcase sample (typed `const`, `enum`, `imut`, `option`, `cond`, sum `case`):

```bash
cargo run -q < tests/fixtures/extensions_showcase_annotated.pas
```

The file includes commented-out examples of intentional compile-time errors (enum/integer mismatch, `imut` reassignment).

Expected output (normalized):

```text
42
TRUE
!
1
GREEN
100
42
15
EXT
```

Additional sample for `result`, copy-update, and pragmatic control-flow replacements:

```bash
cargo run -q < tests/fixtures/functional_ops_result_demo.pas
```

List builtin sample (`Map` / `Filter` / `Fold` over `list.pas`):

```bash
cargo run -q < tests/fixtures/list_pipeline_demo.pas
```

## Notes

- This is a practical subset, not full ISO Pascal compatibility.
- Current scope rules are strict (no-shadowing policy).
- Trigonometric/log functions in `math_fixed.pas` are integer/fixed-point approximations.
- `float` values are emitted as IEEE754 binary32 bit-patterns and use kforth float words (`FADD`, `FDIV`, `F.`, etc.).
- Explicit numeric conversions are available as builtins: `Float(integer) -> float`, `Trunc(float) -> integer`, `Round(float) -> integer`.
- Named record constructor expressions are supported in assignment/initialization contexts: `p := point(x := 1; y := 2.5)`.
- Array literals are supported in assignment/initialization contexts (with target-type checking): `xs := [1, 2, 3]`.
- `result of T, E` is available as sugar for a nominal sum type with `ok(...)` / `err(...)`.
- `case` on `enum` without `else` must be exhaustive.
- Copy-update expressions are available on aggregate variables/values: `p2 := p with (y := 99)`, `ys := xs with [1 := 20]`.
- `Map/Filter/Fold` are list builtins over a list-node ABI (`next` first, `value` payload after it).
- `Map(xs, f)` callback signature: `procedure(var src: T; var dst: T)`.
- `Filter(xs, pred)` callback signature: `function(var v: T): boolean`.
- `Fold(xs, init, f)` callback signature: `function(acc: integer; var v: T): integer`.

## License

MIT License. See `LICENSE`.
