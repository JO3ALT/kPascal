# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Is

**kpascal** is a Pascal-to-Forth compiler written in Rust. It reads Pascal source from stdin and emits Forth IL targeting the `kforthc` bootstrap runtime (32-bit). The language is a Standard Pascal-oriented core (`integer`, `boolean`, `char`, `real`, records, arrays, enums, pointers, conformant array parameters) plus kPascal extensions (`imut`, `option of`, `result of`, `cond(...)`, sum-case destructuring, record/array copy-update, typed `const`, `Map`/`Filter`/`Fold` builtins).

## Build & Test Commands

```bash
cargo check                                          # Fast type check
cargo build                                          # Debug build
cargo run -q < program.pas                          # Compile Pascal to Forth (stdout)
cargo test -q                                        # All tests
cargo test --test e2e_kforth -- --nocapture         # E2E tests (requires kforthc)
cargo test --test sample_regression -- --nocapture  # Standard Pascal sample regressions
cargo test --test selfhost_smoke -- --nocapture     # Self-hosting validation
cargo fmt                                            # Format
cargo clippy -- -D warnings                         # Lint (must pass before PR)
```

Run a single test by name:
```bash
cargo test --test e2e_kforth test_name -- --nocapture
```

## Pipeline Architecture

```
stdin → preprocess_includes() → parse_program() → check_program() → ForthGen::gen_program() → stdout
```

- **`src/main.rs`** — Entry point, include preprocessing (`(* $I filename *)`), pipeline wiring, error reporting
- **`src/ast.rs`** — All AST data structures (`Program`, `Block`, `Stmt`, `Expr`, type nodes)
- **`src/sema.rs`** — Semantic analysis: type resolution, constant evaluation, scope validation, memory layout; produces `Env` passed to codegen
- **`src/codegen.rs`** — Forth code generator (`ForthGen`); stack-based, 32-bit cells; all output to stdout
- **`src/kpascal.pest`** — PEG grammar (Pest). This is the source of truth for parser rules.

Error propagation uses `Result<T, String>` throughout.

## Test Layout

- `tests/fixtures/` — Small `.pas` programs with matching `.in`/`.out` for feature-level E2E
- `tests/samples/` — Restored Standard Pascal sample programs (`01–33`) compiled and executed against expected output
- `tests/all_syntax.rs` — Checks that Forth output contains expected primitives
- `tests/auto_fixture_e2e.rs` — Auto-discovers and runs all fixture tests
- `tests/e2e_kforth.rs` — Runs generated Forth through `kforthc`, verifies stdout
- `tests/sample_regression.rs` — Regression suite for Standard Pascal samples
- `tests/selfhost_smoke.rs` — Validates the self-hosting pipeline

Unit tests go in `#[cfg(test)] mod tests` blocks inside the relevant `src/*.rs` file.

## Self-Hosting (`selfhost/`)

The `selfhost/` directory contains a Pascal rewrite of the compiler itself.

**Critical policy:** the Pascal selfhost source must stay in **1:1 correspondence with `expanded.rs`** (the operational Rust reference, ~785KB). Do not compress multiple Rust steps into one Pascal routine; add helper procedures instead.

- **`selfhost/kpsc_main.pas`** — Main entry; flattened by `scripts/prekpascal` (sed + m4) into a single source file before compilation (no Pascal file I/O)
- **`scripts/preprocess_selfhost.sh`** — Compatibility wrapper around `prekpascal`
- No `forward` declarations — order includes/declarations strictly top-to-bottom
- String helpers belong in `selfhost/string_utils.pas`; use `StrCopy` for char-array copying; do not add duplicate wrappers

## Current Work Policy

- The Standard Pascal-oriented selfhost path is currently validated through `stage3`.
- Current checks cover:
  1. `stage1 -> stage2 -> stage3` self-recompilation on the preprocessed selfhost source,
  2. native-backend cleanliness of emitted `stage3` Forth,
  3. stage2 and stage3 regression suites over feature programs and restored samples.
- Prefer work that preserves or broadens that bootstrap coverage unless the user asks for a narrower fix.

**Every `if/then` and `else` branch in selfhost Pascal must use `begin ... end`**, even for a single statement:
```pascal
if cond then begin
  ...
end else begin
  ...
end;
```
`else if` must also wrap the inner `if` in `begin...end`.

## kforthc Output Contract

Codegen must target `kforthc`'s bootstrap runtime, not generic Forth:
- Use `PWRITE-I32`, `PWRITE-BOOL`, `PWRITE-CHAR`, `PWRITELN`, `PWRITE-HEX` for typed output
- Use `TYPE` for strings: `S" ..." TYPE`
- `S" ..."` is only valid immediately before `TYPE`, `READ-F32`, or `FNUMBER?`
- `PWRITE-HEX` emits uppercase 8-digit hex (e.g., `000000FF`)
- `.` and `EMIT` are aliases only; avoid in new codegen
- See `AVAILABLE_WORDS.txt` for the full list of allowed Forth words

## Key Language Constraints

- No implicit type coercion — no mixed `integer`/`real` arithmetic
- `case` over an enum must be exhaustive (or include `else`)
- Strings are `array[...] of char`, null-terminated (C-style); no separate `string` type
- Whole-array assignment (`dst := src`) is a fixed-size aggregate copy, not a string copy
- `dispose(p)` only stores `nil`; no actual deallocation
- `SetAddr(p, addr)` is intentionally unsafe (no address validation)
- Strict no-shadowing scope policy — locals cannot reuse outer names
- No `forward` declarations in selfhost; no file I/O; stdin/stdout only

## Include Libraries

- **`math.pas`** — Real-based math: `sqrt`, `pow`, `sin`, `cos`, `floor`, `ceil`, `f_trunc`, `f_round`
- **`selfhost/string_utils.pas`** — Fixed-buffer char-array helpers: `StrCopy`, `StrEq`, `StrEqLit`, `StrCmp`, `StartsWith`, `TrimLeft`, `TrimRight`, `AppendChar`, `AppendStr`, `ParseInt`, etc.

## Key Reference Documents

- **`SPEC.md`** — Full specification of kPascal extensions
- **`SCOPING_RULES.md`** — No-shadowing scope policy details
- **`STANDARD_PASCAL_PRECONDITIONS.md`** — Implementation assumptions and integration notes
- **`expanded.rs`** — Operational Rust reference for selfhost 1:1 correspondence

## Commit Style

Use Conventional Commits: `feat:`, `fix:`, `test:`, `refactor:`, `docs:`, `chore:`.
