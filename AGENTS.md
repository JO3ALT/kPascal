# Repository Guidelines

## Project Structure & Module Organization
This repository is a Rust compiler/transpiler prototype that parses a Pascal-like language and emits Forth code.

- `src/main.rs`: entry point, parser wiring, AST construction, and pipeline orchestration.
- `src/ast.rs`: AST data structures (`Program`, `Stmt`, `Expr`, type nodes).
- `src/sema.rs`: semantic environment, type resolution, and constant evaluation.
- `src/codegen.rs`: Forth code generation (`ForthGen`).
- `src/kpascal.pest`: grammar definition used by Pest.
- `Cargo.toml`: crate metadata and dependencies.

Keep new modules under `src/` and add `mod ...;` declarations in `src/main.rs`.

## Build, Test, and Development Commands
- `cargo check`: fast compile/type check without building a full binary.
- `cargo build`: build debug artifacts.
- `cargo run < input.pas`: run the compiler by piping Pascal source via stdin.
- `cargo test`: run unit/integration tests.
- `cargo fmt`: format code with `rustfmt`.
- `cargo clippy -- -D warnings`: lint and fail on warnings.

Run `cargo fmt` and `cargo clippy -- -D warnings` before opening a PR.

## Coding Style & Naming Conventions
- Follow Rust 2021 idioms and default `rustfmt` style (4-space indentation).
- Use `snake_case` for functions/modules/variables, `PascalCase` for types/enums/traits, and `SCREAMING_SNAKE_CASE` for constants.
- Keep parsing, semantic analysis, and code generation concerns separated by module.
- Prefer `Result<T, String>` error propagation patterns already used in `src/main.rs` and `src/sema.rs`.

## Selfhost Pascal Grammar Notes
- When editing Pascal under `selfhost/`, treat [src/kpascal.pest](/home/kamitani/kPascal/src/kpascal.pest) as the source of truth.
- `if` follows `if <expr> then <stmt> (else <stmt>)?`.
- If either branch contains multiple statements, write it as a compound statement with `begin ... end`.
- Preferred forms:
- `if cond then begin ... end;`
- `if cond then begin ... end else begin ... end;`
- Do not write `end; else ...`. If there is an `else`, it must come immediately after the `end` that closes the `then` branch.
- Be careful in `selfhost/parser.inc`: deep nested `if/else` chains should use explicit `begin/end` blocks so the flattened Pascal still matches the Pest grammar.

## Selfhost Implementation Policy
- For `selfhost/`, [expanded.rs](/home/kamitani/kPascal/expanded.rs) is the operational reference, not just `src/kpascal.pest`.
- Keep the Pascal selfhost source as close as possible to the Rust processing units in `expanded.rs`, especially `build_type_spec`, `build_stmt`, `build_expr`, and `build_lvalue`.
- Do not start from an ad hoc evaluator and later “drift” toward Rust. Prefer a direct 1:1 translation of Rust control flow, helper boundaries, and data flow from the beginning.
- When Pascal lacks a direct language feature needed to mirror Rust structure, add helper functions/procedures instead of collapsing multiple Rust steps into one Pascal routine.
- Before extending selfhost behavior, check not only feature-level compatibility but also whether the Pascal code still matches the Rust source at the level of processing steps and call structure.
- String behavior must not be reimplemented piecemeal in parser/codegen files. Centralize string comparison, copy, normalization, and literal-transfer helpers in [string_utils.pas](/home/kamitani/kPascal/string_utils.pas).
- Avoid adding narrow one-off string helpers that duplicate existing string operations. If Rust-aligned string behavior is missing, add or fix the general helper in [string_utils.pas](/home/kamitani/kPascal/string_utils.pas) first, then use it from `selfhost/`.
- Treat string literal to `char`-array assignment as a supported language operation in selfhost, matching Rust behavior. Implement it as assignment semantics, not as an unrelated ad hoc builtin rewrite.
- For `char`-array assignment from a string literal, preserve array-copy semantics on the Pascal side: copy characters into the destination array storage and handle terminating `#0` consistently through shared helpers in [string_utils.pas](/home/kamitani/kPascal/string_utils.pas).

## Testing Guidelines
No tests are currently committed; new features should include tests.

- Unit tests: place in `#[cfg(test)] mod tests` blocks in the relevant `src/*.rs` file.
- Integration tests: place in `tests/` (create if needed), especially for end-to-end input/output cases.
- Name tests by behavior, e.g. `parses_record_field_access`, `rejects_unknown_type`.
- Execute all tests with `cargo test`.

## Commit & Pull Request Guidelines
This branch has no commit history yet, so use clear Conventional Commit-style messages:

- `feat: add repeat-until codegen`
- `fix: resolve field offset for nested records`
- `test: add parser regression for char literals`

PRs should include:
- concise summary of the change and rationale,
- linked issue (if available),
- test evidence (`cargo test`, `cargo clippy`, or sample `cargo run` output),
- notes on grammar or codegen behavior changes.
