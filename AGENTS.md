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
