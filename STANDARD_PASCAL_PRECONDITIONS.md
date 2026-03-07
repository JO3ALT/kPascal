# Standard Pascal Preconditions

This worktree is aligned to the `feat/standard-pascal` baseline.

Rust-oriented extensions from `main` are intentionally removed from this tree, including features such as `Option`, `Result`, list helpers, typed `const`, `cond`, and `imut`.

Project policy and target assumptions:

- The final runtime target does not provide a filesystem, so Pascal file I/O is intentionally not implemented.
- `forward` declarations are intentionally not implemented.
- `packed` is intentionally not supported and is rejected by the grammar.
- Runtime safety checks are selective: array bounds checks are intentionally omitted for speed, while subrange checks and named variant-tag checks are inserted at runtime.
- Strings are currently represented as `array[...] of char`; no separate `string` type is provided.
- String handling is intentionally C-like: text is treated as `#0`-terminated `array[...] of char`.
- String literal assignment truncates to fit, writes at most `len - 1` characters, and appends `#0`.
- `Read(s, max_len)`, `Write(s)`, `WriteLn(s)`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `HexToInt`, and `IntToHex` all operate on `#0`-terminated text.
- `Copy`, `Concat`, `Insert`, and `Pos` also accept string literals through compiler-generated static char-array storage.
- Aggregate assignment of char arrays remains a raw fixed-size copy and does not stop at `#0`.
- Variant records are expected to use named discriminants; anonymous discriminants are intentionally excluded by policy.
- Hex formatting is provided via `IntToHex(value, var dst, max_len, zero_fill)`; no `WriteHex` built-in is kept.
- `Addr(x)` and `SetAddr(p, addr)` are intentionally kept as non-standard extensions for memory-mapped I/O style access.
- `dispose(p)` does not reclaim memory; it simply stores `nil` back into `p`.
- Static arrays support arbitrary dimensions, and conformant array parameters support multiple dimensions.
- Floating-point math functions remain include-library based; built-in numeric helpers are limited to core operations such as `Abs`, `Sqr`, `Round`, `Trunc`, `Succ`, `Pred`, and `Odd`.

End-to-end testing assumes this native backend pipeline:

```text
kpascal -> Forth IL -> kforthc -> LLVM IR -> llc -> clang -> native executable
```

Required local tools and files:

- `kforthc` is available on `PATH` (`/home/kamitani/bin/kforthc` in this environment).
- `llc` or `llc-14` is available on `PATH`.
- `clang` is available on `PATH`.
- `../kFORTHc/runtime/runtime.c` exists relative to this repository root.

Primary verification commands:

```bash
cargo test
cargo test --test e2e_kforth -- --nocapture
cargo test --test sample_regression -- --nocapture
cargo clippy -- -D warnings
```

The integration test `tests/e2e_kforth.rs` compiles generated Forth with `kforthc`, lowers it with LLVM tools, links against `../kFORTHc/runtime/runtime.c`, and executes the resulting native binary.
