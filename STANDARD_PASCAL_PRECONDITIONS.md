# Standard Pascal Integration Notes

This worktree is based on the `feat/standard-pascal` line, but it no longer strips `main`-branch language features. The current state is a Standard Pascal-oriented core with the kPascal extensions integrated on top.

Current language policy:

- The current Standard Pascal-oriented core includes: `record`, variant record, fixed-size `array`, conformant array parameters, `set of`, subranges, enums, `with`, pointers, `new`, `dispose`, `nil`, `case`, `while`, `repeat`, `for`, nested routines, and the scalar/string helpers listed below.
- The integrated kPascal extensions on top of that core are: typed `const`, `imut`, `option of`, `result of`, `record of`, `cond(...)`, named constructors, record updates, array updates, sum-case destructuring, and the list/functional built-ins.
- Floating-point source syntax uses `real` only. `real` is implemented as single-precision floating point. The old `float` spelling is intentionally rejected.
- Strings are represented as `array[...] of char`; there is no separate `string` type.
- String handling is intentionally C-like: text is treated as `#0`-terminated `array[...] of char`.
- String literal assignment truncates to fit, writes at most `len - 1` characters, and appends `#0`.
- `Read(s, max_len)`, `Write(s)`, `WriteLn(s)`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `HexToInt`, and `IntToHex` all operate on `#0`-terminated text.
- `Copy`, `Concat`, `Insert`, and `Pos` also accept string literals through compiler-generated static char-array storage.
- Aggregate assignment of char arrays remains a raw fixed-size copy and does not stop at `#0`.
- The removed helper I/O extensions `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, and `WriteHex` are intentionally not part of the current language surface.
- Runtime safety checks are selective: array bounds checks are intentionally omitted for speed, while subrange checks and named variant-tag checks are inserted at runtime.
- `case` over an enum must be exhaustive unless an `else` arm is present.
- `forward` declarations are intentionally not implemented.
- `packed` is intentionally not supported and is rejected by the grammar.
- `Addr(x)` and `SetAddr(p, addr)` are intentionally kept as non-standard extensions for memory-mapped I/O style access.
- `SetAddr` is intentionally unsafe: only the pointer-lvalue/integer types are checked. The compiler does not try to validate the runtime address value, mapping, alignment, accessibility, or pointee-type correctness.
- `dispose(p)` does not reclaim memory; it simply stores `nil` back into `p`.
- The final runtime target does not provide a filesystem, so Pascal file I/O is intentionally not implemented.

End-to-end testing assumes this native backend pipeline:

```text
kpascal -> Forth IL -> kforthc -> LLVM IR -> llc -> clang -> native executable
```

Required local tools and files:

- `kforthc` is available on `PATH`.
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

At the time of this document, all of the commands above pass in this worktree. The active `main` test set covers compiler checks, kforth end-to-end execution, error-message regressions, enum semantics, and the restored Standard Pascal sample regressions.
