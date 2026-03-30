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
- `string_utils.pas` provides fixed-buffer text helpers for compiler-style code: `ClearStr`, `AppendChar`, `AppendStr`, `StrCopy`, `StrEq`, `StrEqLit`, `StrEqIgnoreCase`, `StrEqIgnoreCaseLit`, `HasNameEqIgnoreCase`, `StrCmp`, `StartsWith`, `TrimLeft`, `TrimRight`, and `ParseInt`.
- The safest first selfhost-side adoption point for these helpers is not the `IsExact*Name` literal checks but variable-to-variable predicates such as `IsStringVar`, where repeated `HasName(...) and StrEqIgnoreCase(...)` chains can be consolidated without introducing literal-argument calling constraints.
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
- For self-hosting, the current language surface is considered sufficient for an initial compiler that uses stdin/stdout, include files, and fixed-size buffers rather than filesystem-driven compilation units.
- Selfhost implementation should follow the same constraints operationally: declarations must be ordered without `forward`, string literal to char-array transfer belongs to normal `:=` assignment semantics, ordinary text copying should go through `StrCopy`, duplicate wrappers should not be introduced, and stdin streaming is preferred over full-source preload.
- The selfhost parser is expected to stay in 1:1 correspondence with `expanded.rs`; where Pascal is too weak to mirror a Rust step directly, add helper procedures/functions rather than reshaping the parser logic.
- Selfhost coding style for conditionals is stricter than the general grammar: every `then` branch and every `else` branch must be an explicit `begin ... end` block, including single-statement branches and `else if` chains.

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

In this repository, "self-hosting complete" is scoped to the Standard Pascal-oriented core. Concretely, that means the selfhost compiler path can compile and run the restored Standard Pascal sample set; it does not, by itself, claim selfhost completion for the integrated kPascal extensions.

Self-hosting validation also includes a preprocessed single-source path. `scripts/prekpascal` uses `sed + m4` to flatten `selfhost/kpsc_main.pas` without requiring Pascal-side file I/O, and `scripts/preprocess_selfhost.sh` remains as a compatibility wrapper to that entry point.

## kforthc Output Contract
- The Forth backend contract is `kforthc`'s bootstrap-style runtime surface.
- Output generation should prefer `PWRITE-I32`, `PWRITE-BOOL`, `PWRITE-CHAR`, `PWRITE-STR`, `PWRITELN`, and `PWRITE-HEX`.
- `.` and `EMIT` may exist as aliases, but they are not the primary output contract for generated code.
- `S" ..."` is assumed to be valid only when immediately followed by `PWRITE-STR`, `READ-F32`, or `FNUMBER?`.
- `TYPE` must not be assumed for string-output compatibility.
