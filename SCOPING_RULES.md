# Scoping Rules

This compiler uses a strict **no-shadowing** policy for now.

## Identifier Kinds
- `const`
- `type`
- `var`
- `procedure` / `function`
- routine parameters

## Current Policy
1. Names must be unique in the same declaration scope.
2. Shadowing outer names is not allowed for local variables and parameters.
3. Routine names must be globally unique.
4. `const` and `type` names are treated as globally unique in the current implementation.

## Practical Implications
- A local variable cannot reuse a global variable name.
- A parameter cannot reuse a global variable name.
- Nested routines are allowed, but their names must not collide with existing routine names.

## Error Message Style
Semantic errors include scope context, for example:
- `name conflict in program.procedure Foo: local variable 'x' shadows an outer name (shadowing is not allowed)`
- `routine redefined in program: Bar`

## Note
This is an intentional simplification to keep code generation predictable. If needed, this can be relaxed later to Pascal-style lexical shadowing.

## Selfhost Constraints
- Selfhost declarations must still obey top-to-bottom ordering because `forward` is not implemented.
- String literal to char-array transfer is treated as normal `:=` assignment semantics; ordinary text copying should use `StrCopy`.
- Duplicate string-copy wrappers should not be introduced.
- Selfhost input handling is intended to be stdin-streaming oriented rather than based on full-source preload.
- Selfhost parser work should still track `expanded.rs` 1:1; missing expression power on the Pascal side should be handled with helper procedures/functions, not parser drift.
- In selfhost Pascal conditionals, every `then` and `else` branch must be written as `begin ... end`, even for single statements.

## kforthc Backend Note
- Backend-facing output must follow `kforthc`'s bootstrap-style surface.
- Prefer `PWRITE-I32`, `PWRITE-BOOL`, `PWRITE-CHAR`, `TYPE`, `PWRITELN`, and `PWRITE-HEX`.
- Use `TYPE` for string output compatibility: `S" ..." TYPE`.
- Treat `S" ..."` as valid only for the `kforthc`-supported consumers `TYPE`, `READ-F32`, and `FNUMBER?`.
- Treat `PWRITE-HEX` output as uppercase 8-digit hexadecimal text.
