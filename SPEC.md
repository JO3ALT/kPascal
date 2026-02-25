# kPascal Rust-Friendly Extensions Spec

This document records compatibility-preserving, Rust-friendly extensions added on top of the current Pascal subset.

## Positioning

- This is not a full ISO Pascal specification.
- This is also not a pure/complete functional language specification.
- The goal of these extensions is a Rust-friendly Pascal: pragmatic language features that improve portability from Rust-style code while preserving explicit control flow and predictable data layout on the Forth-targeted runtime.

## Compatibility

- Existing `if ... then ... else` remains a statement and is unchanged.
- Existing `record`, `array`, `case` (constant labels), `procedure`, `function` behavior remains.
- New features are additive: `record of`, `option of`, `cond(...)`, `imut`, and sum-deconstruction `case`.

## 1. Conditional Record (`record of`)

Tagged sum type (safe union).

```pascal
type
  x = record of
    a: (p: integer; q: integer);
    b: (value: integer);
    c: ();
  end;
```

- Value layout uses a tag cell + payload cells.
- Arms are constructed with named arguments:
  - `a(p := 1; q := 2)`
  - `b(value := 3)`
  - `c()`

## 2. `option of t` (sugar)

`option of t` is sugar for:

```pascal
record of
  none: ();
  some: (value: t);
end
```

Constructor sugar:

- `none`
- `some(expr)`

## 3. Sum Deconstruction `case`

Sum values can be safely deconstructed:

```pascal
case x of
  none(): y := 0;
  some(v): y := v
end
```

- Bind count must match the arm field count.
- Exhaustive arms are recommended; current implementation also accepts `else:`.

## 4. `cond(...)` Expression + `value`

Expression-level conditional with short-circuit evaluation.

```pascal
x := cond(
  a > 0: begin
    value a
  end;
  b > 0: begin
    value b
  end;
  else: begin
    value 0
  end
);
```

- Arms are checked top-to-bottom.
- First true condition executes its block only (later conditions/blocks are not evaluated).
- `else:` is required.
- Every arm must end with `value <expr>`.
- All `value` expressions must have the same type.

## 5. `imut` Declarations

Immutable local/global variables:

```pascal
imut
  x: integer;
```

Current compiler checks:

- must be initialized exactly once
- reassignment is rejected
- use before initialization is rejected
- passing an `imut` variable to a `var` parameter is rejected

## 6. Typed `const` (scalar)

`const` declarations can optionally carry a scalar type annotation.

```pascal
const
  answer: integer = 42;
  yes: boolean = true;
  ch: char = 'A';
```

- Supported typed-const values are current scalar const expressions (`integer`, `boolean`, `char`).
- Type mismatch is rejected during semantic analysis.

## 6.5 `enum` (ordinal lowering)

Enumeration type declarations are supported:

```pascal
type
  color = (red, green, blue);
```

- Enum labels are introduced as ordinal constants (`red = 0`, `green = 1`, ...).
- Code generation uses integer cells, but semantic analysis treats enum types nominally (distinct from `integer` and from other enums).

## 6.6 `float` (binary32 on target cell)

`float` is supported as a scalar type.

```pascal
var
  x: float;
begin
  x := 1.5;
  WriteLn(x)
end.
```

- Runtime representation is IEEE754 binary32 bit-pattern in one 32-bit cell.
- Arithmetic: `+ - * /`
- Comparisons: `= <> < <= > >=`
- I/O: `Read(x)` uses `PREAD-F32`, `Write/WriteLn(x)` uses `F.`

Current pragmatic limits:

- `mod` is not supported for `float`
- `case` on `float` is not supported
- mixed `integer`/`float` arithmetic is not implicitly converted
- `Ord(float)` and `WriteHex(float)` are rejected

## 6.7 `result of T, E` (sugar)

`result of T, E` is sugar for a nominal sum type with two arms:

- `ok(value: T)`
- `err(error: E)`

Example:

```pascal
type
  rint = result of integer, integer;
```

Constructors:

- `ok(value := 42)`
- `err(error := 7)`

## 6.8 Copy-Update for Aggregates

Pragmatic immutable-style update syntax is supported for `record` and `array`.

```pascal
p2 := p with (y := 99);
ys := xs with [1 := 20, 3 := 40];
```

- Semantics: copy base aggregate, then overwrite the listed fields/elements.
- Current parser form uses an identifier as the base expression (`p`, `xs`).

## 6.9 Enum `case` Exhaustiveness

When `case` expression type is an `enum` and there is no `else`, all enum labels must be covered.

```pascal
case c of
  red: ...;
  green: ...;
  blue: ...
end
```

This is checked during semantic analysis.

## 6.10 List Functional Helpers (Pragmatic Builtins)

To improve portability from Rust-style iterator/list processing without full higher-order functions,
the compiler provides list builtins over a common node ABI.

- `Map(xs, f) -> list`
- `Filter(xs, pred) -> list`
- `Fold(xs, init, f) -> integer`

Constraints:

- node type must be a record with:
  - first field `next: ^self`
  - field `value: T` after `next`
- callback is a routine name identifier (not lambda/closure)
- callback signatures are checked:
  - `Map`: `procedure(var src: T; var dst: T)`
  - `Filter`: `function(var v: T): boolean`
  - `Fold`: `function(acc: integer; var v: T): integer`

## 7. Error Message Source Hints

Parser and semantic errors include source-line hints when location can be identified:

- line/column
- the source line text
- caret (`^`) marker

This is best-effort for semantic errors that reference a symbol name.

## 8. Fixture Auto E2E (test convention)

`tests/fixtures/*.out` files opt fixtures into automatic compile+run E2E tests on kforth.

- `foo.pas` : source
- `foo.in`  : optional runtime input
- `foo.out` : expected normalized runtime output

Implemented by `tests/auto_fixture_e2e.rs`.

## Required Examples

### Extension Showcase (Annotated)

See `tests/fixtures/extensions_showcase_annotated.pas` for a compact example that combines:

- typed scalar `const`
- nominal `enum`
- `imut` aggregate initialization
- `option of`
- `cond(...)`
- sum deconstruction `case`

It also includes commented-out examples of intentional type/immutability errors.

### Functional-Style Pragmatic Helpers

See `tests/fixtures/functional_ops_result_demo.pas` for a compact example combining:

- `result of T, E`
- enum `case` exhaustiveness
- record/array copy-update

See `tests/fixtures/list_pipeline_demo.pas` for `list.pas` + `Map` / `Filter` / `Fold`.

### Option + `cond`

```pascal
type
  optint = option of integer;

function findpositive(a: integer; b: integer): optint;
begin
  findpositive := cond(
    a > 0: begin
      value some(a)
    end;
    b > 0: begin
      value some(b)
    end;
    else: begin
      value none
    end
  )
end;
```

### Option `case`

```pascal
procedure useopt(x: optint);
begin
  case x of
    none(): y := 0;
    some(v): y := v
  end
end;
```

### `cond` short-circuit with side effects

Covered by integration test `e2e_cond_short_circuits_side_effects_on_kforth`.

## Current Implementation Notes (Pragmatic Limits)

- Keywords are case-sensitive in the current parser (existing project behavior).
- `cond(...)` code generation is implemented for assignment contexts (including function-result assignment).
- Sum-case codegen currently supports scalar bindings (e.g. `some(v)` where `v` is scalar).
- `typed const` is currently scalar-only (aggregate typed constants are not yet implemented).
