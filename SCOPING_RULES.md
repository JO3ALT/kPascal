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
