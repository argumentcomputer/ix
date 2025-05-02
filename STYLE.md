# Ix Style Guide

Keep all lines under 80 columns. This is restrictive, but is the only way to
ensure readability in every environment.

Indent using two-spaces, never put tabs in a source file.

Structure declarations should not align the type-signatures of their parameters.
Prefer

```lean
structure Foo where
  parameterAcme : A
  condition1 : B
```

over

```lean4
structure Foo where
  parameterAcme : A
  condition1    : B
```

Minimize usage of unicode where ascii equivalents exist. Prefer

```lean4
def foo (A: Type) (x: A) : Foo -> Bar
| foo => bar
```

over

```
def foo (α: Type) (x: α) : Foo → Bar
| foo => bar
```

