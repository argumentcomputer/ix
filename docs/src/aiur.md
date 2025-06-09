# Aiur

Aiur is a statically typed, functional programming language designed for the
zero-knowledge proving context. Unlike many circuit DSLs, it is Turing-complete
with support for unbounded recursion, making it expressive enough to encode complex
logic such as the evaluation of other Turing-complete systems and type checking
for dependently typed constructs.

Aiur includes its own compilation pipeline, beginning with type checking to provide
some level of correctness and safety at the source level. Programs are then
simplified and lowered into a type-erased bytecode representation that preserves
the program's semantics. This low-level form serves as the input for both circuit
synthesis and witness generation.

Using Lean's metaprogramming capabilities, Aiur's frontend was purposely designed
to look like Rust.

```rust
def exampleToplevel := ⟦
  enum Nat {
    Zero,
    Succ(&Nat)
  }

  fn even(m: Nat) -> u1 {
    match m {
      Nat.Zero => 1u1,
      Nat.Succ(m) => odd(load(m)),
    }
  }

  fn odd(m: Nat) -> u1 {
    match m {
      Nat.Zero => 0u1,
      Nat.Succ(m) => even(load(m)),
    }
  }

  fn factorial_u64(n: u64) -> u64 {
    if n {
      mul(n, factorial_u64(sub(n, 1u64)))
    } else {
      1u64
    }
  }
⟧
```

## Function calls via channel balancing

## Logical branches and selectors

## Memory

## Addition

## Multiplication
