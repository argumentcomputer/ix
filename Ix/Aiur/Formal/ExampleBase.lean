module
public import Ix.Aiur.Meta
public import Ix.Aiur.Formal.GenSem

/-!
# Aiur Formal Verification — Example Base

Defines a small expression language with an evaluator.
`Example.lean` builds on this with composite types.
-/

open Aiur

def exampleBase := ⟦
  type Pair = (G, G)

  enum Expr {
    Lit(G),
    Add(&Expr, &Expr),
    Neg(&Expr)
  }

  fn double_eval(e: Expr) -> G {
    eval(e) + eval(e)
  }

  fn eval(e: Expr) -> G {
    match e {
      Expr.Lit(n) => n,
      Expr.Add(&a, &b) => eval(a) + eval(b),
      Expr.Neg(&a) => 0 - eval(a),
    }
  }

  fn swap(p: Pair) -> Pair {
    (proj(p, 1), proj(p, 0))
  }

  fn simplify_neg(e: Expr) -> Expr {
    match e {
      Expr.Neg(&inner) =>
        match inner {
          Expr.Neg(&x) => x,
          Expr.Lit(n) => Expr.Lit(0 - n),
          _ => e,
        },
      _ => e,
    }
  }
⟧

#aiur_gen exampleBase "ExampleBaseSem.lean" #
