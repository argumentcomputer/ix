module
public import Ix.Aiur.Meta
public import Ix.Aiur.Formal.GenSem

/-!
# Aiur Formal Verification — Example Main

Defines `ExprList` and functions that use both `Expr` (from `ExampleBase`)
and `ExprList`, demonstrating cross-toplevel type references and mutual
recursion (`is_even` / `is_odd`). Also demonstrates mutual types
(`Tree` / `Forest`).
-/

open Aiur

def exampleMain := ⟦
  enum ExprList {
    Nil,
    Cons(&Expr, &ExprList)
  }

  enum Tree {
    Leaf(G),
    Node(G, &Forest)
  }

  enum Forest {
    Empty,
    Cons(&Tree, &Forest)
  }

  fn list_sum(xs: ExprList) -> G {
    match xs {
      ExprList.Nil => 0,
      ExprList.Cons(&e, &rest) => eval(e) + list_sum(rest),
    }
  }

  fn assert_eval(e: Expr, expected: G) {
    let result = eval(e);
    assert_eq!(result, expected);
  }

  fn tree_sum(t: Tree) -> G {
    match t {
      Tree.Leaf(n) => n,
      Tree.Node(n, &f) => n + forest_sum(f),
    }
  }

  fn forest_sum(f: Forest) -> G {
    match f {
      Forest.Empty => 0,
      Forest.Cons(&t, &rest) => tree_sum(t) + forest_sum(rest),
    }
  }

  fn is_even(n: G) -> G {
    match eq_zero(n) {
      1 => 1,
      0 => is_odd(n - 1),
    }
  }

  fn is_odd(n: G) -> G {
    match eq_zero(n) {
      1 => 0,
      0 => is_even(n - 1),
    }
  }
⟧

#aiur_gen exampleMain "ExampleMainSem.lean"
  importing Ix.Aiur.Formal.ExampleBaseSem
  opening exampleBase #
