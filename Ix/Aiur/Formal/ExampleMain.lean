module
public import Ix.Aiur.Meta
public import Ix.Aiur.Formal.GenSem

/-!
# Aiur Formal Verification — Example Main

Defines `ExprList` and functions that use both `Expr` (from `ExampleBase`)
and `ExprList`, demonstrating cross-toplevel type references and mutual
recursion (`is_even` / `is_odd`). Also demonstrates mutual types
(`Tree` / `Forest`), generic types (`GList‹T›` with `length‹T›`), and
unconstrained calls (`use_unconstrained` calling `#add_noise`).
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

  enum GList‹T› {
    Nil,
    Cons(T, &GList‹T›)
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

  fn length‹T›(xs: GList‹T›) -> G {
    match xs {
      GList‹T›.Nil => 0,
      GList‹T›.Cons(_, &rest) => 1 + length‹T›(rest),
    }
  }

  fn add_noise(x: G) -> G {
    x + x
  }

  fn use_unconstrained(x: G) -> G {
    x + #add_noise(x)
  }
⟧

#aiur_gen exampleMain "ExampleMainSem.lean"
  importing Ix.Aiur.Formal.ExampleBaseSem
  opening exampleBase #
