/-
  Ix.Theory.Quote: Read-back from semantic values to syntactic expressions.

  quote_s converts SVal back to SExpr at a given binding depth d.
  Under binders, it introduces fresh neutral fvars and evaluates the closure body.
  Mirrors Ix.Kernel2.Infer.quote but pure, strict, and fueled.
-/
import Ix.Theory.Eval

namespace Ix.Theory

variable {L : Type}

/-- Convert a de Bruijn level to a de Bruijn index at depth d. -/
def levelToIndex (d level : Nat) : Nat := d - 1 - level

/-- Quote a head (fvar or const) back to syntax. -/
def quoteHead (h : SHead L) (d : Nat) : SExpr L :=
  match h with
  | .fvar level => .bvar (levelToIndex d level)
  | .const id levels => .const id levels

mutual
/-- Read-back: convert a value to an expression at binding depth d.
    Closures are opened by applying a fresh fvar at level d,
    then quoting the result at depth d+1. -/
def quote_s (fuel : Nat) (v : SVal L) (d : Nat) : Option (SExpr L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match v with
    | .sort u => some (.sort u)
    | .lit n => some (.lit n)
    | .lam dom body env =>
      do let domE ← quote_s fuel dom d
         let freshVar := SVal.neutral (.fvar d) []
         let bodyV ← eval_s fuel body (freshVar :: env)
         let bodyE ← quote_s fuel bodyV (d + 1)
         some (.lam domE bodyE)
    | .pi dom body env =>
      do let domE ← quote_s fuel dom d
         let freshVar := SVal.neutral (.fvar d) []
         let bodyV ← eval_s fuel body (freshVar :: env)
         let bodyE ← quote_s fuel bodyV (d + 1)
         some (.forallE domE bodyE)
    | .neutral hd spine =>
      quoteSpine_s fuel (quoteHead hd d) spine d
    -- letE is eagerly reduced during eval, so no VLet case

/-- Quote a spine of arguments and wrap around a head expression. -/
def quoteSpine_s (fuel : Nat) (acc : SExpr L) (spine : List (SVal L)) (d : Nat) :
    Option (SExpr L) :=
  match spine with
  | [] => some acc
  | arg :: rest =>
    do let argE ← quote_s fuel arg d
       quoteSpine_s fuel (.app acc argE) rest d
end

-- Full NbE: evaluate then quote back
def nbe_s (fuel : Nat) (e : SExpr L) (env : List (SVal L)) (d : Nat) : Option (SExpr L) :=
  do let v ← eval_s fuel e env
     quote_s fuel v d

-- Sanity checks (using L := Nat)
#guard nbe_s 20 (.lit 42 : SExpr Nat) [] 0 == some (.lit 42)
#guard nbe_s 20 (.sort 1 : SExpr Nat) [] 0 == some (.sort 1)
#guard nbe_s 20 (.const 5 [] : SExpr Nat) [] 0 == some (.const 5 [])

-- Identity function roundtrips: (fun x => x) quotes back to (fun _ => bvar 0)
#guard nbe_s 20 (.lam (.sort 0) (.bvar 0) : SExpr Nat) [] 0 ==
    some (.lam (.sort 0) (.bvar 0))

-- Beta: (fun x => x) 5 normalizes to 5
#guard nbe_s 20 (.app (.lam (.sort 0) (.bvar 0)) (.lit 5) : SExpr Nat) [] 0 == some (.lit 5)

-- Beta: (fun x y => x) 1 2 normalizes to 1
#guard nbe_s 30
    (.app (.app (.lam (.sort 0) (.lam (.sort 0) (.bvar 1))) (.lit 1)) (.lit 2) : SExpr Nat)
    [] 0 == some (.lit 1)

-- Let: let x := 5 in x normalizes to 5
#guard nbe_s 20 (.letE (.sort 0) (.lit 5) (.bvar 0) : SExpr Nat) [] 0 == some (.lit 5)

-- Partial application: (fun x y => x) 3 normalizes to (fun _ => 3)
#guard nbe_s 30
    (.app (.lam (.sort 0) (.lam (.sort 0) (.bvar 1))) (.lit 3) : SExpr Nat)
    [] 0 == some (.lam (.sort 0) (.lit 3))

-- Neutral: f x y stays as app (app f x) y
#guard nbe_s 20 (.app (.app (.const 0 []) (.lit 1)) (.lit 2) : SExpr Nat) [] 0 ==
    some (.app (.app (.const 0 []) (.lit 1)) (.lit 2))

-- Under a binder: (fun f => f 1) with f free at depth 0
-- evaluates to neutral (fvar 0) applied to lit 1
#guard nbe_s 30
    (.lam (.sort 0) (.app (.bvar 0) (.lit 1)) : SExpr Nat)
    [] 0 == some (.lam (.sort 0) (.app (.bvar 0) (.lit 1)))

end Ix.Theory
