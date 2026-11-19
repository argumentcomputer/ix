import LSpec
import Ix.Common

/-!
# The dependency collector on a mutual family

`Lean.collectDependencies` and `Lean.collectDependenciesMany` (`Ix/Common.lean`) list the
dependency closure of their roots in the order the walk first reaches each declaration,
the last reached first. Visiting one member of a mutual family visits the others: from
`First`, the walk reaches `Second` through `First`'s family and, inside `Second`'s visit,
`Third`. `Third` comes after `Second` in `First`'s family as well, so the walk has to see
there that `Third` was visited meanwhile, or it visits and lists `Third` a second time.

The family below has three members, each referring to the next. Every closure of it lists
each declaration once; the closure of `First` is pinned in full, in first-discovery order.
The closures are computed when this module is compiled, from its own declarations.
-/

namespace Tests.Ix.CollectDependencies

mutual
  inductive First where
    | leaf
    | next (other : Second)
  inductive Second where
    | next (other : Third)
  inductive Third where
    | next (other : First)
end

open Lean Elab Term in
/-- The names `Lean.collectDependenciesMany` lists for the roots, in its order, computed in
the environment of this module. -/
elab "collected_names% " roots:ident* : term => do
  let roots ← roots.mapM fun r => realizeGlobalConstNoOverloadWithInfo r
  return toExpr ((Lean.collectDependenciesMany roots (← getEnv).constants).map Prod.fst)

open Lean Elab Term in
/-- The names `Lean.collectDependencies` lists for the root. -/
elab "collected_names_one% " root:ident : term => do
  let root ← realizeGlobalConstNoOverloadWithInfo root
  return toExpr ((Lean.collectDependencies root (← getEnv).constants).map Prod.fst)

def fromFirst : List Lean.Name := collected_names% First
def fromSecond : List Lean.Name := collected_names% Second
def fromThird : List Lean.Name := collected_names% Third
def fromConstructor : List Lean.Name := collected_names% Third.next
def fromTwo : List Lean.Name := collected_names% Second First
def fromFirstOne : List Lean.Name := collected_names_one% First

/-- The family and its constructors. -/
def family : List Lean.Name :=
  [``First, ``Second, ``Third, ``First.leaf, ``First.next, ``Second.next, ``Third.next]

/-- The closure of `First` as the walk reaches it: `First`, then `Second` with `Third`
inside it, `Third`'s and `Second`'s constructors, then `First`'s; the last reached first. -/
def firstExpected : List Lean.Name :=
  [``First.next, ``First.leaf, ``Second.next, ``Third.next, ``Third, ``Second, ``First]

def distinct (ns : List Lean.Name) : Bool := ns.eraseDups.length == ns.length

def sameSet (ns ms : List Lean.Name) : Bool :=
  ns.length == ms.length && ns.all ms.contains && ms.all ns.contains

open LSpec in
def suite : List TestSeq := [
  test "the closure of First lists each declaration once" (distinct fromFirst),
  test "the closure of First, in first-discovery order" (fromFirst == firstExpected),
  test "the closure of Second lists the family once" (distinct fromSecond && sameSet fromSecond family),
  test "the closure of Third lists the family once" (distinct fromThird && sameSet fromThird family),
  test "the closure of a constructor lists the family once"
    (distinct fromConstructor && sameSet fromConstructor family),
  test "two roots of one family share one walk" (distinct fromTwo && sameSet fromTwo family),
  test "the single-root collector agrees" (fromFirstOne == fromFirst)
]

end Tests.Ix.CollectDependencies
