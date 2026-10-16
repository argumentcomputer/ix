/-
  canon-clique: the clique order's pinned choice compares last.
  `Canon.CliqueMember.toMutConst` puts the structural `recArgPos` after the
  value, so it decides only between members whose types and values tie.
  Synthetic cliques of two members of one type (`Nat → Nat → Nat`, values
  constant functions), under the compiler's rules:

  * values 1 and 2, pinned positions 1 and 0: the values decide;
  * the same clique in the other member order gives the same order;
  * equal values, pinned positions 1 and 0: the positions separate them;
  * equal values, no pinned choice: one class (the valid neighbour).
-/
import LSpec
import Ix.Compile.Canon

open LSpec
open _root_.Ix.Compile.Canon

namespace Tests.Ix.Compile.CanonClique

def nm (s : String) : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon s

def natTy : Ix.Expr := Ix.Expr.mkConst (nm "Nat") #[]

def fnTy : Ix.Expr :=
  Ix.Expr.mkForallE (nm "a") natTy (Ix.Expr.mkForallE (nm "b") natTy natTy .default) .default

/-- `fun a b => k`. -/
def constFn (k : Nat) : Ix.Expr :=
  Ix.Expr.mkLam (nm "a") natTy (Ix.Expr.mkLam (nm "b") natTy (Ix.Expr.mkLit (.natVal k)) .default) .default

/-- Every external reference (`Nat`) at one fixed address. -/
def addr? : Ix.Name → Option Address := fun _ => some (Address.blake3 "Nat".toUTF8)

def member (s : String) (k : Nat) (p : Option Nat) : CliqueMember :=
  { name := nm s, levelParams := #[], type := fnTy, value := constFn k, recArgPos := p }

/-- The classes, in canonical order, by member name. -/
def order (rules : Rules) (ms : Array CliqueMember) : Option (List (List String)) :=
  match cliqueClasses rules addr? { kind := .structural, members := ms } with
  | .ok (cls, _) => some (cls.toList.map fun c => c.toList.map (·.pretty))
  | .error _ => none

def suiteFor (rules : Rules) (label : String) : List TestSeq := [
  test s!"{label}: equal types, the values decide before the pinned positions (f first)"
    (order rules #[member "f" 1 (some 1), member "g" 2 (some 0)] == some [["f"], ["g"]]),
  test s!"{label}: the same clique in the other member order gives the same order"
    (order rules #[member "g" 2 (some 0), member "f" 1 (some 1)] == some [["f"], ["g"]]),
  test s!"{label}: equal types and values, the pinned positions separate them (g first)"
    (order rules #[member "f" 1 (some 1), member "g" 1 (some 0)] == some [["g"], ["f"]]),
  test s!"{label}: equal specifications without a pinned choice form one class"
    ((order rules #[member "f" 1 none, member "g" 1 none]).map (·.length) == some 1)]

def suite : List TestSeq := suiteFor Rules.compiler "compiler"

end Tests.Ix.Compile.CanonClique
