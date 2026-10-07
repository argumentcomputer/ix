/-
  The clique order's pinned choice compares last (owner decision Q8,
  2026-10-03; design document §2.7): `Canon.CliqueMember.toMutConst` puts the
  structural `recArgPos` after the value, so it decides only between members
  whose types and values tie. Synthetic cliques of two members of one type
  (`Nat → Nat → Nat`, values constant functions):

  * values 1 and 2, pinned positions 1 and 0: the values decide (before
    2026-10-07 the positions did, giving the opposite order);
  * equal values, pinned positions 1 and 0: the positions separate them;
  * equal values, no pinned choice: one class (the valid neighbour).
-/
module
public import LSpec
public import Ix.Compile.Canon

public section

open LSpec
open Ix.Compile.Canon

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
def order (ms : Array CliqueMember) : Option (List (List String)) :=
  match cliqueClasses Rules.phaseA addr? { kind := .structural, members := ms } with
  | .ok (cls, _) => some (cls.toList.map fun c => c.toList.map (·.pretty))
  | .error _ => none

def suite : List TestSeq := [
  test "Q8: equal types, the values decide before the pinned positions (f first)"
    (order #[member "f" 1 (some 1), member "g" 2 (some 0)] == some [["f"], ["g"]]),
  test "Q8: the same clique in the other member order gives the same order"
    (order #[member "g" 2 (some 0), member "f" 1 (some 1)] == some [["f"], ["g"]]),
  test "Q8: equal types and values, the pinned positions separate them (g first)"
    (order #[member "f" 1 (some 1), member "g" 1 (some 0)] == some [["g"], ["f"]]),
  test "Q8 neighbour: equal specifications without a pinned choice form one class"
    ((order #[member "f" 1 none, member "g" 1 none]).map (·.length) == some 1)]

end Tests.Ix.Compile.CanonClique

end
