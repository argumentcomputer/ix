/- Regression tests for the DAG helpers against the unchanged tree helpers.
   Shared nodes occur at different binder depths; low-fuel failures and the
   exact fresh-variable stream have successful neighbours. -/
module
public import LSpec
public import Ix.Compile.Clique.WFConjugation
public section

namespace Tests.Ix.Compile.CliqueDag
open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.Compile.Clique

def nm (s : String) : Name := Name.mkStr Name.mkAnon s

def samples : Array Expr := Id.run do
  let x := Expr.mkFVar (nm "x")
  let c := Expr.mkConst (nm "C") #[]
  let mut out := #[x, c, Expr.mkBVar 0, Expr.mkBVar 1, Expr.mkBVar 5]
  for k in [0:4] do
    let shared := Expr.mkApp out[k]! out[k + 1]!
    out := out ++ #[
      shared, Expr.mkApp shared shared,
      Expr.mkLam (nm "a") shared (Expr.mkApp shared (Expr.mkBVar 1)) .implicit,
      Expr.mkForallE (nm "b") shared (Expr.mkApp shared (Expr.mkBVar 0)) .default,
      Expr.mkLetE (nm "v") c shared (Expr.mkApp shared (Expr.mkBVar 2)) false,
      Expr.mkProj (nm "S") k shared]
  return out

/-- Compare the full derived tree representations, including constructor fields,
rather than Expr's hash-only BEq. This is regression evidence, not a proof. -/
def sameTree (a b : Expr) : Bool := reprStr a == reprStr b

def helpersAgree : Bool := samples.all fun e =>
  (List.range 5).all fun k =>
    (List.range 4).all fun n =>
      sameTree (liftLoose e n k) (_root_.Ix.Compile.Canon.liftLoose e n k) &&
      sameTree (lowerLoose e n k) (_root_.Ix.Compile.Canon.lowerLoose e n k) &&
      looseAtLeast e k == _root_.Ix.Compile.Canon.looseAtLeast e k &&
      sameTree (instantiateRev e #[Expr.mkBVar k, Expr.mkFVar (nm "x")])
        (_root_.Ix.Compile.Canon.instantiateRev e #[Expr.mkBVar k, Expr.mkFVar (nm "x")]) &&
      sameTree (abstractFVars #[nm "x", nm "y", nm "x"] e)
        (_root_.Ix.Compile.Image.abstractFVars #[nm "x", nm "y", nm "x"] e)

def layout : WFLayout := {
  n := 2, sigma := #[1, 0], mutualName := nm "source", newMutualName := nm "target",
  numFixed := 0, fixedPerm := #[], leaves := #[] }

/-- The same shared application is visited first with enough fuel and then
with too little: a memo keyed only by expression would incorrectly succeed. -/
def fuelTerm : Expr :=
  let shared := Expr.mkApp (Expr.mkConst (nm "f") #[]) (Expr.mkConst (nm "a") #[])
  Expr.mkApp shared (Expr.mkApp shared shared)

def fuelRejected : Bool :=
  match (ownedWFCalls layout (Expr.mkBVar 0) 3 0 fuelTerm).run' with
  | .error reason => reason == "WF ownership: body recursion bound"
  | .ok _ => false

def fuelAccepted : Bool :=
  match (ownedWFCalls layout (Expr.mkBVar 0) 4 0 fuelTerm).run' with
  | .ok result => result == fuelTerm
  | .error _ => false

def freshPreserved : Bool :=
  let e := Expr.mkBVar 0
  let allocating : TransportMemoM Expr := do
    let n ← liftM freshFVar
    return Expr.mkFVar n
  let action : TransportMemoM (Expr × Expr) := do
    let first ← memoTransport e 1 0 allocating
    let second ← memoTransport e 1 0 allocating
    return (first, second)
  match ((action.run' {}).run {}) with
  | .ok ((first, second), state) =>
    state.next == 2 && first == Expr.mkFVar (Name.mkNat fvarRoot 0) &&
      second == Expr.mkFVar (Name.mkNat fvarRoot 1)
  | .error _ => false

def firstOccurrences : Bool :=
  let a := Expr.mkConst (nm "a") #[]
  let b := Expr.mkConst (nm "b") #[]
  let shared := Expr.mkApp b a
  constOccurrences (fun _ => true) (Expr.mkApp shared (Expr.mkApp a shared)) ==
    #[nm "b", nm "a"]

def suite : List TestSeq := [
  test "DAG arithmetic agrees with original helpers across shared binder depths" helpersAgree,
  test "DAG memo preserves a low-fuel refusal after a larger-fuel visit" fuelRejected,
  test "DAG fuel neighbour succeeds at sufficient depth" fuelAccepted,
  test "DAG memo preserves both fresh allocations and the exact counter" freshPreserved,
  test "DAG traversal preserves first occurrence order" firstOccurrences]

end Tests.Ix.Compile.CliqueDag
end

