module
public import LSpec
public import Ix.IxonUniv
public import Tests.Gen.Ixon

/-! The complete universe semantic corpus retained from Tests.Ix.Tc.Unit.
Only the backend-specific P4 normal-form oracle and reduceUniv twin are
omitted. Exhaustive inputs, value checks, witnesses, seeded families,
slip conditions, bounds and rule vectors retain their original definitions.
-/

namespace Tests.Ix.IxonUniverse
open LSpec

def canonUnivSweep :
    Bool × Bool × Bool × Bool × Bool := Id.run do
  let mut p0 := true
  let mut p1 := true
  let mut p2 := true
  let mut p3 := true
  let mut p6 := true
  for u in Tests.Gen.Ixon.enumerateUniv 6 do
    let c := Ixon.canonUniv u
    let n := Ixon.CanonUniv.normalize u
    p0 := p0 && (Tests.Gen.Ixon.univDifferAt? 3 u c).isNone
    p1 := p1 && (Ixon.canonUniv c == c)
    p2 := p2 && Ixon.CanonUniv.normEqSemantic
      (Ixon.CanonUniv.normalize (Ixon.CanonUniv.linearize n)) n
    p3 := p3 && (Ixon.reduceUniv c == c)
    p6 := p6 && (Ixon.canonUniv (Ixon.reduceUniv u) == c)
  return (p0, p1, p2, p3, p6)

/-- Does `subsumption` leave a sublevel that a single other sublevel
    dominates (`canon_univ.rs::tests::has_slip`)? A constant `c@P` is
    dominated by a constant `≥ c` at a strict sub-path, or by an atom
    `(y, k)` with `k + 1 ≥ c` at a sub-path; an atom `(x, k)@P` by an
    atom `(x, ≥ k)` at a strict sub-path. `subsumption` mirrors the
    kernels' normalizers, which test a constant against its own node's
    vars instead of the dominator's (`max (v+1) (imax (imax 2 u) v)`
    keeps the constant `2` at `[u, v]`). Only such leftovers make equal
    levels' normal forms differ, so a slip-free normal form is the
    unique one of its class. -/
def normHasSlip (n : Ixon.CanonUniv.CNorm) : Bool :=
  let es := n.toList
  es.any fun (p, node) =>
    let c := node.constant
    let constDominated := c > 0 && es.any fun (q, m) =>
      Ixon.CanonUniv.isSubset q p
        && ((q.length < p.length && m.constant ≥ c)
          || m.vars.any (fun v => v.2 + 1 ≥ c))
    let varDominated := node.vars.any fun (x, k) => es.any fun (q, m) =>
      q.length < p.length && Ixon.CanonUniv.isSubset q p
        && m.vars.any (fun (y, k2) => y == x && k2 ≥ k)
    constDominated || varDominated

/-- Failures and slip-skipped draws of `checkCanon`. -/
structure CanonCheck where
  failures : Array String := #[]
  slips : Nat := 0
  count : Nat := 0

/-- P0/P1/P2/P3/P6 and class stability of one level over params `0..params`
    (`canon_univ.rs::tests::check_canon`).
    P0 and P3 are checked unconditionally. With `strict`, so are the
    rest; otherwise P1, P2 and class stability are checked when
    neither `u`'s nor its canonical form's normal form has a
    subsumption leftover (`normHasSlip`), and P6 when neither `u`'s nor
    `reduceUniv u`'s has. -/
def checkCanon (params : Nat) (strict : Bool) (acc : CanonCheck)
    (u : Ixon.Univ) : CanonCheck := Id.run do
  let mut acc := { acc with count := acc.count + 1 }
  let fail (acc : CanonCheck) (msg : String) : CanonCheck :=
    { acc with failures := acc.failures.push msg }
  let n := Ixon.CanonUniv.normalize u
  let c := Ixon.canonUniv u
  if let some vals := Tests.Gen.Ixon.univDifferAt? params u c then
    acc := fail acc s!"P0 {repr u} ↦ {repr c} at {vals}"
  if Ixon.reduceUniv c != c then
    acc := fail acc s!"P3 {repr u} ↦ {repr c}"
  let nc := Ixon.CanonUniv.normalize c
  if strict || !(normHasSlip n || normHasSlip nc) then
    if Ixon.canonUniv c != c then
      acc := fail acc s!"P1 {repr u} ↦ {repr c}"
    if !Ixon.CanonUniv.normEqSemantic (Ixon.CanonUniv.normalize (Ixon.CanonUniv.linearize n)) n then
      acc := fail acc s!"P2 {repr u}"
    if !Ixon.CanonUniv.normEqSemantic nc n then
      acc := fail acc s!"CLASS {repr u} ↦ {repr c}"
  else
    acc := { acc with slips := acc.slips + 1 }
  let r := Ixon.reduceUniv u
  if (strict || !(normHasSlip n || normHasSlip (Ixon.CanonUniv.normalize r)))
      && Ixon.canonUniv r != c then
    acc := fail acc s!"P6 {repr u} ↦ {repr c}"
  return acc

/-- A `checkCanon` run as a test: no failures (the first three shown). -/
def canonCheckTest (name : String) (r : CanonCheck) : TestSeq :=
  test s!"{name} ({r.count} levels, {r.slips} slip-skipped){
    if r.failures.isEmpty then "" else s!": {r.failures.toList.take 3}"}"
    r.failures.isEmpty

/-- P0 on the smallest value-change witness and its family (strict),
    with the witness's representative pinned (`canon_univ.rs::tests::p0_witness`
    pins the same term), and on the biased random family. -/
def canonUnivValueTests : TestSeq :=
  let (u, v, w) : Ixon.Univ × Ixon.Univ × Ixon.Univ := (.var 0, .var 1, .var 2)
  let l : Ixon.Univ := .imax (.imax (.succ (.imax u w)) u) v
  let σ : Nat → Nat := fun i => [0, 1, 2].getD i 0
  let witness := Tests.Gen.Ixon.univWitnessFamily.foldl (checkCanon 4 true) {}
  let random :=
    (Tests.Gen.Ixon.biasedUnivFamily 3 10 4000 41).foldl (checkCanon 3 false) {}
  let random4 :=
    (Tests.Gen.Ixon.biasedUnivFamily 4 12 1000 43).foldl (checkCanon 4 false) {}
  test "canonUniv P0: imax (imax (imax u w + 1) u) v keeps its value 1 at (0, 1, 2)"
    (Tests.Gen.Ixon.univEval σ l == 1 && Tests.Gen.Ixon.univEval σ (Ixon.canonUniv l) == 1)
  ++ test "canonUniv: the witness's representative is pinned (Rust pins the same)"
    (Ixon.canonUniv l == .max (.imax (.imax (.succ w) u) v)
      (.imax (.imax (.imax (.succ u) w) u) v))
  ++ test "canonUniv: complete witness and seeded context counts"
    (witness.count == 121 && random.count == 20000 && random4.count == 5000)
  ++ canonCheckTest "canonUniv P0/P1/P2/P3/P6: the witness family" witness
  ++ canonCheckTest "canonUniv P0/P1/P2/P3/P6: biased random, 3 params" random
  ++ canonCheckTest "canonUniv P0/P1/P2/P3/P6: biased random, 4 params" random4
  -- The slip is rare; a jump here means the normal forms changed.
  ++ test "canonUniv: subsumption slips stay rare (< 1 in 200)"
    ((random.slips + random4.slips) * 200 < random.count + random4.count)

def canonUnivVectors : TestSeq :=
  let v : UInt64 → Ixon.Univ := .var
  let s : Ixon.Univ → Ixon.Univ := .succ
  let z : Ixon.Univ := .zero
  test "canonUniv: commutative twins converge"
    (Ixon.canonUniv (.max (v 1) (v 0)) == .max (v 0) (v 1))
  ++ test "canonUniv: reassociation converges"
    (Ixon.canonUniv (.max (.max (v 0) (v 1)) (v 2))
      == .max (v 0) (.max (v 1) (v 2)))
  ++ test "canonUniv: succ distributes over max"
    (Ixon.canonUniv (s (.max (v 0) (v 1))) == .max (s (v 0)) (s (v 1)))
  ++ test "canonUniv: WF eq_def shape reduces"
    (Ixon.canonUniv (.imax (.imax (s z) (v 0)) (v 0)) == v 0)
  ++ test "canonUniv: common spellings are fixpoints"
    ([z, s z, v 0, s (v 0), .max (v 0) (v 1), .imax (v 0) (v 1),
      .imax (s (v 1)) (v 0),
      .imax (.imax (s (v 0)) (v 1)) (v 2)].all fun u =>
      Ixon.canonUniv u == u)
  ++ test "reduceUniv: rule table (M1/M4/M7/I2/I4 spot checks)"
    (Ixon.reduceUniv (.max (s z) (s (s z))) == s (s z)
      && Ixon.reduceUniv (.max (v 0) z) == v 0
      && Ixon.reduceUniv (.max (s (v 0)) (s (s (v 0)))) == s (s (v 0))
      && Ixon.reduceUniv (.imax (v 0) z) == z
      && Ixon.reduceUniv (.imax (s z) (v 0)) == v 0)

def canonUnivTests : TestSeq :=
  let (p0, p1, p2, p3, p6) := canonUnivSweep
  canonUnivVectors
  ++ canonUnivValueTests
  ++ test "canonUniv P0: value-preserving (exhaustive ≤6)" p0
  ++ test "canonUniv P1: idempotent (exhaustive ≤6)" p1
  ++ test "canonUniv P2: linearize∘normalize fixpoint (exhaustive ≤6)" p2
  ++ test "canonUniv P3: canonical forms are mk* fixpoints (exhaustive ≤6)"
    p3
  ++ test "canonUniv P6: mk* rebuild absorbed (exhaustive ≤6)" p6

public def suite : List TestSeq := [
  test "canonUniv: exhaustive size classes 1–6 and total 3736"
    ((List.range 6).map (fun i =>
      (Tests.Gen.Ixon.enumerateUniv (i + 1)).length -
        (Tests.Gen.Ixon.enumerateUniv i).length) == [4, 4, 36, 100, 708, 2884] &&
      (Tests.Gen.Ixon.enumerateUniv 6).length == 3736),
  canonUnivTests]

end Tests.Ix.IxonUniverse
