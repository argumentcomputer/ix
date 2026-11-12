import IxCCTests.Own.Owned.Interp
import IxCC.Rt.Readback

/-! # The ownership checker's suite: a refinement oracle for accepted maps

`oracleV`: run a map on the instrumented interpreter (`Interp`: production heap operations; a
read, an `inc` or a release of a dead cell, or a count driven below one, is an error there, since
the abstract heap never reuses a location) and require, against the reference result of the
accepted unmutated map on the same input: no error; the same complete value (readback); exact
counts at return (every dynamic count equals the result's references plus incoming fields:
`Balance` with no external owner); and every cell dead after the result is dropped. This is what
`checkOwned_refines` and `checkOwned_reclaims` promise for an accepted map, tested independently
of their proofs. `Rng` is the campaign's seeded generator. -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Own (RVal Heap)
open IxCC.Fir (Var)

/-! ## The oracle -/

def balancedAt (H : Heap) (v : RVal) : Bool := Id.run do
  let mut refs : Array Nat := Array.replicate H.size 0
  for c in H.cells do
    match c with
    | .live _ _ b =>
      for f in b.fields do
        match f with
        | .loc l => if l < refs.size then refs := refs.modify l (· + 1)
        | _ => pure ()
    | .dead => pure ()
  match v with
  | .loc l => if l < refs.size then refs := refs.modify l (· + 1)
  | _ => pure ()
  let mut ok := true
  for l in [0:H.size] do
    if Own.Rc.dynCount H l != refs[l]! then ok := false
  return ok

def reclaimed (H : Heap) (v : RVal) : Bool :=
  match Own.Rc.dropAll H [v] with
  | some H' => H'.cells.all fun c => match c with | .dead => true | _ => false
  | none => false

def readOf (r : Except String (RVal × Heap)) : String :=
  match r with
  | .ok (v, H) => (H.readback v).map Rt.renderObs |>.getD "?"
  | .error e => s!"error: {e}"

/-- One oracle run: `failure` is `none` when the run is safe and equal to the reference. -/
structure Verdict where
  failure : Option String
  hits : Nat
  /-- `inc` and `dec` calls on cells, and the peak of live cells. -/
  sig : Nat × Nat × Nat
  heapHash : UInt64
  fullHash : UInt64
  immHash : UInt64

/-- `failure = none` when the run is safe and equal to `reference`; otherwise what went wrong. -/
def oracleV (P : Program) (f : Nat) (args : List RVal) (reference : String) (watch : Nat) :
    Verdict :=
  let (r, c) := runI P 200000000 f args watch
  let verdict := match r with
    | .error e => some s!"run failed: {e}"
    | .ok (v, H) =>
      let got := readOf r
      if got != reference then some s!"value {got} ≠ {reference}"
      else if !balancedAt H v then some "counts at return are not exact"
      else if !reclaimed H v then some "not everything reclaimed after dropping the result"
      else none
  { failure := verdict, hits := c.hits, sig := (c.incs - c.incImm, c.decs - c.decImm, c.peak)
    heapHash := c.heapHash, fullHash := c.fullHash, immHash := c.immHash }

def oracle (P : Program) (f : Nat) (args : List RVal) (reference : String) (watch : Nat) :
    Option String × Nat × (Nat × Nat × Nat) :=
  let v := oracleV P f args reference watch
  (v.failure, v.hits, v.sig)

/-! ## A seeded generator (the campaign's) -/


structure Rng where
  s : UInt64

def Rng.next (r : Rng) (bound : Nat) : Nat × Rng :=
  let s := r.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % (max bound 1), ⟨s⟩)

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : List α) : α × Rng :=
  let (i, r) := r.next xs.length
  (xs[i]!, r)


end IxCCTests.Own.Owned
