import IxCC.Xv.Validate.NatMap
import IxCC.Xv.Syntax
import IxCC.Xv.Slots

/-!
# The validator's abstract state

`AState` maps each location to the set of virtual registers whose
current value it holds: `v ∈ a[l]` means that, in the matching runs, the Xl
location `l` equals Xv's `ρ v`. A missing location holds nothing known;
there is no `Top` (regalloc2 gap 2), and `≤` is pointwise inclusion, so a
smaller state claims less. The soundness argument (`Validate.sound`)
needs only that `Agree` is antitone in `≤` and preserved by each transfer
function below.

Everything here is kernel-evaluable (D17): locations are keyed by `Nat` in a
`NatMap`, sets are sorted lists, and every function recurses structurally.

- `stepMove`: a move copies the source's set to the destination; a move from
  a location holding nothing known leaves the destination holding nothing
  known (regalloc2 gap 1).
- `define`: a definition removes its register from every location (its old
  value is gone), then the destination holds exactly it.
- `bindParams`: an edge's parallel binding of block parameters, as a
  symbolic move over registers (regalloc2 `checker.rs:562-599`): each
  location loses the parameters and gains every parameter whose argument it
  holds. -/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg)

/-! ## Locations as keys -/

/-- An injective key: registers `0–15`, then slots, incoming and outgoing
cells interleaved. -/
def locKey : Loc → Nat
  | .reg r => gprIndex r
  | .slot i => 16 + 3 * i
  | .inArg i => 17 + 3 * i
  | .outArg i => 18 + 3 * i

/-- Whether a key is an outgoing cell's. -/
def isOutArgKey (k : Nat) : Bool := decide (18 ≤ k) && (k - 18) % 3 == 0

/-! ## Sets of registers (sorted, without duplicates) -/

abbrev VSet := List VReg

namespace VSet

def mem (x : VReg) : VSet → Bool
  | [] => false
  | y :: ys => if x == y then true else if x < y then false else mem x ys

def insert (x : VReg) : VSet → VSet
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insert x ys

/-- `xs` without `x`. A filter: on the sorted sets built here it is the
same as stopping at `x`'s place, and it is correct without sortedness, which
`Validate.sound` then need not track. -/
def erase (x : VReg) (xs : VSet) : VSet := xs.filter (· != x)

def subset (xs ys : VSet) : Bool := xs.all (mem · ys)

def ofList (xs : List VReg) : VSet := xs.foldl (fun s x => insert x s) []

end VSet

/-! ## States -/

/-- Locations (by `locKey`) to the registers they hold; absent is `∅`. -/
abbrev AState := NatMap VSet

namespace AState

def empty : AState := .leaf

def get (a : AState) (l : Loc) : VSet := (a.find? (locKey l)).getD []

/-- Set a location's registers; `∅` removes the entry. -/
def set (a : AState) (l : Loc) (vs : VSet) : AState :=
  match vs with
  | [] => a.erase (locKey l)
  | _ => a.insert (locKey l) vs

def holds (a : AState) (l : Loc) (v : VReg) : Bool := VSet.mem v (a.get l)

/-- `a ≤ b`: every fact of `a` is a fact of `b`. -/
def le (a b : AState) : Bool :=
  a.all fun k vs => VSet.subset vs ((b.find? k).getD [])

/-- A move `dst ← src` (gap 1: an unknown source leaves `dst` unknown). -/
def stepMove (a : AState) (dst src : Loc) : AState := a.set dst (a.get src)

/-- Forget `v` everywhere (its value is about to change). -/
def forget (a : AState) (v : VReg) : AState :=
  a.filterMap fun _ vs => match VSet.erase v vs with
    | [] => none
    | vs => some vs

/-- Forget whatever a location holds. -/
def clear (a : AState) (l : Loc) : AState := a.erase (locKey l)

/-- Forget every outgoing stack cell (a call releases them). -/
def clearOutArgs (a : AState) : AState :=
  a.filterMap fun k vs => if isOutArgKey k then none else some vs

/-- Definitions `(v, l)`: forget each `v`, clear the clobbered registers,
then each `l` holds exactly its `v`. -/
def define (a : AState) (defs : List (VReg × Loc)) (clobbers : List Loc) : AState :=
  let a := defs.foldl (fun a (v, _) => a.forget v) a
  let a := clobbers.foldl clear a
  defs.foldl (fun a (v, l) => a.set l [v]) a

/-- The parameters bound by an edge with arguments `args`, in parallel. -/
def bindParams (a : AState) (params args : List VReg) : AState :=
  let pairs := params.zip args
  a.filterMap fun _ vs =>
    let kept := vs.filter fun v => !params.contains v
    let gained := pairs.foldl (fun s (p, x) => if VSet.mem x vs then VSet.insert p s else s) kept
    match gained with
    | [] => none
    | gs => some gs

/-- A state from explicit facts (a certificate). -/
def ofList (facts : List (Loc × List VReg)) : AState :=
  facts.foldl (fun a (l, vs) => a.set l (VSet.ofList (vs ++ a.get l))) empty

/-- The facts of a state, by key. -/
def facts (a : AState) : List (Nat × VSet) := a.toList

end AState

end IxCC.Xv.Validate
