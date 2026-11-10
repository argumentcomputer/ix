import IxCC.Xv.Alloc.LinearScan
import IxCC.Xv.Alloc.AllSlots
import IxCC.Xv.Validate.Check

/-!
# Allocation with its checks

`Alloc.run` allocates each function of an Xv program by linear scan,
validates the result, and falls back to all slots (the CakeML
pattern of a checker-gated oracle with a fallback): a linear-scan failure
or a rejection is recorded and the function is allocated again with
`allSlots`, which must itself validate or the program is declined (a
compile error, never wrong code). The Xl program returned is
`Validate.run`'s: exactly the code the validator accepted.
-/

namespace IxCC.Xv.Alloc

/-- What happened to one function. -/
inductive Outcome where
  /-- Linear scan's allocation was accepted. -/
  | scan
  /-- Linear scan failed (a message); all slots was accepted. -/
  | declined (msg : String)
  /-- Linear scan's allocation was rejected (an allocator bug); all slots was
  accepted. -/
  | rejected (err : Validate.Err)
  deriving Inhabited

structure Result where
  program : LProgram
  outs : List Output
  outcomes : List Outcome

/-- The all-slots fallback (`Alloc.allSlots_valid` is stated of it). -/
def allSlots (f : Func Lir.VReg) : Except String Output := AllSlots.run f

/-- Allocate and validate one function, with the fallback. -/
def allocFunc (env : Xl.Env) (fi : Nat) (f : Func Lir.VReg) (chaos : Chaos) :
    Except String (Output × Outcome) := do
  let fallback (why : Outcome) : Except String (Output × Outcome) := do
    let o ← match AllSlots.run f with
      | .ok o => pure o
      | .error e => throw s!"function {fi}: all slots failed: {e}"
    match Validate.func env fi f o with
    | .ok () => pure (o, why)
    | .error e => throw s!"function {fi}: all slots rejected: {e.text}"
  match LinearScan.run env f chaos with
  | .error msg => fallback (.declined msg)
  | .ok o =>
      match Validate.func env fi f o with
      | .ok () => pure (o, .scan)
      | .error e => fallback (.rejected e)

/-- Allocate every function of `p`. -/
def run (env : Xl.Env) (p : VProgram) (chaos : Chaos := {}) : Except String Result := do
  let mut outs := #[]
  let mut outcomes := #[]
  for h : fi in [:p.funcs.size] do
    let (o, why) ← allocFunc env fi p.funcs[fi] chaos
    outs := outs.push o
    outcomes := outcomes.push why
  let program ← Validate.run env p outs.toList
  return { program, outs := outs.toList, outcomes := outcomes.toList }

/-- `run` as the producer calls it: the same allocations, outcomes and
program, without validating every function a second time. `allocFunc`
accepts an allocation only after `Validate.func` accepts it at its index,
and `Validate.run` checks exactly those again before it applies them, so the
program is `applyProgram`'s; `tests-recheck --producer` compares the two.
`run` keeps the closing check, which `Backend.alloc_validated` reads. -/
def runProducer (env : Xl.Env) (p : VProgram) (chaos : Chaos := {}) : Except String Result := do
  let mut outs := #[]
  let mut outcomes := #[]
  for h : fi in [:p.funcs.size] do
    let (o, why) ← allocFunc env fi p.funcs[fi] chaos
    outs := outs.push o
    outcomes := outcomes.push why
  let program ← applyProgram p outs.toList
  return { program, outs := outs.toList, outcomes := outcomes.toList }

/-- All slots for every function, validated. -/
def runAllSlots (env : Xl.Env) (p : VProgram) : Except String Result := do
  let mut outs := #[]
  for h : fi in [:p.funcs.size] do
    let f := p.funcs[fi]
    let o ← match AllSlots.run f with
      | .ok o => pure o
      | .error e => throw s!"function {fi}: all slots failed: {e}"
    outs := outs.push o
  let program ← Validate.run env p outs.toList
  return { program, outs := outs.toList, outcomes := outs.toList.map fun _ => .scan }

end IxCC.Xv.Alloc
