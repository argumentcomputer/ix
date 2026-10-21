import LSpec
import Ix.Meta
import Ix.CompileDriver
import Ix.Resource.Validate
import Ix.Cert.Statement
import Tests.Ix.Kernel.SourceIngress

/-! # The resource validator's typing input on a compiled closure (`resource-hints`)

`Ix.Resource.TypingInput.hint` copies `Ix.Cert.hintsOf`'s rule, so that
`Ix.Resource` does not import `Ix.Cert`. On the compiled closure of the
reader-fidelity and Source-ingress fixtures, the two give the same hint at
every member and constructor of every record, through and around its
projection record. The check is not vacuous: hints are found both through a
projection record and at a record itself.

The same input submits every record of the environment exactly once
(`Ixon.CheckOrder.wholeEnv`), and the typing half accepts the closure. -/

namespace Tests.ResourceHints

open LSpec
open _root_.Ix.Kernel (ConstRef)
open Tests.Ix.Kernel.SourceIngress (defsModule ownModule preludeNames)

/-- The fixture modules' constants and everything they reach (as
`cert-statement` selects them). -/
def fixtureConsts (leanEnv : Lean.Environment) : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let some idx' := leanEnv.getModuleIdx? ownModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    let m := leanEnv.getModuleIdxFor? n
    if m == some idx || m == some idx' then some n else none
  IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (seeds ++ #[`Nat.div] ++ preludeNames))

/-- Every reference a record of `ixe` denotes or holds: a singleton's member
0, a block's members and constructors, a projection's member. -/
def refsOf (ixe : Ixon.Env) : Array (ConstRef Address) := Id.run do
  let mut out : Array (ConstRef Address) := #[]
  for (a, lc) in ixe.consts.toList do
    let some c := lc.get? | continue
    match c.info with
    | .muts ms =>
      for (m, i) in ms.zipIdx do
        out := out.push (.member a i)
        if let .indc ind := m then
          for j in [0:ind.ctors.size] do out := out.push (.ctor a i j)
    | .dPrj p => out := out.push (.member p.block p.idx.toNat)
    | .iPrj p => out := out.push (.member p.block p.idx.toNat)
    | .rPrj p => out := out.push (.member p.block p.idx.toNat)
    | .cPrj p => out := out.push (.ctor p.block p.idx.toNat p.cidx.toNat)
    | _ => out := out.push (.member a 0)
  return out

/-- A reference, for messages. -/
def spell : ConstRef Address → String
  | .member b i => s!"{b} member {i}"
  | .ctor b i c => s!"{b} member {i} constructor {c}"

def agreement : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule, ownModule]
  let consts ← fixtureConsts leanEnv
  let out ← match ← Ix.CompileM.compileLeanConsts consts (numWorkers := 4) with
    | .ok out => pure out
    | .error e => return (#[s!"compileLeanConsts failed: {e}"], #[])
  let ixe := out.env
  let input ← match Ix.Resource.typingInput ixe with
    | .ok input => pure input
    | .error e => return (#[s!"typingInput failed: {e}"], #[])
  let mut errors : Array String := #[]
  let mut viaProjection := 0
  let mut atRecord := 0
  let refs := refsOf ixe
  for r in refs do
    let mine := input.hint r
    let theirs := Ix.Cert.hintsOf ixe r
    unless mine == theirs do
      errors := errors.push s!"hint at {spell r}: resource {repr mine}, Ix.Cert {repr theirs}"
    if mine.isSome then
      if input.projections.contains r then viaProjection := viaProjection + 1
      else atRecord := atRecord + 1
  if viaProjection == 0 then errors := errors.push "no hint found through a projection record"
  if atRecord == 0 then errors := errors.push "no hint found at a record"
  -- coverage: every record once, in the submitted order
  let submitted := input.records.map (·.1)
  let distinct : Std.HashSet Address := submitted.foldl (·.insert ·) {}
  unless submitted.length == ixe.consts.size && distinct.size == submitted.length do
    errors := errors.push s!"typing input submits {submitted.length} records ({distinct.size} distinct) \
      of {ixe.consts.size}"
  if let .error e := Ix.Resource.typeCheck ixe then
    errors := errors.push s!"the typing half declines the fixture closure: {e}"
  let lines := #[s!"resource-hints: {refs.size} references, {viaProjection} hints through a projection \
    record, {atRecord} at a record; {submitted.length} records submitted"]
  return (errors, lines)

def suite : List TestSeq := [
  .individualIO "the typing input's hints, coverage and verdict on the compiled fixtures" none (do
    let (errors, lines) ← agreement
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate (errors.toList.take 20))
    return (errors.isEmpty, 1, 0, msg)) .done]

end Tests.ResourceHints
