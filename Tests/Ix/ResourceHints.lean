import LSpec
import Ix.Meta
import Ix.CompileDriver
import Ix.EnvScope
import Ix.Resource.Validate
import Ix.Cert.Statement
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.ContractPipeline
import Tests.Ix.SourceContract.SyntaxFixture
import Tests.Ix.Kernel.TierIndDefs

/-! # The resource validator's typing half on compiled closures (`resource-hints`)

* **Hints and coverage.** `Ix.Resource.TypingInput.hint` copies
  `Ix.Cert.hintsOf`'s rule, so that `Ix.Resource` does not import `Ix.Cert`.
  On the compiled closure of the reader-fidelity and Source-ingress fixtures,
  the two give the same hint at every member and constructor of every record,
  through and around its projection record; hints are found both through a
  projection record and at a record itself. The input lists every record
  exactly once (`Ixon.CheckOrder.wholeEnv`).
* **Actual typing verdicts**, on compiled
  closures the typing half accepts: those fixtures (with assumption axioms),
  the source-contract syntax fixture (a contract input), the contract
  pipeline's input (an assumption axiom, `ContractA`) and the typing tier's
  inductive fixtures (unsafe inductives, `kernel-tier-ind`). Each reports the
  size of its uncertified part. -/

namespace Tests.ResourceHints

open LSpec
open _root_.Ix.Kernel (ConstRef)
open Tests.Ix.Kernel.SourceIngress (defsModule ownModule preludeNames)

/-- The constants of `modules` and everything they reach (as `cert-statement`
selects them), with `extra` seeds. -/
def closureOf (leanEnv : Lean.Environment) (modules : Array Lean.Name) (extra : Array Lean.Name := #[]) :
    IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let mut idxs : Array Nat := #[]
  for m in modules do
    let some idx := leanEnv.getModuleIdx? m | throw (IO.userError s!"fixture module {m} not loaded")
    idxs := idxs.push idx.toNat
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    match leanEnv.getModuleIdxFor? n with
    | some m => if idxs.contains m.toNat then some n else none
    | none => none
  IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (seeds ++ extra ++ preludeNames))

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

/-- Size of the initial uncertified split. The typing fallback may expand
this set to include all tier owners; this helper does not observe that path. -/
def uncertifiedSize (ixe : Ixon.Env) : Nat :=
  match Ix.Resource.typingInput ixe with
  | .error _ => 0
  | .ok input =>
    let unc := Ix.Resource.splitOf input
    (input.ordered.filter fun (a, c, _) => unc.contains (Ixon.CheckOrder.owner a c)).size

/-- The typing half must accept the actual compiled `ixe`. -/
def verdict (label : String) (ixe : Ixon.Env) : Array String × Array String :=
  let ixc := Ix.Resource.typeCheck ixe
  let named (e : String) : List String := ixe.named.toList.filterMap fun (n, nd) =>
    if (e.splitOn (toString nd.addr)).length > 1 then some (toString n) else none
  let errors := match ixc with
    | .error e => #[s!"{label}: the typing half declines: {e} (names: {named e})"]
    | .ok _ => #[]
  (errors, #[s!"{label}: {ixe.consts.size} records, {uncertifiedSize ixe} in the initial uncertified split, \
    IxC {if ixc.toOption.isSome then "accepts" else "declines"}"])

def hintsAndCoverage : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule, ownModule]
  let consts ← closureOf leanEnv #[defsModule, ownModule] #[`Nat.div]
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
  let listed := input.ordered.map (·.1)
  let distinct : Std.HashSet Address := listed.foldl (·.insert ·) {}
  unless listed.size == ixe.consts.size && distinct.size == listed.size do
    errors := errors.push s!"typing input lists {listed.size} records ({distinct.size} distinct) \
      of {ixe.consts.size}"
  let (vErrors, vLines) := verdict "reader-fidelity and Source-ingress fixtures" ixe
  let lines := #[s!"resource-hints: {refs.size} references, {viaProjection} hints through a projection \
    record, {atRecord} at a record; {listed.size} records listed"] ++ vLines
  return (errors ++ vErrors, lines)

def compiledVerdicts : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  -- the source-contract syntax fixture: a contract input, in the closure
  -- `compile-lean --local` takes (`collectSelectedDeps`: recursors, logical
  -- units, checker and string-literal support)
  let syntaxModule := `Tests.Ix.SourceContract.SyntaxFixture
  let leanEnv ← getCompileEnv #[syntaxModule]
  let some syntaxIdx := leanEnv.getModuleIdx? syntaxModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
    if leanEnv.getModuleIdxFor? n == some syntaxIdx then some n else none
  match Ix.Compile.compileInputFromEnv leanEnv (Ix.EnvScope.collectSelectedDeps leanEnv seeds) with
  | .error e => errors := errors.push s!"source-contract syntax fixture: input: {e}"
  | .ok input =>
    match ← Ix.CompileM.compileLeanInput input (numWorkers := 4) with
    | .error e => errors := errors.push s!"source-contract syntax fixture: compile: {e}"
    | .ok out =>
      let (es, ls) := verdict "source-contract syntax fixture" out.env
      errors := errors ++ es
      lines := lines ++ ls
  -- the contract pipeline's input: an assumption axiom and a contracted identity
  match Tests.ContractPipeline.input with
  | .error e => errors := errors.push s!"contract pipeline: input: {e}"
  | .ok input =>
    match ← Ix.CompileM.compileLeanInput input (numWorkers := 1) with
    | .error e => errors := errors.push s!"contract pipeline: compile: {e}"
    | .ok out =>
      let (es, ls) := verdict "contract pipeline (ContractA)" out.env
      errors := errors ++ es
      lines := lines ++ ls
  -- the typing tier's inductive fixtures: unsafe inductives
  let tierModule := `Tests.Ix.Kernel.TierIndDefs
  let leanEnv ← getCompileEnv #[tierModule]
  let consts ← closureOf leanEnv #[tierModule]
  match ← Ix.CompileM.compileLeanConsts consts (numWorkers := 4) with
  | .error e => errors := errors.push s!"kernel-tier-ind fixtures: compile: {e}"
  | .ok out =>
    let (es, ls) := verdict "kernel-tier-ind fixtures (unsafe inductives)" out.env
    errors := errors ++ es
    lines := lines ++ ls
  return (errors, lines)

def report (name : String) (action : IO (Array String × Array String)) : TestSeq :=
  .individualIO name none (do
    let (errors, lines) ← action
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate (errors.toList.take 20))
    return (errors.isEmpty, 1, 0, msg)) .done

def suite : List TestSeq := [
  report "the typing input's hints and coverage, and its verdict, on the compiled fixtures" hintsAndCoverage,
  report "actual typing verdicts: a contract input, an assumption axiom, unsafe inductives"
    compiledVerdicts]

end Tests.ResourceHints
