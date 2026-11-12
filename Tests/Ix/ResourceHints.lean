import LSpec
import Ix.Meta
import Ix.CompileCertified
import Ix.Resource.Validate
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.ContractPipeline
import Tests.Ix.Kernel.TierIndDefs

/-! # The resource validator's typing half on compiled closures (`resource-hints`)

Actual typing verdicts (`Ix.Resource.typeCheck`) on compiled closures the typing
half accepts: the reader-fidelity and Source-ingress fixtures (with assumption
axioms), the contract pipeline's input (an assumption axiom, `ContractA`, and an
identity under the ordinary contract) and the typing tier's
inductive fixtures (unsafe inductives, `kernel-tier-ind`). Each reports the
size of its uncertified part. -/

namespace Tests.ResourceHints

open LSpec
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

def fixtureVerdict : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule, ownModule]
  let consts ← closureOf leanEnv #[defsModule, ownModule] #[`Nat.div]
  let out ← match ← Ix.CompileM.compileCertified leanEnv consts 4 with
    | .ok out => pure out
    | .error e => return (#[s!"compileCertified failed: {e}"], #[])
  return verdict "reader-fidelity and Source-ingress fixtures" out.env

def compiledVerdicts : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  -- the contract pipeline's input: an assumption axiom and an identity under the
  -- ordinary contract
  match Tests.ContractPipeline.input .many .shared .shared with
  | .error e => errors := errors.push s!"contract pipeline: input: {e}"
  | .ok input =>
    match ← Tests.ContractPipeline.compileInput input with
    | .error e => errors := errors.push s!"contract pipeline: compile: {e}"
    | .ok out =>
      let (es, ls) := verdict "contract pipeline (ContractA)" out.env
      errors := errors ++ es
      lines := lines ++ ls
  -- the typing tier's inductive fixtures: unsafe inductives
  let tierModule := `Tests.Ix.Kernel.TierIndDefs
  let leanEnv ← getCompileEnv #[tierModule]
  let consts ← closureOf leanEnv #[tierModule]
  match ← Ix.CompileM.compileCertified leanEnv consts 4 with
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
  report "the typing half's verdict on the compiled fixtures" fixtureVerdict,
  report "actual typing verdicts: an ordinary contract input, an assumption axiom, unsafe inductives"
    compiledVerdicts]

end Tests.ResourceHints
