import Ix.Cert.CompileCorrect
import Ix.KernelFidelity.Reader
import Ix.Compile.SourceContract.Transport
import Tests.Ix.Kernel.SourceIngressStep

/-! # `CompileCorrect.checked`'s premises, executed (part of `cert-statement`)

`Ix.Cert.CompileCorrect.checked` concludes from executed checks only:
* the default role table reads (`Ix.Kernel.Reader.defaultTable = .ok t`);
* the role table's certificate check passes (`Ix.Cert.RoleClosure.roleEvidenceCheck`);
* the compile with its artifact checks passes (`Ix.Cert.compileChecked t env`);
* no constant of the computed closure (`Ix.Cert.closure env roots`) failed in its report;
* quotient Source accepts that closure at the artifact
  (`Ix.LeanIngress.checkSourceCollapsedBundledAt`).

`checkedCase` runs each premise, as the theorem states it, on the closures of
`Nat.add` and of `List.length`, and requires every one to hold: the theorem
applies to real closures, not only to none.

`evidenceRefusals` gives the evidence check, one of the artifact checks, crafted
inputs it must refuse (the other two have planted cases in `cert-statement`). -/

namespace Tests.Ix.Cert.ExecutedChecks

/-- The roots whose closures the premises are run on. -/
def roots : List Lean.Name := [``Nat.add, ``List.length]

/-- `CompileCorrect.checked`'s premises other than the certificate check, on
the closure of `root` (`env` is the prepared, canonicalized closure of `root`,
`roots` is `[root]`): errors, and lines for the report. -/
def premisesAt (leanEnv : Lean.Environment) (root : Lean.Name) :
    IO (Array String × Array String) := do
  let t0 ← IO.monoMsNow
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[root])
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let sub := Ix.Cert.closure env [Ix.Name.fromLeanName root]
  let .ok t := Ix.Kernel.Reader.defaultTable
    | return (#[s!"{root}: the default role table does not read"], #[])
  match Ix.Cert.compileChecked t env with
  | .error e => return (#[s!"{root}: compileChecked refuses the closure: {e}"], #[])
  | .ok (ixe, failures) =>
    unless (sub.consts.keys.all fun n => !failures.failed n) do
      return (#[s!"{root}: a constant of the closure failed in the compile's report"], #[])
    match Ix.LeanIngress.checkSourceCollapsedBundledAt ixe t sub (Ix.Cert.blocksOf sub) with
    | .error e =>
      return (#[s!"{root}: quotient Source refuses the closure at the artifact: {e}"], #[])
    | .ok envQ =>
      return (#[], #[s!"{root}: closure of {sub.consts.size} constants; the default table \
        reads; compileChecked passes ({ixe.consts.size} records); no constant of the closure \
        failed; quotient Source accepts it at the artifact ({envQ.consts.length} kernel \
        constants) ({(← IO.monoMsNow) - t0} ms)"])

/-- Every premise of `CompileCorrect.checked`, on the closure of each of `roots`. -/
def checkedCase (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  if Ix.Cert.RoleClosure.roleEvidenceCheck then
    lines := lines.push "roleEvidenceCheck passes"
  else
    errors := errors.push "roleEvidenceCheck fails"
  for root in roots do
    let (e, l) ← premisesAt leanEnv root
    errors := errors ++ e
    lines := lines ++ l
  return (errors, lines)

/-- **The evidence check refuses crafted inputs** (`Ix.Cert.EvidenceCheck.evidenceCheck`,
one of the artifact checks `compileChecked` runs). On the compiled closure of
`List.length`, which it accepts, it refuses:
* the artifact against a role table with one role's address replaced by
  another role's (the table it is compiled under must be the admitted
  default table);
* the artifact with a fallback record of the prelude replaced, at its address,
  by another record's bytes (a fallback record the artifact holds, it must
  hold identically). -/
def evidenceRefusals (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[``List.length])
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let .ok t := Ix.Kernel.Reader.defaultTable
    | return (#["evidence refusals: the default role table does not read"], #[])
  let .ok (ixe, _) := Ix.Cert.compileChecked t env
    | return (#["evidence refusals: compileChecked refuses the closure of List.length"], #[])
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  match Ix.Cert.EvidenceCheck.evidenceCheck t ixe with
  | .ok () => lines := lines.push s!"evidence check: passes on the compiled closure of List.length \
      ({ixe.consts.size} records)"
  | .error e => errors := errors.push s!"evidence check: refuses the compiled closure of List.length: {e}"
  -- the table with its first role bound at another role's address
  match t.bound[0]? with
  | some (r, a0) =>
    let other := ((t.bound.toList.find? (·.2 != a0)).map (·.2)).getD a0
    let t' := { t with bound := t.bound.set! 0 (r, other) }
    match Ix.Cert.EvidenceCheck.evidenceCheck t' ixe with
    | .ok () => errors := errors.push s!"evidence check: accepts a table with {repr r} at another \
        role's address"
    | .error _ => lines := lines.push s!"evidence check: refuses a table with {repr r} at another \
        role's address"
  | none => errors := errors.push "evidence check: the default table binds no role"
  -- a fallback record of the prelude replaced, at its address, by another record's bytes
  let .ok (pre : Ix.Kernel.Reader.Prelude .anon) := Ix.Kernel.Reader.preludeFor t
    | return (errors.push "evidence check: the committed prelude does not read", lines)
  match pre.records[0]? with
  | none => errors := errors.push "evidence check: the prelude has no fallback record to replace"
  | some (a, c) =>
    match ixe.consts.toList.find? fun (_, lc) => lc.get? != some c with
    | none => errors := errors.push "evidence check: no record differs from the prelude's first"
    | some (_, other) =>
      let planted := { ixe with consts := ixe.consts.insert a other }
      match Ix.Cert.EvidenceCheck.evidenceCheck t planted with
      | .ok () => errors := errors.push s!"evidence check: accepts another record's bytes at the \
          fallback record {a}"
      | .error _ => lines := lines.push s!"evidence check: refuses another record's bytes at the \
          fallback record {a}"
  return (errors, lines)

end Tests.Ix.Cert.ExecutedChecks
