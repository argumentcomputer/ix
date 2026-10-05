import Ix.CompileCert.AnnotReduceEntry

namespace Tests.Ix.CompileCert.AnnotReduceOps
open _root_.Ix.CompileCert _root_.Ix.Kernel

private def aliasName := sourceName `ReductionReceipt.alias
private def theoremName := sourceName `ReductionReceipt.equal
private def missingName := sourceName `ReductionReceipt.absent
private def request : ValueEquationRequest :=
  ⟨theoremName, [], .succ .zero, (reduceOpCvA reduceNatName).type,
    aliasName, [], reduceNatName, []⟩
private def declarations : Array Declaration := #[
  .basisDecl .eqK, .basisDecl .natK,
  .opaqueDecl (reduceOpRaw reduceNatName) (reduceDeclPin reduceNatName),
  .defnDecl ⟨aliasName, [], (reduceOpRaw reduceNatName).type⟩ (.const reduceNatName []) (.regular 0),
  .thmDecl ⟨theoremName, [], request.type⟩
    (Expr.mkAppN (.const eqReflName [.succ .zero]) [(reduceOpCvA reduceNatName).type, .const reduceNatName []])]

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"reduce receipt control failed: {label}")
  IO.println s!"PASS: reduce receipt {label}"

def run : IO Unit := do
  let env ← match checked : Cached.checkDecls .verified [] declarations with
    | .ok env =>
      have _independent : ∀ (V : Type) [inst : SetTheory V], Nonempty (StrongInstalledModel V env) := by
        intro V inst
        exact strongInstalledModel_exists V [] declarations env checked
      pure env
    | .error (error, position) => throw (IO.userError s!"reduce receipt fold failed at {position}: {error}")
  let certificates := fun _ => theoremName
  let missing := fun _ => missingName
  let names := fun name => if name == reduceNatName then aliasName else name
  require "actual pinned opaque is present" (reduceStoredOk env reduceNatName)
  require "identity requires no extra certificate"
    (checkReduceOperationReceipts env env id missing missing == some true)
  require "actual admitted operation alias equation"
    (checkReduceOperationReceipts env env names certificates missing == some true)
  require "missing alias equation refuses"
    (checkReduceOperationReceipts env env names missing missing == some false)
  require "missing canonical operation refuses"
    (checkReduceOperationReceipts env { env with consts := env.consts.filter (fun row => row.name != reduceNatName) }
      names certificates missing == some false)
  require "wrong element map refuses"
    (checkReduceOperationReceipts env env (fun name => if name == natName then aliasName else names name)
      certificates missing == some false)
  IO.println "reduction receipts: 6/6 controls passed"

#eval run
end Tests.Ix.CompileCert.AnnotReduceOps
