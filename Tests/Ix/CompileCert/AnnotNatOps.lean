import Ix.CompileCert.AnnotStrong

namespace Tests.Ix.CompileCert.AnnotNatOps
open _root_.Ix.CompileCert _root_.Ix.Kernel

private def natType : Expr := .const natName []
private def functionType : Expr := .forallE natType natType ⟨.never⟩
private def predBody : Expr := .lam natType
  (Expr.mkAppN (.const (natName.str "rec") [.succ .zero])
    [.lam natType natType ⟨.never⟩, .const natZeroName [],
     .lam natType (.lam natType (.bvar 1) ⟨.never⟩) ⟨.never⟩, .bvar 0]) ⟨.never⟩
private def aliasName := sourceName `NatReceipt.predAlias
private def theoremName := sourceName `NatReceipt.predEqual
private def missingName := sourceName `NatReceipt.missing
private def request : ValueEquationRequest :=
  ⟨theoremName, [], .succ .zero, functionType, aliasName, [], natPredName, []⟩
private def sourceDecls : Array Declaration := #[.basisDecl .eqK, .basisDecl .natK,
  .defnDecl ⟨natPredName, [], functionType⟩ predBody (.regular 0)]
private def targetDecls : Array Declaration := sourceDecls ++ #[
  .defnDecl ⟨aliasName, [], functionType⟩ (.const natPredName []) (.regular 1),
  .thmDecl ⟨theoremName, [], request.type⟩
    (Expr.mkAppN (.const eqReflName [.succ .zero]) [functionType, .const natPredName []])]
private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"Nat receipt control failed: {label}")
  IO.println s!"PASS: Nat receipt {label}"
private def install (declarations : Array Declaration) : IO Env :=
  match checked : Cached.checkDecls .verified [] declarations with
  | .ok env =>
    have _independent : ∀ (V : Type) [inst : SetTheory V], Nonempty (StrongInstalledModel V env) := by
      intro V inst
      exact strongInstalledModel_exists V [] declarations env checked
    pure env
  | .error (error, position) => throw (IO.userError s!"Nat receipt fold failed at {position}: {error}")

def run : IO Unit := do
  let source ← install sourceDecls
  let target ← install targetDecls
  let names := fun name => if name == natPredName then aliasName else name
  let levels := fun _ => Level.succ .zero
  let certificates := fun _ => theoremName
  let missing := fun _ => missingName
  require "actual canonical pred installed" (match source.find? natPredName with | some (.defnInfo _ _ _) => true | _ => false)
  require "identity without theorem" (checkNatOperationReceipts source source id missing levels == some true)
  require "admitted alias at both recurrence equations" (checkNatOperationReceipts source target names certificates levels == some true)
  require "missing alias theorem refuses" (checkNatOperationReceipts source target names missing levels == some false)
  require "missing canonical target refuses" (checkNatOperationReceipts source
    { target with consts := target.consts.filter (fun row => row.name != natPredName) } names certificates levels == some false)
  require "wrong source map refuses" (checkNatOperationReceipts source target
    (fun name => if name == natPredName then natSuccName else name) certificates levels == some false)
  require "wrong equation universe refuses" (checkNatOperationReceipts source target names certificates (fun _ => .zero) == some false)
  require "nonmonomorphic constant grammar refuses" (!(readCheckedNatEquation source target names certificates levels
    (.const natPredName [.zero])).isSome)
  require "unrelated binder grammar refuses" (!(readCheckedNatEquation source target names certificates levels predBody).isSome)
  require "DivMod canonical definition required" (!(readCheckedDivModOperation source target id missing levels natDivName).isSome)
  IO.println "Nat receipts: 10/10 controls passed"

#eval run
end Tests.Ix.CompileCert.AnnotNatOps
