import Ix.Meta
import Ix.CompileDriver
import Ix.KernelCheck
import Ix.AuxGen.IxcScope
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.Kernel.AccelSemanticsDefs

/-! Semantic inputs retained from Tc.AccelDiff, without its deleted backend
switch or internal term addresses. Rust and IxC check the complete selected
closure, including Lean-checked value/head witnesses and Nat.decLe itself.
Actual IxC queries additionally inspect the four weak-head results. -/

namespace Tests.Ix.Kernel.AccelSemantics

private def fixture (s : String) : Lean.Name := `Tests.Ix.Kernel.AccelSemanticsDefs ++ s.toName
private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)

/-- Bind the tests to the original applications, including each literal. -/
private def inputShapes (env : Lean.Environment) : IO Unit := do
  let lit (n : Nat) : Lean.Expr := .lit (.natVal n)
  let call (n : Lean.Name) (args : Array Lean.Expr) := Lean.mkAppN (Lean.mkConst n) args
  let bv n := call ``BitVec.ofNat #[lit 8, lit n]
  let expected := #[
    ("bitNat", call ``BitVec.toNat #[lit 8, bv 5]),
    ("bitUlt", call ``BitVec.ult #[lit 8, bv 3, bv 7]),
    ("natLe", call ``Nat.decLe #[lit 3, lit 5]),
    ("natEq", call ``Nat.decEq #[lit 4, lit 6])]
  for (label, body) in expected do
    let some (.defnInfo info) := env.find? (fixture label)
      | throw (IO.userError s!"missing actual application: {label}")
    need (info.value == body) s!"original application changed: {label}: {info.value}"

def run : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Kernel.AccelSemanticsDefs]
  inputShapes leanEnv
  let roots := #[fixture "bitNat", fixture "bitUlt", fixture "natLe", fixture "natEq",
    fixture "bitNat_value", fixture "bitUlt_value", fixture "natLe_head", fixture "natEq_head", ``Nat.decLe]
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv
    (roots ++ Tests.Ix.Kernel.SourceIngress.preludeNames))
  let names := (closed.map (·.1)).toArray
  need (!closed.isEmpty && roots.all names.contains) "selected semantic closure lost a root"
  let compiled ← IO.ofExcept (← Ix.CompileM.compileLeanConsts closed (numWorkers := 4))
  need (compiled.ungroundedCount == 0) "semantic closure has ungrounded inputs"
  let rust ← Ix.KernelCheck.rsCheckConstsFFI closed names (Array.replicate names.size true) true
  need (rust.size == names.size) "Rust omitted selected closure verdicts"
  for i in [:names.size] do
    if let some error := rust[i]! then
      throw (IO.userError s!"Rust rejected {names[i]!}: {error.message}")
  let checked ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts compiled.env
  for name in names do
    let key := Ix.LeanIngress.ingressKey (Ix.Name.fromLeanName name)
    let some (outcome, reason) := checked[key]?
      | throw (IO.userError s!"IxC omitted {name}")
    need (outcome == "accept") s!"IxC did not accept {name}: {outcome}: {reason}"
  let source ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv roots
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError toString)
  let sourceRoots := roots.map Ix.Name.fromLeanName
  let service := (Ix.AuxGen.Source.Service.create pre source
    (Tests.Ix.Kernel.SourceIngressStep.condense source)
    (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames sourceRoots
  need ((Ix.AuxGen.Ixc.blockStatus? service sourceRoots).isNone)
    s!"Source semantic roots were not accepted: {Ix.AuxGen.Ixc.blockStatus? service sourceRoots}"
  let scope ← IO.ofExcept (Ix.AuxGen.Ixc.Scope.new service.env #[])
  let query (s : String) := Ix.Expr.mkConst (Ix.Name.fromLeanName (fixture s)) #[]
  let (nat, _) ← IO.ofExcept (scope.whnfExpr (query "bitNat"))
  need (Ix.Compile.ExactKey.exprEq nat (Ix.Expr.mkLit (.natVal 5))) "BitVec.toNat 8/5 did not produce 5"
  for (label, head) in [("bitUlt", ``Bool.true), ("natLe", ``Decidable.isTrue),
      ("natEq", ``Decidable.isFalse)] do
    let (result, _) ← IO.ofExcept (scope.whnfExpr (query label))
    let .const actual _ _ := (Ix.AuxGen.decomposeApps result).1
      | throw (IO.userError s!"{label}: result has no constructor head")
    need (Ix.Compile.ExactKey.nameEq actual (Ix.Name.fromLeanName head)) s!"{label}: wrong head {actual}"
    IO.println s!"retained acceleration {label}: {head}"
  IO.println s!"retained acceleration: all four exact inputs, real WHNF results and Nat.decLe admission; {names.size} complete Rust/IxC closure verdicts"
  return 0

end Tests.Ix.Kernel.AccelSemantics
