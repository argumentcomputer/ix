import Ix.Meta
import Ix.CompileDriver
import Ix.KernelCheck
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.Kernel.AccelSemanticsDefs

/-! Semantic inputs retained from Tc.AccelDiff, without its deleted backend
switch or internal term addresses. Rust and IxC check the complete selected
closure, including Lean-checked value/head witnesses (each a `rfl` the
checkers reduce) and Nat.decLe itself. -/

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
  IO.println s!"retained acceleration: all four exact inputs, their value/head witnesses and Nat.decLe admission; {names.size} complete Rust/IxC closure verdicts"
  return 0

end Tests.Ix.Kernel.AccelSemantics
