import Ix.CompileCert.Bridge.Lane
import Ix.CanonM

/-!
# M7 X2: the bridge as an export (the executable round trip)

The translation lemmas (`bridge_eq_lane`, `bridge_eq_with`) say that the bridge of a compiler term
is the lane's export of the `Lean.Expr` that term decompiles to (`ixExprE`). What they leave to
evidence is the compiler's own `Lean → Ix` conversion (`Ix.CanonM.canonExpr`, pointer-memoised, so
executable only): that `ixExprE (canonExpr e)` is `e` up to metadata. `bridgeExport` runs the
lane's `directExport` with every term routed through `canonExpr` and the bridge; the test runner
`bridge-roundtrip` compares it with `directExport` and with the certified reader's entries on the
compiled fixtures, and `bridgeSource` with `exportSourceExpr` on every Init+Std constant.
`bridgeSource_eq` is the proved half of the latter comparison.
-/

namespace Ix.CompileCert.Bridge

/-- The compiler's `Lean → Ix` conversion, run on its own (fresh tables). -/
def canonOf (e : Lean.Expr) : Ix.Expr := (Ix.CanonM.canonExpr e).run' {}

/-- The bridge at the lane's naming, as an export step. -/
def bridgeLane (tc : TermContext) (e : Ix.Expr) : ExportM Kernel.Expr :=
  match bridge (laneN tc.context) (laneL tc) e with
  | some k => .ok k
  | none => .error "bridge: unsupported term"

theorem bridgeLane_eq (tc : TermContext) (e : Ix.Expr) :
    (bridgeLane tc e).toOption = (ixToKernelE tc e).toOption := by
  rw [← bridge_eq_lane]; unfold bridgeLane; split <;> simp_all [Except.toOption]

/-- The lane's `directExport`, every term through `canon` and the bridge. -/
def bridgeExport (cx : ExportContext) (canon : Lean.Expr → Ix.Expr) (ci : Lean.ConstantInfo) :
    ExportM DirectEntry := do
  unless sourceSupported ci do throw s!"unsupported source safety: {ci.name}"
  unless ci.levelParams.eraseDups.length == ci.levelParams.length do
    throw s!"duplicate source universe parameters: {ci.name}"
  let levels ← cx.levels ci
  let tc : TermContext := ⟨cx, ci.levelParams, levels⟩
  let val : Kernel.ConstantVal := ⟨← cx.name ci.name, levels, ← bridgeLane tc (canon ci.type)⟩
  match ci with
  | .axiomInfo _ => return .axiom val
  | .defnInfo v => return .defn val (← bridgeLane tc (canon v.value)) (exportHint v.hints)
  | .thmInfo v => return .thm val (← bridgeLane tc (canon v.value))
  | .opaqueInfo v => return .opaque val (← bridgeLane tc (canon v.value))
  | .quotInfo v => return .quot (exportQuot v.kind) val
  | .inductInfo v => return .induct val v.numParams
  | .ctorInfo v => return .ctor val v.numParams v.numFields
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do
      return Kernel.RecRule.mk (← cx.name r.ctor) r.nfields 0 .inert
        (← bridgeLane tc (canon r.rhs)) false false false
    return .recursor val (v.numParams + v.numMotives + v.numMinors + v.numIndices)
      (v.numParams + v.numMotives + v.numMinors) rules

/-- The bridge at the source naming: original names, the declaration's own positional levels. -/
def bridgeSource (params : List Lean.Name) (e : Ix.Expr) : Option Kernel.Expr :=
  bridge (fun n => some (sourceName (ixName n))) (fun u => (ixLevel u >>= exportSourceLevel params).toOption) e

/-- At the source naming the bridge is the lane's source export of the decompiled term. -/
theorem bridgeSource_eq (params : List Lean.Name) (e : Ix.Expr) :
    bridgeSource params e = (ixExprE e >>= exportSourceExpr params).toOption :=
  bridge_eq_with (exportSourceLevel params) (fun n => .ok (sourceName n)) e

end Ix.CompileCert.Bridge
