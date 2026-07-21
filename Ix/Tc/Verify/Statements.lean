import Ix.Tc.Check
import Ix.Tc.Verify.Monad
import Lean4Lean.Theory.VEnv

/-!
# M1 statement skeleton: the headline `.WF` shapes

Sorried statements of the program's target theorems (plans/
tc-verify-roadmap.md), written against the A6 Hoare kernel. The
translation relations are `opaque` stubs — *stubs with types* (roadmap
posture rule 2): every statement below is a legal proposition today whose
text never changes as M2 (`TrKExpr`, `CollisionFree`) and M3
(`KernelInv`, env translation) replace the stubs with definitions.
Judgment plumbing (universe counts, contexts) deliberately routes through
the stub relations so the shapes don't churn while that plumbing is
designed; the theory anchor is `Lean4Lean`'s `VExpr`/`VConstant`.

Sorry frontier: every theorem in this file (they acquire proofs in
M5-M7); the stubs themselves are not sorries.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VConstant)

variable {m : Mode}

/-- The run-wide kernel state invariant (M3: the ghost `VState` view —
    cache soundness, env translation, intern support). -/
opaque KernelInv : {m : Mode} → TcState m → Prop

/-- No Blake3 collisions among this run's interned terms (M2: `Set.InjOn`
    over the intern-table range, up to anon erasure). -/
opaque CollisionFree : {m : Mode} → TcState m → Prop

/-- Expression translation: `KExpr` denotes this theory-level `VExpr` in
    the current state's context (M2: the `TrExprS` analog over `KVLCtx`,
    with owned `prj`/literal cases). -/
opaque TrKExpr : {m : Mode} → TcState m → KExpr m → VExpr → Prop

/-- Constant translation: the constant at `id` denotes this theory-level
    `VConstant` (M3: the `TrConstant` analog over `KEnv`). -/
opaque TrKConst : {m : Mode} → TcState m → KId m → VConstant → Prop

/-- The state's environment translates to a well-formed `VEnv` extension
    in which `d` is a valid constant (M3/M7; the `NativeOracle` defeqs
    enter as the env's `.extra` judgments). -/
opaque TrustedConst : {m : Mode} → TcState m → VConstant → Prop

/-- Theory-level definitional equality of the translations, in the
    current state's environment and context (M2/M3 plumbing). -/
opaque KDefEqU : {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- Theory-level typing of the translations (M2/M3 plumbing). -/
opaque KHasType : {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- **`whnf` soundness shape** (M5): reduction preserves the translation
    up to theory-level defeq. -/
theorem TcM.whnf.wf {s : TcState m} {e : KExpr m} {ve : VExpr}
    (hcf : CollisionFree s) (he : TrKExpr s e ve) :
    TcM.WF KernelInv s (TcM.whnf e)
      (fun e' s' => ∃ ve', TrKExpr s' e' ve' ∧ KDefEqU s' ve ve') := by
  sorry

/-- **`infer` soundness shape** (M6): the inferred type translates and
    types the subject. -/
theorem TcM.infer.wf {s : TcState m} {e : KExpr m} {ve : VExpr}
    (hcf : CollisionFree s) (he : TrKExpr s e ve) :
    TcM.WF KernelInv s (TcM.infer e)
      (fun ty s' => ∃ vty, TrKExpr s' ty vty ∧ KHasType s' ve vty) := by
  sorry

/-- **`isDefEq` soundness shape** (M6): a `true` verdict implies
    theory-level definitional equality. (`false` implies nothing —
    incompleteness is not unsoundness.) -/
theorem TcM.isDefEq.wf {s : TcState m} {a b : KExpr m} {va vb : VExpr}
    (hcf : CollisionFree s) (ha : TrKExpr s a va) (hb : TrKExpr s b vb) :
    TcM.WF KernelInv s (TcM.isDefEq a b)
      (fun r s' => r = true → KDefEqU s' va vb) := by
  sorry

/-- **`checkConst` soundness shape** (M7, the headline): acceptance means
    the constant translates to a trusted theory-level constant —
    conditional on `CollisionFree` (and, inside `TrustedConst`, the
    `NativeOracle` defeqs and upstream Theory debt). -/
theorem TcM.checkConst.wf {s : TcState m} {id : KId m}
    (hcf : CollisionFree s) :
    TcM.WF KernelInv s (TcM.checkConst id)
      (fun _ s' => ∃ d, TrKConst s' id d ∧ TrustedConst s' d) := by
  sorry

end Ix.Tc
