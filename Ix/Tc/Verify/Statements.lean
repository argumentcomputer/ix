import Ix.Tc.Check
import Ix.Tc.Verify.Monad
import Lean4Lean.Theory.VEnv

/-!
# Statement skeleton: the headline `.WF` shapes

Sorried statements of the program's target theorems, written against
the Hoare kernel (Verify/Monad.lean). The translation relations are
`opaque` stubs — *stubs with types*: every statement below is a legal
proposition today whose
text never changes as the concrete relations (`TrKExprS`/`TrKExpr` in
Verify/Trans.lean, `CollisionFree` in Verify/Expr.lean, `TcInv`/`TrKEnv`
in Verify/State.lean and Verify/Env.lean) replace the stubs.
Judgment plumbing (universe counts, contexts) deliberately routes through
the stub relations so the shapes don't churn while that plumbing is
designed; the theory anchor is `Lean4Lean`'s `VExpr`/`VConstant`.

Sorry frontier: every theorem in this file (they acquire proofs as the
whnf/infer/checkConst soundness layers land); the stubs themselves are
not sorries.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VConstant)

variable {m : Mode}

/-- The run-wide kernel state invariant (the ghost `VState` view —
    cache soundness, env translation, intern support; concrete form:
    `TcInv`, Verify/State.lean). -/
opaque KernelInv : {m : Mode} → TcState m → Prop

/-- No Blake3 collisions among this run's interned terms (`Set.InjOn`
    over the intern-table range, up to anon erasure; concrete form:
    `CollisionFreeOn`, Verify/Expr.lean). -/
opaque CollisionFree : {m : Mode} → TcState m → Prop

/-- Expression translation: `KExpr` denotes this theory-level `VExpr` in
    the current state's context (the `TrExprS` analog over `KVLCtx`,
    with owned `prj`/literal cases; concrete form: `TrKExprS`,
    Verify/Trans.lean). -/
opaque TrKExpr : {m : Mode} → TcState m → KExpr m → VExpr → Prop

/-- Constant translation: the constant at `id` denotes this theory-level
    `VConstant` (the `TrConstant` analog over `KEnv`; Verify/Env.lean). -/
opaque TrKConst : {m : Mode} → TcState m → KId m → VConstant → Prop

/-- The state's environment translates to a well-formed `VEnv` extension
    in which `d` is a valid constant (the `NativeOracle` defeqs
    enter as the env's `.extra` judgments). -/
opaque TrustedConst : {m : Mode} → TcState m → VConstant → Prop

/-- Theory-level definitional equality of the translations, in the
    current state's environment and context (translation-layer plumbing). -/
opaque KDefEqU : {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- Theory-level typing of the translations (translation-layer plumbing). -/
opaque KHasType : {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- **`whnf` soundness shape**: reduction preserves the translation
    up to theory-level defeq. -/
theorem TcM.whnf.wf {s : TcState m} {e : KExpr m} {ve : VExpr}
    (hcf : CollisionFree s) (he : TrKExpr s e ve) :
    TcM.WF KernelInv s (TcM.whnf e)
      (fun e' s' => ∃ ve', TrKExpr s' e' ve' ∧ KDefEqU s' ve ve') := by
  sorry

/-- **`infer` soundness shape**: the inferred type translates and
    types the subject. -/
theorem TcM.infer.wf {s : TcState m} {e : KExpr m} {ve : VExpr}
    (hcf : CollisionFree s) (he : TrKExpr s e ve) :
    TcM.WF KernelInv s (TcM.infer e)
      (fun ty s' => ∃ vty, TrKExpr s' ty vty ∧ KHasType s' ve vty) := by
  sorry

/-- **`isDefEq` soundness shape**: a `true` verdict implies
    theory-level definitional equality. (`false` implies nothing —
    incompleteness is not unsoundness.) -/
theorem TcM.isDefEq.wf {s : TcState m} {a b : KExpr m} {va vb : VExpr}
    (hcf : CollisionFree s) (ha : TrKExpr s a va) (hb : TrKExpr s b vb) :
    TcM.WF KernelInv s (TcM.isDefEq a b)
      (fun r s' => r = true → KDefEqU s' va vb) := by
  sorry

/-- **`checkConst` soundness shape** (the headline): acceptance means
    the constant translates to a trusted theory-level constant —
    conditional on `CollisionFree` (and, inside `TrustedConst`, the
    `NativeOracle` defeqs and upstream Theory debt). -/
theorem TcM.checkConst.wf {s : TcState m} {id : KId m}
    (hcf : CollisionFree s) :
    TcM.WF KernelInv s (TcM.checkConst id)
      (fun _ s' => ∃ d, TrKConst s' id d ∧ TrustedConst s' d) := by
  sorry

end Ix.Tc
