import Ix.Tc.Check
import Ix.Tc.Verify.Execution
import Ix.Tc.Verify.State
import Lean4Lean.Theory.VEnv

/-!
# Statement skeleton: the headline `.WF` shapes

Sorried statements of the program's target theorems, written against
the Hoare kernel (Verify/Monad.lean). The translation relations are
`opaque` stubs — *stubs with types*: every statement below is a legal
proposition today whose shape changes only at named architecture milestones
as the concrete relations (`TrKExprS`/`TrKExpr` in Verify/Trans.lean, finite
`RunSupport`/`ResourceBounds` in Verify/Support.lean, execution-indexed
`RunAssumptions` in Verify/Execution.lean, and
`KernelTcInv`/`TrustedConstRel` in Verify/State.lean and Verify/Env.lean)
replace the stubs. G4 has now replaced the state-invariant stub itself;
only the judgment-level relations below remain provisional.
Judgment plumbing (universe counts, contexts) deliberately routes through
the stub relations so the shapes don't churn while that plumbing is
designed; the theory anchor is `Lean4Lean`'s `VExpr`/`VConstant`.

Sorry frontier: every theorem in this file (they acquire proofs as the
whnf/infer/checkConst soundness layers land); the stubs themselves are
not sorries.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VConstant)

/-- The headline invariant is now the concrete G4 invariant: some current
trusted world extends the caller's baseline and justifies the loaded catalog,
intern range, and every warm cache entry under one finite run support. -/
def KernelRunInv (semantics : CacheSemantics) (trProj : RawProjRel)
    (world₀ : VerifyWorld) (support : RunSupport)
    (s : TcState .anon) : Prop :=
  KernelTcInv semantics trProj world₀ support s

/-- Expression translation: `KExpr` denotes this theory-level `VExpr` in
    the current state's context (the `TrExprS` analog over `KVLCtx`,
    with owned `prj`/literal cases; concrete form: `TrKExprS`,
    Verify/Trans.lean). -/
opaque StatementTrKExpr :
  {m : Mode} → TcState m → KExpr m → VExpr → Prop

/-- Constant translation: the constant at `id` denotes this theory-level
    `VConstant` (concrete G2b interface: exact loaded/trusted resolution via
    `TrustedConstRel`, Verify/Env.lean). -/
opaque StatementTrKConst :
  {m : Mode} → TcState m → KId m → VConstant → Prop

/-- The state's environment translates to a well-formed `VEnv` extension
    in which `d` is a valid constant (the `NativeOracle` defeqs
    enter as the env's `.extra` judgments). -/
opaque StatementTrustedConst :
  {m : Mode} → TcState m → VConstant → Prop

/-- Theory-level definitional equality of the translations, in the
    current state's environment and context (translation-layer plumbing). -/
opaque StatementKDefEqU :
  {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- Theory-level typing of the translations (translation-layer plumbing). -/
opaque StatementKHasType :
  {m : Mode} → TcState m → VExpr → VExpr → Prop

/-- **`whnf` soundness shape**: reduction preserves the translation
    up to theory-level defeq. -/
theorem TcM.whnf.wf {s : TcState .anon} {e : KExpr .anon} {ve : VExpr}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world₀ : VerifyWorld}
    {support : RunSupport} {requests : List WalkerRequest}
    (hrun : RunAssumptions s (TcM.whnf e) requests support)
    (he : StatementTrKExpr s e ve) :
    TcM.WF (KernelRunInv semantics trProj world₀ support) s (TcM.whnf e)
      (fun e' s' => ∃ ve', StatementTrKExpr s' e' ve' ∧
        StatementKDefEqU s' ve ve') := by
  sorry

/-- **`infer` soundness shape**: the inferred type translates and
    types the subject. -/
theorem TcM.infer.wf {s : TcState .anon} {e : KExpr .anon} {ve : VExpr}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world₀ : VerifyWorld}
    {support : RunSupport} {requests : List WalkerRequest}
    (hrun : RunAssumptions s (TcM.infer e) requests support)
    (he : StatementTrKExpr s e ve) :
    TcM.WF (KernelRunInv semantics trProj world₀ support) s (TcM.infer e)
      (fun ty s' => ∃ vty, StatementTrKExpr s' ty vty ∧
        StatementKHasType s' ve vty) := by
  sorry

/-- **`isDefEq` soundness shape**: a `true` verdict implies
    theory-level definitional equality. (`false` implies nothing —
    incompleteness is not unsoundness.) -/
theorem TcM.isDefEq.wf {s : TcState .anon}
    {a b : KExpr .anon} {va vb : VExpr}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world₀ : VerifyWorld}
    {support : RunSupport} {requests : List WalkerRequest}
    (hrun : RunAssumptions s (TcM.isDefEq a b) requests support)
    (ha : StatementTrKExpr s a va) (hb : StatementTrKExpr s b vb) :
    TcM.WF (KernelRunInv semantics trProj world₀ support) s
      (TcM.isDefEq a b)
      (fun r s' => r = true → StatementKDefEqU s' va vb) := by
  sorry

/-- **`checkConst` soundness shape** (the headline): acceptance means
    the constant translates to a trusted theory-level constant —
    conditional on the concrete execution-indexed finite run assumptions
    (and, inside `StatementTrustedConst`, the `NativeOracle` defeqs and
    upstream Theory debt). -/
theorem TcM.checkConst.wf {s : TcState .anon} {id : KId .anon}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world₀ : VerifyWorld}
    {support : RunSupport} {requests : List WalkerRequest}
    (hrun : RunAssumptions s (TcM.checkConst id) requests support) :
    TcM.WF (KernelRunInv semantics trProj world₀ support) s
      (TcM.checkConst id)
      (fun _ s' => ∃ d, StatementTrKConst s' id d ∧
        StatementTrustedConst s' d) := by
  sorry

end Ix.Tc
