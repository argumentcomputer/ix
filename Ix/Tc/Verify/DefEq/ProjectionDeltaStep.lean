import Ix.Tc.Verify.DefEq.DeltaClassification
import Ix.Tc.Verify.DefEq.ProjectionReduction

/-!
# Projection-directed delta step

The inner projection loop uses a compact legacy delta step distinct from the
main DefEq lazy-delta iteration.  Its first two effects are declaration
lookups that classify the operand heads.  This module isolates those lookups
from the remaining rank/unfold/reduction branches and proves their complete
success, absence, and partial-error behavior through the installed anonymous
lazy-ingress contract.
-/

namespace Ix.Tc

namespace RecM

/-- Exact continuation contract once at least one projection-step operand is
known to have a delta-reducible head. -/
def LazyDeltaReductionAfterActive.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right aHead bHead
      aDelta bDelta},
    (!aDelta && !bDelta) = false →
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepAfterActive left right
        aHead bHead aDelta bDelta)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result)

/-- Exact continuation contract after both projection-step head classifiers
have run. -/
def LazyDeltaReductionAfterClassification.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right aHead bHead
      aDelta bDelta},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepAfterClassification left right
        aHead bHead aDelta bDelta)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result)

/-- The joint-negative classifier result is exactly the `.unknown` exit and
preserves the current pair invariant.  Every active flag combination is
delegated with the concrete guard equation. -/
theorem lazyDeltaReductionStepAfterClassification_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : Lean4Lean.VExpr}
    {left right : KExpr .anon} {aHead bHead : Option (KId .anon)}
    {aDelta bDelta : Bool}
    (hactive : LazyDeltaReductionAfterActive.WFAt layer semantics trProj
      world support uvars)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStepAfterClassification left right
        aHead bHead aDelta bDelta)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  unfold lazyDeltaReductionStepAfterClassification
  cases hnone : (!aDelta && !bDelta) with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ => hpair
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact hactive hnone hpair

namespace LazyDeltaReductionAfterClassification

/-- Package the exact inactive/active split as the post-classification
contract. -/
theorem ofActive
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hactive : LazyDeltaReductionAfterActive.WFAt layer semantics trProj
      world support uvars) :
    LazyDeltaReductionAfterClassification.WFAt layer semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource left right aHead bHead aDelta
    bDelta hpair
  exact lazyDeltaReductionStepAfterClassification_wf hactive hpair

end LazyDeltaReductionAfterClassification

/-- Both production classifier lookups preserve the recursive invariant and
delegate their exact results to the post-classification continuation. -/
theorem lazyDeltaReductionStep_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : Lean4Lean.VExpr}
    {left right : KExpr .anon}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hafter : LazyDeltaReductionAfterClassification.WFAt .noAccel semantics
      trProj world support uvars)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (lazyDeltaReductionStep left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  unfold lazyDeltaReductionStep
  apply RecM.WF.bind (classifyDeltaHead_wf ingress.preserves left)
  intro leftDelta afterLeft _
  apply RecM.WF.bind (classifyDeltaHead_wf ingress.preserves right)
  intro rightDelta afterRight _
  exact hafter hpair

namespace LazyDeltaReductionStep

/-- Package the concrete head-classification prefix as the lower step
contract consumed by the bounded projection driver. -/
theorem ofClassification
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hafter : LazyDeltaReductionAfterClassification.WFAt .noAccel semantics
      trProj world support uvars) :
    LazyDeltaReductionStep.WFAt .noAccel semantics trProj world support
      uvars := by
  intro Delta state leftSource rightSource left right hpair
  exact lazyDeltaReductionStep_wf ingress hafter hpair

/-- Assemble the classifier prefix and its exact inactive/active split. -/
theorem ofActive
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hactive : LazyDeltaReductionAfterActive.WFAt .noAccel semantics trProj
      world support uvars) :
    LazyDeltaReductionStep.WFAt .noAccel semantics trProj world support
      uvars :=
  ofClassification ingress
    (LazyDeltaReductionAfterClassification.ofActive hactive)

end LazyDeltaReductionStep

end RecM

end Ix.Tc
