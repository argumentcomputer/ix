import Ix.Tc.Verify.DefEq.AcceleratorGates
import Ix.Tc.Verify.Whnf.Runtime.LazyIngress

/-!
# Lazy-delta head classification

Delta classification performs up to two declaration lookups, so its primary
obligation is preservation across the installed lazy-ingress hook.  The
classifier result only selects which already-sound reduction is attempted;
no semantic claim is attached to a negative answer.  This module also closes
the exact stopped branch where neither head is classified as reducible.
-/

namespace Ix.Tc

namespace RecM

/-- Exact remaining one-step contract after the classifier establishes that
at least one operand has a delta-reducible head. -/
def DefEqLazyDeltaAfterDeltaClassification.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right aHead bHead
      aDelta bDelta},
    (!aDelta && !bDelta) = false →
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterDeltaClassification left right
        aHead bHead aDelta bDelta)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- Head classification preserves the complete recursive state invariant,
including successful, absent, and partially failing lazy declaration loads. -/
theorem classifyDeltaHead_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (source : KExpr .anon) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (classifyDeltaHead source) (fun _ _ => True) := by
  unfold classifyDeltaHead
  cases hhead : headConstId source with
  | none =>
      exact RecM.WF.pure fun _ => trivial
  | some id =>
      unfold isDelta
      apply RecM.WF.bind <| RecM.WF.liftTcM <|
        TcM.tryGetConst_wf hfault id state
      intro found afterLookup _
      cases found with
      | none => exact RecM.WF.pure fun _ => trivial
      | some decl =>
          cases decl <;> simp only
          all_goals try exact RecM.WF.pure fun _ => trivial
          all_goals
            split <;> exact RecM.WF.pure fun _ => trivial

/-- Close both classifier lookups and the joint non-delta stopped result. -/
theorem defEqLazyDeltaStepAfterAcceleratorMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : Lean4Lean.VExpr}
    {left right : KExpr .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hafter : DefEqLazyDeltaAfterDeltaClassification.WFAt layer semantics
      trProj world support uvars)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterAcceleratorMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  unfold defEqLazyDeltaStepAfterAcceleratorMiss
  apply RecM.WF.bind (classifyDeltaHead_wf hfault left)
  intro leftDelta afterLeft _
  apply RecM.WF.bind (classifyDeltaHead_wf hfault right)
  intro rightDelta afterRight _
  cases hstopped : (!leftDelta && !rightDelta) with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ => hpair
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact hafter hstopped hpair

namespace DefEqLazyDeltaAfterAcceleratorMiss

/-- Package classification against the actual anonymous lazy-ingress
contract used by the no-acceleration driver. -/
theorem ofClassification
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (hafter : DefEqLazyDeltaAfterDeltaClassification.WFAt .noAccel semantics
      trProj world support uvars) :
    DefEqLazyDeltaAfterAcceleratorMiss.WFAt .noAccel semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource left right hpair
  exact defEqLazyDeltaStepAfterAcceleratorMiss_wf ingress.preserves hafter
    hpair

end DefEqLazyDeltaAfterAcceleratorMiss

end RecM

end Ix.Tc
