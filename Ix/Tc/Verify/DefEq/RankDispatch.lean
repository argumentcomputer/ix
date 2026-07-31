import Ix.Tc.Verify.DefEq.OneSidedDelta

/-!
# Lazy-delta rank dispatch

After projection probing, reducibility ranks select a left-only, right-only,
or equal-rank reduction.  Rank values have no semantic interpretation in the
soundness theorem: they choose among reduction helpers that are proved sound
independently.  Their declaration lookups must nevertheless preserve the
state invariant across lazy ingress.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Contract for the sole remaining equal-rank lazy-delta branch. -/
def DefEqLazyDeltaEqualRank.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right aHead bHead},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepWithEqualRank left right aHead bHead)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- Reducibility-rank lookup preserves the recursive state invariant through
all declaration shapes and lazy-load outcomes. -/
theorem rankDeltaHead_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (head : Option (KId .anon)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (rankDeltaHead head) (fun _ _ => True) := by
  unfold rankDeltaHead
  cases head with
  | none => exact RecM.WF.pure fun _ => trivial
  | some id =>
      unfold defRankId
      apply RecM.WF.bind <| RecM.WF.liftTcM <|
        TcM.tryGetConst_wf hfault id state
      intro found afterLookup _
      cases found with
      | none => exact RecM.WF.pure fun _ => trivial
      | some decl =>
          cases decl <;> simp only
          all_goals try exact RecM.WF.pure fun _ => trivial
          all_goals
            split <;> try exact RecM.WF.pure fun _ => trivial
          all_goals
            split <;> exact RecM.WF.pure fun _ => trivial

/-- Dispatch every post-projection flag/rank combination.  The impossible
joint-negative flag case is excluded by the caller's exact gate equation. -/
theorem defEqLazyDeltaStepAfterProjectionMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {aHead bHead : Option (KId .anon)} {aDelta bDelta : Bool}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (context : LazyDeltaReductionContext layer semantics trProj world support
      uvars)
    (hequal : DefEqLazyDeltaEqualRank.WFAt layer semantics trProj world
      support uvars)
    (hactive : (!aDelta && !bDelta) = false)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterProjectionMiss left right
        aHead bHead aDelta bDelta)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  unfold defEqLazyDeltaStepAfterProjectionMiss
  cases aDelta <;> cases bDelta
  case false.false =>
    simp at hactive
  case false.true =>
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    exact defEqLazyDeltaStepWithRightDelta_wf context hDelta hpair
  case true.false =>
    simp only [Bool.true_and, Bool.false_eq_true, if_false, if_true]
    exact defEqLazyDeltaStepWithLeftDelta_wf context hDelta hpair
  case true.true =>
    simp only [Bool.true_and, if_true]
    apply RecM.WF.bind (rankDeltaHead_wf hfault aHead)
    intro leftRank afterLeftRank _
    apply RecM.WF.bind (rankDeltaHead_wf hfault bHead)
    intro rightRank afterRightRank _
    cases heq : leftRank == rightRank with
    | true =>
        simp only [if_true]
        exact hequal hpair
    | false =>
        simp only [Bool.false_eq_true, if_false]
        cases hcompare : compareRank leftRank rightRank with
        | lt =>
            exact defEqLazyDeltaStepWithRightDelta_wf context hDelta hpair
        | eq =>
            exact defEqLazyDeltaStepWithRightDelta_wf context hDelta hpair
        | gt =>
            exact defEqLazyDeltaStepWithLeftDelta_wf context hDelta hpair

namespace DefEqLazyDeltaAfterProjectionMiss

/-- Package rank dispatch with the concrete anonymous lazy-ingress contract. -/
theorem ofRankDispatch
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (ingress : AnonLazyIngressContext .noAccel semantics trProj world
      support)
    (context : LazyDeltaReductionContext .noAccel semantics trProj world
      support uvars)
    (hequal : DefEqLazyDeltaEqualRank.WFAt .noAccel semantics trProj world
      support uvars) :
    DefEqLazyDeltaAfterProjectionMiss.WFAt .noAccel semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource left right aHead bHead aDelta
    bDelta hactive hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepAfterProjectionMiss_wf ingress.preserves context
    hequal hactive hI.2.1.wf hpair) methods hmethods hI

end DefEqLazyDeltaAfterProjectionMiss

end RecM

end Ix.Tc
