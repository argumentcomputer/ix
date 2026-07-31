import Ix.Tc.Verify.DefEq.NatOffset

/-!
# Lazy-delta Nat reduction

After the offset probe misses, production conditionally tries the ordinary
Nat reducer on each operand.  A successful reduction is compared recursively
against the opposite operand.  This module composes the existing optional
reducer and predecessor DefEq contracts with the lazy-delta pair invariant.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Exact remaining one-step contract after both gated Nat reductions miss
or the gate is disabled. -/
def DefEqLazyDeltaAfterNatMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterNatMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- Close the gated left/right Nat-reduction prefix. -/
theorem defEqLazyDeltaStepAfterOffsetMiss_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hnat : OptionalReduction.WFAt .noAccel semantics trProj world support
      uvars tryReduceNat)
    (hafter : DefEqLazyDeltaAfterNatMiss.WFAt .noAccel semantics trProj
      world support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterOffsetMiss (left, right))
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepAfterOffsetMiss
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = state ∧ after = state)
    (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
  intro observed afterRead hread
  rcases hread with ⟨hObserved, hAfterRead⟩
  subst observed
  subst afterRead
  cases hgate :
      ((!left.hasFVars && !right.hasFVars) || state.eagerReduce) with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact hafter hpair
  | true =>
      simp only [if_true]
      apply RecM.WF.bind
        (RecM.WF.withInv <|
          hnat hpair.leftSupport hleft)
      intro leftResult afterLeft hleftResult
      rcases hleftResult with ⟨hILeft, hleftResult⟩
      cases leftResult with
      | some reducedLeft =>
          rcases hleftResult with ⟨hreducedSupport, hreducedMeaning⟩
          have hleftReduced := WhnfPost.transMeaning theory hDelta
            ⟨leftV, hleft, hleftEq⟩ hreducedMeaning
          obtain ⟨reducedV, hreduced, hleftReducedEq⟩ := hleftReduced
          apply RecM.WF.bind <|
            RecM.isDefEqCall_wf hreducedSupport hpair.rightSupport
              hreduced hright
          intro answer afterEq hanswer
          exact RecM.WF.pure fun _ htrue =>
            hleftReducedEq.trans world.venvWF hDelta <|
              (hanswer htrue).trans world.venvWF hDelta hrightEq.symm
      | none =>
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              hnat hpair.rightSupport hright)
          intro rightResult afterRight hrightResult
          rcases hrightResult with ⟨hIRight, hrightResult⟩
          cases rightResult with
          | some reducedRight =>
              rcases hrightResult with ⟨hreducedSupport, hreducedMeaning⟩
              have hrightReduced := WhnfPost.transMeaning theory hDelta
                ⟨rightV, hright, hrightEq⟩ hreducedMeaning
              obtain ⟨reducedV, hreduced, hrightReducedEq⟩ := hrightReduced
              apply RecM.WF.bind <|
                RecM.isDefEqCall_wf hpair.leftSupport hreducedSupport
                  hleft hreduced
              intro answer afterEq hanswer
              exact RecM.WF.pure fun _ htrue =>
                hleftEq.trans world.venvWF hDelta <|
                  (hanswer htrue).trans world.venvWF hDelta
                    hrightReducedEq.symm
          | none =>
              exact hafter hpair

namespace DefEqLazyDeltaAfterOffsetMiss

/-- Package the Nat prefix as the complete post-offset-miss contract. -/
theorem ofNat
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hnat : OptionalReduction.WFAt .noAccel semantics trProj world support
      uvars tryReduceNat)
    (hafter : DefEqLazyDeltaAfterNatMiss.WFAt .noAccel semantics trProj
      world support uvars) :
    DefEqLazyDeltaAfterOffsetMiss.WFAt .noAccel semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource pair hpair
  rcases pair with ⟨left, right⟩
  intro methods hmethods hI
  exact (defEqLazyDeltaStepAfterOffsetMiss_wf theory hnat hafter
    hI.2.1.wf hpair) methods hmethods hI

end DefEqLazyDeltaAfterOffsetMiss

end RecM

end Ix.Tc
