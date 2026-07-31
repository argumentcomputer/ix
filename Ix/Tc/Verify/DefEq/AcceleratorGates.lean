import Ix.Tc.Verify.DefEq.NatReduction
import Ix.Tc.Verify.Whnf.Driver.FullStep

/-!
# Lazy-delta accelerator gates

The verification stack closes the recursive kernel in the `.noAccel` layer.
In that layer both native evaluation and Decidable synthesis return `none`
before inspecting their operands or invoking callbacks.  This module removes
those four operationally unreachable hit branches from lazy delta and exposes
the first substantive remaining tail: delta-head classification.
-/

namespace Ix.Tc

namespace RecM

/-- Exact remaining one-step contract after both native and both Decidable
acceleration probes miss. -/
def DefEqLazyDeltaAfterAcceleratorMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterAcceleratorMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- In `.noAccel`, the native and Decidable prefix is definitionally a chain
of four misses, so it delegates to the post-accelerator tail without any new
semantic premise. -/
theorem defEqLazyDeltaStepAfterNatMiss_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : Lean4Lean.VExpr}
    {left right : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hafter : DefEqLazyDeltaAfterAcceleratorMiss.WFAt .noAccel semantics
      trProj world support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterNatMiss left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepAfterNatMiss
  apply RecM.WF.bind
    (RecM.WF.withInv <|
      tryReduceNative_noAccel_optional_wf hpair.leftSupport hleft)
  intro leftNative afterLeftNative hleftNative
  rcases hleftNative with ⟨hILeftNative, hleftNative⟩
  cases leftNative with
  | some reducedLeft =>
      rcases hleftNative with ⟨hreducedSupport, hreducedMeaning⟩
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
          tryReduceNative_noAccel_optional_wf hpair.rightSupport hright)
      intro rightNative afterRightNative hrightNative
      rcases hrightNative with ⟨hIRightNative, hrightNative⟩
      cases rightNative with
      | some reducedRight =>
          rcases hrightNative with ⟨hreducedSupport, hreducedMeaning⟩
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
          apply RecM.WF.bind
            (RecM.WF.withInv <|
              tryReduceDecidable_noAccel_optional_wf
                hpair.leftSupport hleft)
          intro leftDecidable afterLeftDecidable hleftDecidable
          rcases hleftDecidable with ⟨hILeftDecidable, hleftDecidable⟩
          cases leftDecidable with
          | some reducedLeft =>
              rcases hleftDecidable with
                ⟨hreducedSupport, hreducedMeaning⟩
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
                  tryReduceDecidable_noAccel_optional_wf
                    hpair.rightSupport hright)
              intro rightDecidable afterRightDecidable hrightDecidable
              rcases hrightDecidable with
                ⟨hIRightDecidable, hrightDecidable⟩
              cases rightDecidable with
              | some reducedRight =>
                  rcases hrightDecidable with
                    ⟨hreducedSupport, hreducedMeaning⟩
                  have hrightReduced := WhnfPost.transMeaning theory hDelta
                    ⟨rightV, hright, hrightEq⟩ hreducedMeaning
                  obtain ⟨reducedV, hreduced, hrightReducedEq⟩ :=
                    hrightReduced
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

namespace DefEqLazyDeltaAfterNatMiss

/-- Package the no-acceleration gate proof as the complete post-Nat
contract. -/
theorem ofNoAccel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hafter : DefEqLazyDeltaAfterAcceleratorMiss.WFAt .noAccel semantics
      trProj world support uvars) :
    DefEqLazyDeltaAfterNatMiss.WFAt .noAccel semantics trProj world support
      uvars := by
  intro Delta state leftSource rightSource left right hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepAfterNatMiss_wf theory hafter hI.2.1.wf hpair)
    methods hmethods hI

end DefEqLazyDeltaAfterNatMiss

end RecM


end Ix.Tc
