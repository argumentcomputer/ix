import Ix.Tc.Verify.DefEq.DeltaClassification

/-!
# Lazy-delta projection probe

When exactly one side is delta-reducible, lazy delta gives a projection-headed
opposite operand one no-delta normalization opportunity before unfolding the
definition.  This module proves the helper as an optional reduction and then
closes both asymmetric branches, transporting a successful projection result
into the loop's pair invariant.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Exact remaining one-step contract after the asymmetric projection probe
is skipped or misses. -/
def DefEqLazyDeltaAfterProjectionMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right aHead bHead
      aDelta bDelta},
    (!aDelta && !bDelta) = false →
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterProjectionMiss left right
        aHead bHead aDelta bDelta)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- The production projection probe is an optional reduction whenever the
public no-delta reducer has its standard support-and-meaning contract. -/
theorem tryUnfoldProjApp_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hwhnf : DefEqReduction.WFAt layer semantics trProj world support uvars
      whnfNoDelta) :
    OptionalReduction.WFAt layer semantics trProj world support uvars
      tryUnfoldProjApp := by
  intro Delta source sourceV state hsourceSupport hsource
  unfold tryUnfoldProjApp
  generalize hspine : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head <;> simp only
  all_goals try exact RecM.WF.pure fun _ => trivial
  case prj =>
    apply RecM.WF.bind (hwhnf hsourceSupport hsource)
    intro reduced afterReduced hreduced
    cases haddr : reduced.addr == source.addr with
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ => trivial
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact RecM.WF.pure fun _ =>
          ⟨hreduced.1, WhnfPost.meaning hsource hreduced.2⟩

/-- Close the projection-headed opposite-side probes in both directions. -/
theorem defEqLazyDeltaStepAfterDeltaClassification_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    {aHead bHead : Option (KId .anon)} {aDelta bDelta : Bool}
    (theory : WhnfTheory trProj world uvars)
    (hproj : OptionalReduction.WFAt layer semantics trProj world support
      uvars tryUnfoldProjApp)
    (hafter : DefEqLazyDeltaAfterProjectionMiss.WFAt layer semantics trProj
      world support uvars)
    (hactive : (!aDelta && !bDelta) = false)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterDeltaClassification left right
        aHead bHead aDelta bDelta)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStepAfterDeltaClassification
  cases aDelta <;> cases bDelta
  case false.false =>
    simp at hactive
  case false.true =>
    simp only [Bool.false_and, Bool.false_eq_true, if_false,
      Bool.not_false, Bool.true_and, if_true]
    apply RecM.WF.bind
      (RecM.WF.withInv <|
        hproj hpair.leftSupport hleft)
    intro reduced afterReduced hreduced
    rcases hreduced with ⟨hI, hreduced⟩
    cases reduced with
    | none =>
        exact hafter (aHead := aHead) (bHead := bHead) hactive hpair
    | some reducedLeft =>
        rcases hreduced with ⟨hreducedSupport, hreducedMeaning⟩
        exact RecM.WF.pure fun _ =>
          ⟨hreducedSupport, hpair.rightSupport,
            WhnfPost.transMeaning theory hDelta hpair.left hreducedMeaning,
            hpair.right⟩
  case true.false =>
    simp only [Bool.not_true, Bool.true_and]
    apply RecM.WF.bind
      (RecM.WF.withInv <|
        hproj hpair.rightSupport hright)
    intro reduced afterReduced hreduced
    rcases hreduced with ⟨hI, hreduced⟩
    cases reduced with
    | none =>
        exact hafter (aHead := aHead) (bHead := bHead) hactive hpair
    | some reducedRight =>
        rcases hreduced with ⟨hreducedSupport, hreducedMeaning⟩
        exact RecM.WF.pure fun _ =>
          ⟨hpair.leftSupport, hreducedSupport, hpair.left,
            WhnfPost.transMeaning theory hDelta hpair.right hreducedMeaning⟩
  case true.true =>
    simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
    exact hafter (aHead := aHead) (bHead := bHead) hactive hpair

namespace DefEqLazyDeltaAfterDeltaClassification

/-- Package projection probing as the complete post-classification
contract. -/
theorem ofProjection
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hproj : OptionalReduction.WFAt layer semantics trProj world support
      uvars tryUnfoldProjApp)
    (hafter : DefEqLazyDeltaAfterProjectionMiss.WFAt layer semantics trProj
      world support uvars) :
    DefEqLazyDeltaAfterDeltaClassification.WFAt layer semantics trProj world
      support uvars := by
  intro Delta state leftSource rightSource left right aHead bHead aDelta
    bDelta hactive hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStepAfterDeltaClassification_wf theory hproj hafter
    hactive hI.2.1.wf hpair) methods hmethods hI

end DefEqLazyDeltaAfterDeltaClassification

end RecM

end Ix.Tc
