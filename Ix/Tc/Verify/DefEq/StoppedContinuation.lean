import Ix.Tc.Verify.DefEq.ApplicationSpine
import Ix.Tc.Verify.DefEq.StructuralCongruence

/-!
# Stopped lazy-delta continuation

Once bounded lazy delta stops, production tries structural congruence, reduces
both sides with `whnfCore`, recursively compares a changed pair, and otherwise
tries address equality, quick structural equality, application-spine equality,
and the final WHNF comparator in that order.  This module proves that exact
outer control flow from contracts for its substantive helpers.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Exact semantic contract for the final full-WHNF comparison tier.  Its
constructor-exhaustive implementation is intentionally separated from the
outer stopped-continuation control flow. -/
def IsDefEqWhnf.WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnf left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- The exact helper contracts consumed by the stopped continuation. -/
structure StoppedContinuationResources (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop where
  structural : TryStructuralCongruence.WFAt layer semantics trProj world
    support uvars
  core : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfCore
  sorts : SortComponentResources support
  quick : QuickDefEqResources support
  application : TryDefEqApp.WFAt layer semantics trProj world support uvars
  finalWhnf : IsDefEqWhnf.WFAt layer semantics trProj world support uvars

/-- Complete execution proof of the production continuation after lazy delta
stops.  Every accepting branch is transported back to the two original
operands retained by `DefEqPairInvariant`. -/
theorem isDefEqAfterLazyDeltaStopped_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (collision : support.CollisionFree)
    (resources : StoppedContinuationResources layer semantics trProj world
      support uvars)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqAfterLazyDeltaStopped left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftSource rightSource) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold isDefEqAfterLazyDeltaStopped
  apply RecM.WF.bind <|
    resources.structural hpair.leftSupport hpair.rightSupport hleft hright
  intro structurallyEqual afterStructural hstructural
  cases structurallyEqual with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun hI _ =>
        hleftEq.trans world.venvWF hI.2.1.wf <|
          (hstructural rfl).trans world.venvWF hI.2.1.wf hrightEq.symm
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind (RecM.WF.withInv <|
        resources.core hpair.leftSupport hleft)
      intro leftCore afterLeftCore hleftCore
      rcases hleftCore with
        ⟨hILeftCore, hleftCoreSupport, leftCoreV, hleftCoreTr,
          hleftCoreEq⟩
      apply RecM.WF.bind (RecM.WF.withInv <|
        resources.core hpair.rightSupport hright)
      intro rightCore afterRightCore hrightCore
      rcases hrightCore with
        ⟨hIRightCore, hrightCoreSupport, rightCoreV, hrightCoreTr,
          hrightCoreEq⟩
      cases hchanged :
          (leftCore.addr != left.addr || rightCore.addr != right.addr) with
      | true =>
          simp only [if_true, pure_bind]
          refine RecM.WF.mono (RecM.WF.withInv <|
            RecM.isDefEqCall_wf hleftCoreSupport hrightCoreSupport
              hleftCoreTr hrightCoreTr) ?_ (fun _ _ h => h)
          rintro answer final ⟨hI, hanswer⟩ htrue
          exact hleftEq.trans world.venvWF hI.2.1.wf <|
            hleftCoreEq.trans world.venvWF hI.2.1.wf <|
              (hanswer htrue).trans world.venvWF hI.2.1.wf <|
                hrightCoreEq.symm.trans world.venvWF hI.2.1.wf
                  hrightEq.symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases haddr : leftCore.addr == rightCore.addr with
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun hI _ => by
                have herase := collision.expr hleftCoreSupport
                  hrightCoreSupport (eq_of_beq haddr)
                have hsame : leftCore = rightCore := by
                  simpa only [KExpr.eraseMeta_anon] using herase
                subst rightCore
                have hmiddle := hleftCoreTr.uniq world.venvWF
                  theory.literalWF theory.projections
                  (KVLCtx.IsDefEq.refl world.venvWF hI.2.1.wf)
                  hrightCoreTr
                exact hleftEq.trans world.venvWF hI.2.1.wf <|
                  hleftCoreEq.trans world.venvWF hI.2.1.wf <|
                    hmiddle.trans world.venvWF hI.2.1.wf <|
                      hrightCoreEq.symm.trans world.venvWF hI.2.1.wf
                        hrightEq.symm
          | false =>
              simp only [Bool.false_eq_true, if_false]
              apply RecM.WF.bind <|
                quickDefEq_wf theory collision resources.sorts
                  resources.quick hleftCoreSupport hrightCoreSupport
                  hleftCoreTr hrightCoreTr
              intro quicklyEqual afterQuick hquick
              cases quicklyEqual with
              | true =>
                  simp only [if_true]
                  exact RecM.WF.pure fun hI _ =>
                    hleftEq.trans world.venvWF hI.2.1.wf <|
                      hleftCoreEq.trans world.venvWF hI.2.1.wf <|
                        (hquick rfl).trans world.venvWF hI.2.1.wf <|
                          hrightCoreEq.symm.trans world.venvWF hI.2.1.wf
                            hrightEq.symm
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  apply RecM.WF.bind <|
                    resources.application hleftCoreSupport
                      hrightCoreSupport hleftCoreTr hrightCoreTr
                  intro applicationsEqual afterApplication happlication
                  cases applicationsEqual with
                  | true =>
                      simp only [if_true]
                      exact RecM.WF.pure fun hI _ =>
                        hleftEq.trans world.venvWF hI.2.1.wf <|
                          hleftCoreEq.trans world.venvWF hI.2.1.wf <|
                            (happlication rfl).trans world.venvWF
                              hI.2.1.wf <|
                              hrightCoreEq.symm.trans world.venvWF
                                hI.2.1.wf hrightEq.symm
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      apply RecM.WF.mono (RecM.WF.withInv <|
                        resources.finalWhnf hleftCoreSupport
                          hrightCoreSupport hleftCoreTr hrightCoreTr)
                      · intro answer final hpost htrue
                        rcases hpost with ⟨hI, hanswer⟩
                        exact hleftEq.trans world.venvWF hI.2.1.wf <|
                          hleftCoreEq.trans world.venvWF hI.2.1.wf <|
                            (hanswer htrue).trans world.venvWF hI.2.1.wf <|
                              hrightCoreEq.symm.trans world.venvWF
                                hI.2.1.wf hrightEq.symm
                      · intro _ _ _
                        trivial

namespace DefEqAfterLazyDeltaStopped

/-- Package the production theorem as the exact stopped-continuation
contract used by the bounded lazy-delta driver. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (collision : support.CollisionFree)
    (resources : StoppedContinuationResources layer semantics trProj world
      support uvars) :
    DefEqAfterLazyDeltaStopped.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state leftSource rightSource left right hpair
  exact isDefEqAfterLazyDeltaStopped_wf theory collision resources hpair

end DefEqAfterLazyDeltaStopped

end RecM

end Ix.Tc
