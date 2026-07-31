import Ix.Tc.Verify.DefEq.ProjectionDeltaStep

/-!
# Finishing a productive projection-directed delta step

After projection probing or delta unfolding changes a pair, the compact
projection loop performs its address and quick-structural checks and either
reports equality or schedules the transformed pair for another bounded
iteration.  This module proves that shared finish once.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Semantic resources used only by the final address/quick comparison. -/
structure ProjectionDeltaFinishResources (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop where
  theory : WhnfTheory trProj world uvars
  collision : support.CollisionFree
  sorts : SortComponentResources support
  structural : QuickDefEqResources support

/-- The productive-pair finish either proves the original operands equal or
returns the unchanged transformed pair with its invariant. -/
theorem finishLazyDeltaReductionStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (resources : ProjectionDeltaFinishResources trProj world support uvars)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (finishLazyDeltaReductionStep left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold finishLazyDeltaReductionStep
  apply RecM.WF.bind <|
    quickDefEq_wf resources.theory resources.collision resources.sorts
      resources.structural hpair.leftSupport hpair.rightSupport hleft hright
  intro accepted afterQuick haccepted
  cases hresult : (left.addr == right.addr || accepted) with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact RecM.WF.pure fun _ => hpair
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun hI => by
        have hcurrent : world.venv.IsDefEqU uvars Delta.toCtx leftV rightV := by
          rcases Bool.or_eq_true_iff.mp hresult with haddr | hquick
          · exact DefEqMeaning.of_translations resources.theory hI.2.1.wf
              hleft hright
              (DefEqMeaning.of_addr_beq resources.theory hI.2.1
                resources.collision hpair.leftSupport hpair.rightSupport
                hleft haddr) rfl
          · exact haccepted hquick
        exact hleftEq.trans world.venvWF hI.2.1.wf <|
          hcurrent.trans world.venvWF hI.2.1.wf hrightEq.symm

end RecM

end Ix.Tc
