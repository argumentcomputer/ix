import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.DefEq.ProofIrrelevance

/-!
# Final-WHNF proof-irrelevance tail

The final fallback is the already-verified proof-irrelevance probe.  This
module packages it at the final-WHNF seam and composes it with an independently
verified unit-like shortcut.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- The final-WHNF tail is exactly the concrete proof-irrelevance probe. -/
theorem isDefEqWhnfAfterUnit_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterUnit left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  simpa only [isDefEqWhnfAfterUnit] using
    (tryProofIrrel_wf hisProp hleftSupport hrightSupport hleft hright)

namespace IsDefEqWhnfAfterUnit

/-- Package the concrete proposition classifier at the terminal seam. -/
theorem ofClassifier
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars) :
    IsDefEqWhnfAfterUnit.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact isDefEqWhnfAfterUnit_wf hisProp hleftSupport hrightSupport hleft
    hright

end IsDefEqWhnfAfterUnit

/-- Compose the unit-like shortcut with the terminal proof-irrelevance
fallback. -/
theorem isDefEqWhnfAfterStructEta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hunit : TryDefEqUnit.WFAt layer semantics trProj world support uvars)
    (htail : IsDefEqWhnfAfterUnit.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterStructEta left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnfAfterStructEta
  apply RecM.WF.bind <|
    hunit hleftSupport hrightSupport hleft hright
  intro accepted afterUnit haccepted
  cases accepted with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => haccepted rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact htail hleftSupport hrightSupport hleft hright

namespace IsDefEqWhnfAfterStructEta

/-- Package the unit-like and proof-irrelevance tail contracts. -/
theorem ofUnitAndProof
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hunit : TryDefEqUnit.WFAt layer semantics trProj world support uvars)
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars) :
    IsDefEqWhnfAfterStructEta.WFAt layer semantics trProj world support
      uvars := by
  exact fun hleftSupport hrightSupport hleft hright =>
    isDefEqWhnfAfterStructEta_wf hunit
      (IsDefEqWhnfAfterUnit.ofClassifier hisProp)
      hleftSupport hrightSupport hleft hright

end IsDefEqWhnfAfterStructEta

/-- Compose the optional structure-eta phase with the unit/proof tail. -/
theorem isDefEqWhnfAfterString_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hstructEta : TryDefEqWhnfStructEta.WFAt layer semantics trProj world
      support uvars)
    (htail : IsDefEqWhnfAfterStructEta.WFAt layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterString left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnfAfterString
  apply RecM.WF.bind <|
    hstructEta hleftSupport hrightSupport hleft hright
  intro result afterStructEta hresult
  cases result with
  | none => exact htail hleftSupport hrightSupport hleft hright
  | some answer => exact RecM.WF.pure fun _ => hresult

namespace IsDefEqWhnfAfterString

/-- Package structure eta with its concrete unit/proof continuation. -/
theorem ofStructEta
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hstructEta : TryDefEqWhnfStructEta.WFAt layer semantics trProj world
      support uvars)
    (htail : IsDefEqWhnfAfterStructEta.WFAt layer semantics trProj world
      support uvars) :
    IsDefEqWhnfAfterString.WFAt layer semantics trProj world support
      uvars := by
  exact fun hleftSupport hrightSupport hleft hright =>
    isDefEqWhnfAfterString_wf hstructEta htail hleftSupport hrightSupport
      hleft hright

end IsDefEqWhnfAfterString

end RecM

end Ix.Tc
