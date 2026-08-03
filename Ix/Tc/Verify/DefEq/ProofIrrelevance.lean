import Ix.Tc.Verify.DefEq.CheapReduction
import Ix.Tc.Verify.Whnf.StructEta.CallbackPrefix

/-!
# Pre-delta proof irrelevance

This tier infers both operands under the infer-only policy, establishes that
the first inferred type is a proposition, and compares the two inferred
types recursively.  A positive result is justified by Theory proof
irrelevance; caught callback errors remain ordinary misses.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- The Infer spelling used by DefEq is operationally the same scoped
predecessor callback already verified for WHNF helpers. -/
theorem tryOptionalInferOnlyCall_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryOptional (inferOnlyCall source))
      (fun result _ => match result with
        | some ty => support ty ∧
            InferPost trProj world uvars Delta sourceV ty
        | none => True) := by
  simpa only [inferOnlyCall, inferOnlyRec] using
    (tryOptionalInferOnlyRec_wf
      (layer := layer) (semantics := semantics) (s := state)
      hsourceSupport hsource)

/-- Semantic contract for the memoized proposition-type classifier.  Only a
positive result carries meaning; a negative result remains conservative. -/
def IsPropType.WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state source sourceV},
    support source →
    TrKExpr world.venv uvars world.nameOf trProj Delta source sourceV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isPropType source)
      (fun answer _ => answer = true →
        world.venv.HasType uvars Delta.toCtx sourceV (.sort .zero))

/-- The concrete proof-irrelevance probe is sound once the memoized
proposition classifier satisfies its positive-result contract. -/
theorem tryProofIrrel_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {a b : KExpr .anon} {aV bV : VExpr}
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b bV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryProofIrrel a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV) := by
  unfold tryProofIrrel
  apply RecM.WF.bind
    (tryOptionalInferOnlyCall_wf haSupport ha)
  intro aTy afterA haTy
  cases aTy with
  | none =>
      simp only
      exact RecM.WF.pure fun _ htrue => by contradiction
  | some aTy =>
      rcases haTy with ⟨haTySupport, aTyV, haTyTr, haType⟩
      simp only
      apply RecM.WF.bind (hisProp haTySupport haTyTr)
      intro aIsProp afterProp haProp
      cases aIsProp with
      | false =>
          simp only [Bool.not_false]
          exact RecM.WF.pure fun _ htrue => by contradiction
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          apply RecM.WF.bind
            (tryOptionalInferOnlyCall_wf hbSupport hb)
          intro bTy afterB hbTy
          cases bTy with
          | none =>
              simp only
              exact RecM.WF.pure fun _ htrue => by contradiction
          | some bTy =>
              rcases hbTy with ⟨hbTySupport, bTyV, hbTyTr, hbType⟩
              obtain ⟨aTyCoreV, haTyCoreTr, haTyEq⟩ := haTyTr
              obtain ⟨bTyCoreV, hbTyCoreTr, hbTyEq⟩ := hbTyTr
              simp only
              apply RecM.WF.mono
                (RecM.WF.withInv <|
                  isDefEqCall_wf haTySupport hbTySupport
                    haTyCoreTr hbTyCoreTr)
              · intro answer final hpost htrue
                have htypes : world.venv.IsDefEqU uvars Delta.toCtx
                    aTyV bTyV :=
                  haTyEq.symm.trans world.venvWF hpost.1.2.1.wf <|
                    (hpost.2 htrue).trans world.venvWF hpost.1.2.1.wf
                      hbTyEq
                exact ⟨aTyV, .proofIrrel (haProp rfl) haType
                  (hbType.defeqU_r world.venvWF hpost.1.2.1.wf
                    htypes.symm)⟩
              · intro _ _ _
                trivial

namespace DefEqAfterProofIrrelevance

/-- Semantic contract for the lazy-delta and final-WHNF tiers. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqInnerAfterProofIrrelevance a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

/-- Close the pre-delta proof-irrelevance attempt. -/
theorem closesAfterNoDeltaPass
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterNoDeltaPass.WF layer semantics trProj world support uvars := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInnerAfterNoDeltaPass
  apply RecM.WF.bind
    (tryProofIrrel_wf hisProp haSupport hbSupport ha hb)
  intro accepted after haccepted
  cases accepted with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => haccepted rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact htail haSupport hbSupport ha hb

/-- Compose proof irrelevance with both preceding cheap passes. -/
theorem closesAfterStringExpansion
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (hreduction : DefEqCheapReductionContext layer semantics trProj world
      support uvars)
    (hisProp : IsPropType.WFAt layer semantics trProj world support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterStringExpansion.WF layer semantics trProj world support
      uvars :=
  DefEqAfterNoDeltaPass.closesAfterStringExpansion theory hcollision hsorts
    hstructural hreduction (closesAfterNoDeltaPass hisProp htail)

end DefEqAfterProofIrrelevance

end RecM

end Ix.Tc
