import Ix.Tc.Verify.Check.PreTranslationCompatibility
import Ix.Tc.Verify.Infer.CacheSoundness

/-!
# Full inference from untyped checker ingress

The ordinary K2 contract starts from `TrKExprS`, which already contains the
typing facts checked by full inference.  K3 instead starts from
`PreTrKExprS` and must return the missing typed translation together with the
usual inference result.

This file records that stronger postcondition and discharges the production
full-cache-hit branch.  A cache hit is not circular: cache provenance supplies
an earlier typed translation, and `PreTrKExprS.upgradeOfTyped` reconciles it
with the exact translation chosen by the current raw ingress.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Successful full inference both validates the source translation and
returns a Theory type for that exact translated source. -/
def FullInferPost (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (source : KExpr .anon) (sourceV : VExpr)
    (result : KExpr .anon) : Prop :=
  support result ∧
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ∧
    InferPost trProj world uvars Delta sourceV result

namespace FullInferPost

/-- Strengthen the ordinary K2 inference post once the current source has
independently been upgraded to a typed structural translation. -/
theorem of_typed
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source result : KExpr .anon}
    {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hpost : support result ∧
      InferPost trProj world uvars Delta sourceV result) :
    FullInferPost trProj world support uvars Delta source sourceV result :=
  ⟨hpost.1, hsource, hpost.2⟩

end FullInferPost

namespace RecM

/-- A validated full-cache hit upgrades the current untyped structural
translation and returns the same strong postcondition required of a fresh
full inference run. -/
theorem inferWith_fullHit_pre_acceptance
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {model : KernelSuffixModel trProj world}
    {Delta : KVLCtx} {source cached : KExpr .anon}
    {sourceV : VExpr} {key : Address × Address}
    {s s' : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hkey : TcM.inferKey source s = .ok key s')
    (hhit : s'.env.inferCache[key]? = some cached)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (hsourceSupport : support source)
    (hsource : PreTrKExprS world.venv model.keys.uvars world.nameOf trProj
      Delta source sourceV) :
    (inferWith inferRec source).run methods s = .ok cached s' ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta s' ∧
      FullInferPost trProj world support model.keys.uvars Delta
        source sourceV cached := by
  have hkeyPost :=
    (TcM.inferKey_model_matches_wf (layer := layer)
      (support := support) model (Delta := Delta) (source := source)
      (s := s)) hI
  rw [hkey] at hkeyPost
  have hprovenance := hkeyPost.1.1.caches.hit (.infer hhit)
  have hmeaning := hprovenance.kernelInferMeaningOfMatches
    .infer hsourceSupport hkeyPost.2.1
  obtain ⟨typedV, htyped, hcachedPost⟩ := hmeaning
  have hDelta := hI.2.1.wf
  have hsourceTyped : TrKExprS world.venv model.keys.uvars world.nameOf
      trProj Delta source sourceV :=
    hsource.upgradeOfTyped world.venvWF theory.literalWF
      theory.projections (KVLCtx.IsDefEq.refl world.venvWF hDelta) htyped
  exact ⟨inferWith_fullHit hkey hhit, hkeyPost.1,
    hprovenance.supported.2, hsourceTyped,
    InferMeaning.post theory hDelta hsourceTyped
      ⟨typedV, htyped, hcachedPost⟩⟩

end RecM

end Ix.Tc
