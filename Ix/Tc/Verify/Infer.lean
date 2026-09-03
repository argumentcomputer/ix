import Ix.Tc.Verify.Suffix
import Ix.Tc.Verify.Knot

/-!
# K2 inference semantics

This module replaces the inference-cache portion of K1's fallback semantics
with its exact Theory meaning.  Algorithmic branch proofs will consume the
hit and insertion interfaces defined here.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace TcM

/-- Inference and WHNF deliberately share the exact production key
algorithm; the theorem pins that policy so the cache proof cannot drift from
runtime behavior. -/
@[simp] theorem inferKey_eq_whnfKey (source : KExpr .anon) :
    TcM.inferKey source = TcM.whnfKey source := rfl

/-- Inference-key computation preserves the complete fixed-world invariant
and returns the concrete source address in the first component. -/
theorem inferKey_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.inferKey source)
      (fun key s' => key.1 = source.addr ∧ ContextKeyFrame s s') := by
  simpa using (TcM.whnfKey_wf (layer := layer) (semantics := semantics)
    (trProj := trProj) (world := world) (support := support)
    (uvars := uvars) (Δ := Delta) (source := source) (s := s))

/-- The canonical operational key interpretation needs no representation
oracle for inference: the successful key run itself is the witness. -/
theorem inferKey_operational_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.inferKey source)
      (fun key s' =>
        (operationalWhnfContextKeys trProj world uvars).Matches trProj world
          s Delta source key ∧ ContextKeyFrame s s') := by
  simpa [operationalWhnfContextKeys] using
    (TcM.whnfKey_matches_wf (layer := layer) (semantics := semantics)
      (trProj := trProj) (world := world) (support := support)
      (keys := operationalWhnfContextKeys trProj world uvars)
      (Δ := Delta) (source := source) (s := s)
      (fun key s' hctx hrun =>
        operationalWhnfContextKeys.represents hctx hrun))

end TcM

namespace RecM

/-- A validated inference-cache hit returns immediately after the shared key
computation, in either inference policy. -/
theorem inferWith_fullHit
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source cached : KExpr .anon}
    {key : Address × Address} {s s' : TcState .anon}
    (hkey : TcM.inferKey source s = .ok key s')
    (hhit : s'.env.inferCache[key]? = some cached) :
    (inferWith inferRec source).run methods s = .ok cached s' := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s' = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s' = .ok s' s' from rfl]
  simp only [hhit]
  rfl

/-- An infer-only entry is consulted only after the validated cache misses
and the captured policy bit is true. -/
theorem inferWith_inferOnlyHit
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {source cached : KExpr .anon}
    {key : Address × Address} {s s' : TcState .anon}
    (hpolicy : s.inferOnly = true)
    (hkey : TcM.inferKey source s = .ok key s')
    (hfullMiss : s'.env.inferCache[key]? = none)
    (hhit : s'.env.inferOnlyCache[key]? = some cached) :
    (inferWith inferRec source).run methods s = .ok cached s' := by
  unfold inferWith
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.inferKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s' = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s' = .ok s' s' from rfl]
  simp only [hfullMiss, hpolicy]
  simp only [pure_bind, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s' = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s' = .ok s' s' from rfl]
  simp only [hhit]
  rfl

namespace InferCacheUpdate

/-- Installing a certified full inference result changes only its physical
cache partition and preserves the complete checker invariant. -/
theorem full_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {ty : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .infer key ty)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        inferCache := s.env.inferCache.insert key ty}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertInfer hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Installing an infer-only result cannot widen it into the validated full
partition; the corresponding state update preserves all other invariants. -/
theorem inferOnly_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {ty : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .inferOnly key ty)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        inferOnlyCache := s.env.inferOnlyCache.insert key ty}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertInferOnly hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end InferCacheUpdate

end RecM

/-- A concrete inference result translates to a Theory type of the translated
source expression in the represented mixed context. -/
def InferMeaning (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (source ty : KExpr .anon) : Prop :=
  ∃ sourceV,
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ∧
      InferPost trProj world uvars Delta sourceV ty

namespace InferMeaning

theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after) {uvars : Nat} {Delta : KVLCtx}
    {source ty : KExpr .anon}
    (h : InferMeaning trProj before uvars Delta source ty) :
    InferMeaning trProj after uvars Delta source ty := by
  obtain ⟨sourceV, hsource, tyV, hty, hhasType⟩ := h
  obtain ⟨tyCoreV, htyCore, htyEq⟩ := hty
  refine ⟨sourceV, ?_, tyV, ⟨tyCoreV, ?_, htyEq.mono hle.venv⟩,
    hhasType.mono hle.venv⟩
  · simpa only [← hle.nameOf] using hsource.mono hle.venv
  · simpa only [← hle.nameOf] using htyCore.mono hle.venv

theorem of_post {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {source ty : KExpr .anon}
    {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hpost : InferPost trProj world uvars Delta sourceV ty) :
    InferMeaning trProj world uvars Delta source ty :=
  ⟨sourceV, hsource, hpost⟩

/-- Recover the caller-indexed postcondition from cache meaning.  Structural
translation is unique only up to definitional equality, so the proof uses
Theory uniqueness before transporting the typing derivation. -/
theorem post {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars) {Delta : KVLCtx}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source ty : KExpr .anon} {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (h : InferMeaning trProj world uvars Delta source ty) :
    InferPost trProj world uvars Delta sourceV ty := by
  obtain ⟨cachedV, hcached, tyV, hty, hhasType⟩ := h
  refine ⟨tyV, hty, ?_⟩
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have hsourceEq := hcached.uniq world.venvWF theory.literalWF
    theory.projections hctx hsource
  exact hhasType.defeqU_l world.venvWF hDelta hsourceEq

end InferMeaning

namespace ExprCacheKind

inductive IsInfer : ExprCacheKind → Prop
  | infer : IsInfer .infer
  | inferOnly : IsInfer .inferOnly

end ExprCacheKind

/-- Exact validity of the two inference cache families.  All other entries
retain the semantics already established by the caller (normally K1 WHNF).
Persistent entries created under a later-popped local scope are required to
carry semantic meaning only when their source is structurally in scope in the
represented context. -/
def InferCacheValid (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .expr .infer key ty | .expr .inferOnly key ty =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Delta, keys.Represents source.lbr key.2 Delta →
          source.ContextScoped Delta →
          InferMeaning trProj authority.world keys.uvars Delta source ty
  | entry => fallback.Valid authority support entry

namespace InferCacheValid

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {before after : CacheAuthority}
    {support : RunSupport} {entry : CacheEntry} (hle : before ≤ after)
    (h : InferCacheValid keys trProj fallback before support entry) :
    InferCacheValid keys trProj fallback after support entry := by
  cases entry with
  | expr kind key value =>
      cases kind with
      | infer | inferOnly =>
          intro source hsource haddr Delta hctx hscoped
          exact (h source hsource haddr Delta hctx hscoped).mono hle.world
      | whnf | whnfNoDelta | whnfNoDeltaCheap | whnfCore | whnfCoreCheap =>
          exact fallback.mono hle h
  | defEq | defEqFailure | unfold | natSuccStuck | isProp | isRec |
      recursor | recMajors | blockPeer | blockResult =>
      exact fallback.mono hle h

theorem expr {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {ty source : KExpr .anon}
    (hkind : kind.IsInfer)
    (h : InferCacheValid keys trProj fallback authority support
      (.expr kind key ty))
    (hsource : support source) (haddr : source.addr = key.1)
    {Delta : KVLCtx} (hctx : keys.Represents source.lbr key.2 Delta)
    (hscoped : source.ContextScoped Delta) :
    InferMeaning trProj authority.world keys.uvars Delta source ty := by
  cases hkind <;> exact h source hsource haddr Delta hctx hscoped

end InferCacheValid

/-- Overlay K2's inference meanings on the already-selected cache semantics. -/
def inferCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := InferCacheValid keys trProj fallback
  mono := InferCacheValid.mono
  Equiv := fallback.Equiv
  equivEquivalence := fallback.equivEquivalence
  equivMono := fallback.equivMono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err
  blockSuccess := by
    intro authority support block h
    exact fallback.blockSuccess authority support block h
  blockSuccessSound := by
    intro authority support block h
    exact fallback.blockSuccessSound authority support block h

namespace CacheProvenance

theorem inferMeaning {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {ty source : KExpr .anon}
    (h : CacheProvenance (inferCacheSemantics keys trProj fallback)
      authority support (.expr kind key ty))
    (hkind : kind.IsInfer) (hsource : support source)
    (haddr : source.addr = key.1) {Delta : KVLCtx}
    (hctx : keys.Represents source.lbr key.2 Delta)
    (hscoped : source.ContextScoped Delta) :
    InferMeaning trProj authority.world keys.uvars Delta source ty :=
  InferCacheValid.expr hkind h.valid hsource haddr hctx hscoped

theorem inferMeaningOfMatches {keys : WhnfContextKeys}
    {trProj : RawProjRel} {fallback : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {kind : ExprCacheKind} {key : Address × Address}
    {ty source : KExpr .anon} {s : TcState .anon} {Delta : KVLCtx}
    (h : CacheProvenance (inferCacheSemantics keys trProj fallback)
      authority support (.expr kind key ty))
    (hkind : kind.IsInfer) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Delta source key)
    (hscoped : source.ContextScoped Delta) :
    InferMeaning trProj authority.world keys.uvars Delta source ty :=
  h.inferMeaning hkind hsource hmatch.sourceAddr hmatch.2.1 hscoped

end CacheProvenance

namespace CacheInvariant

theorem inferHitOfMatches {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {env : KEnv .anon} {kind : ExprCacheKind}
    {key : Address × Address} {ty source : KExpr .anon}
    {s : TcState .anon} {Delta : KVLCtx}
    (h : CacheInvariant (inferCacheSemantics keys trProj fallback)
      authority support env)
    (hhit : env.HasCacheEntry (.expr kind key ty))
    (hkind : kind.IsInfer) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Delta source key)
    (hscoped : source.ContextScoped Delta) :
    InferMeaning trProj authority.world keys.uvars Delta source ty :=
  (h.hit hhit).inferMeaningOfMatches hkind hsource hmatch hscoped

end CacheInvariant

end Ix.Tc
