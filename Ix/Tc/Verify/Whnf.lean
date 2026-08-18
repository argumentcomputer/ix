import Ix.Tc.Verify.Ctx
import Ix.Tc.Verify.Inductive
import Ix.Tc.Verify.Run
import Ix.Tc.Verify.State

/-!
# WHNF soundness boundary

This file starts K1 at the semantic boundary shared by reduction, caches, and
the recursive method knot.  It intentionally does not identify a context
hash with a typing context by fiat.  `WhnfContextKeys.Represents` is the one
named ghost relation whose production implementation must be connected to
`TcM.ctxAddrForLbr`; K2 supplies the suffix-sufficiency transport theorem.

The semantic payload is already concrete: `WhnfMeaning` says that source and
result have structural `TrKExprS` translations in the same `KVLCtx`, and that
those translations are definitionally equal in the current Theory world.
Consequently a cache hit is useful only after supplying both its finite
source witness and the represented context.  Address equality alone carries
no semantic meaning.

K1 has five expression-cache policies.  The inference caches are excluded
from this layer and continue through a caller-supplied fallback semantics;
K2 replaces that fallback with their exact typing contracts.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)
open Std (HashSet)

/-! ## Concrete reduction meaning -/

/-- Theory meaning of one concrete reduction result.  Both terms retain a
structural translation witness; their translations may differ, but must be
definitionally equal in the same world and mixed local context. -/
def WhnfMeaning (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Δ : KVLCtx) (source result : KExpr .anon) : Prop :=
  ∃ sourceV resultV,
    TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV ∧
    TrKExprS world.venv uvars world.nameOf trProj Δ result resultV ∧
    world.venv.IsDefEqU uvars Δ.toCtx sourceV resultV

namespace WhnfMeaning

/-- A translated, well-formed expression has the reflexive reduction
meaning.  Keeping the WF premise explicit prevents an arbitrary raw syntax
node from entering the semantic cache contract. -/
theorem refl {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {ve : VExpr}
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e ve)
    (hwf : VExpr.WF world.venv uvars Δ.toCtx ve) :
    WhnfMeaning trProj world uvars Δ e e :=
  ⟨ve, ve, htr, htr, hwf⟩

/-- Reduction meaning is symmetric at the semantic level.  This does not
claim the operational WHNF relation is symmetric. -/
theorem symm {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {source result : KExpr .anon}
    (h : WhnfMeaning trProj world uvars Δ source result) :
    WhnfMeaning trProj world uvars Δ result source := by
  obtain ⟨sourceV, resultV, hsource, hresult, hdefeq⟩ := h
  exact ⟨resultV, sourceV, hresult, hsource, hdefeq.symm⟩

/-- A certified reduction remains certified when the trusted Theory world
grows.  `VerifyWorld.LE` fixes `nameOf`, so both structural translations are
transported without changing their address interpretation. -/
theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after) {uvars : Nat} {Δ : KVLCtx}
    {source result : KExpr .anon}
    (h : WhnfMeaning trProj before uvars Δ source result) :
    WhnfMeaning trProj after uvars Δ source result := by
  obtain ⟨sourceV, resultV, hsource, hresult, hdefeq⟩ := h
  refine ⟨sourceV, resultV, ?_, ?_, hdefeq.mono hle.venv⟩
  · simpa only [← hle.nameOf] using hsource.mono hle.venv
  · simpa only [← hle.nameOf] using hresult.mono hle.venv

end WhnfMeaning

/-! ## Cache-policy partition -/

/-- The five semantic policies implemented by the WHNF expression caches.
The policy records operational strength; every policy has the same C1
soundness consequence (`WhnfMeaning`). -/
inductive WhnfCachePolicy where
  | full
  | noDelta
  | noDeltaCheap
  | core
  | coreCheap
  deriving Repr, DecidableEq

namespace ExprCacheKind

/-- Classify exactly the K1 cache families.  Inference caches are K2. -/
def whnfPolicy? : ExprCacheKind → Option WhnfCachePolicy
  | .whnf => some .full
  | .whnfNoDelta => some .noDelta
  | .whnfNoDeltaCheap => some .noDeltaCheap
  | .whnfCore => some .core
  | .whnfCoreCheap => some .coreCheap
  | .infer | .inferOnly => none

@[simp] theorem whnfPolicy?_whnf :
    ExprCacheKind.whnf.whnfPolicy? = some .full := rfl

@[simp] theorem whnfPolicy?_whnfNoDelta :
    ExprCacheKind.whnfNoDelta.whnfPolicy? = some .noDelta := rfl

@[simp] theorem whnfPolicy?_whnfNoDeltaCheap :
    ExprCacheKind.whnfNoDeltaCheap.whnfPolicy? = some .noDeltaCheap := rfl

@[simp] theorem whnfPolicy?_whnfCore :
    ExprCacheKind.whnfCore.whnfPolicy? = some .core := rfl

@[simp] theorem whnfPolicy?_whnfCoreCheap :
    ExprCacheKind.whnfCoreCheap.whnfPolicy? = some .coreCheap := rfl

@[simp] theorem whnfPolicy?_infer :
    ExprCacheKind.infer.whnfPolicy? = none := rfl

@[simp] theorem whnfPolicy?_inferOnly :
    ExprCacheKind.inferOnly.whnfPolicy? = none := rfl

/-- Proof-relevant membership in the K1 cache partition. -/
inductive IsWhnf : ExprCacheKind → Prop
  | whnf : IsWhnf .whnf
  | whnfNoDelta : IsWhnf .whnfNoDelta
  | whnfNoDeltaCheap : IsWhnf .whnfNoDeltaCheap
  | whnfCore : IsWhnf .whnfCore
  | whnfCoreCheap : IsWhnf .whnfCoreCheap

theorem isWhnf_iff {kind : ExprCacheKind} :
    kind.IsWhnf ↔ ∃ policy, kind.whnfPolicy? = some policy := by
  cases kind <;> constructor
  · intro _
    exact ⟨.full, rfl⟩
  · intro _
    exact .whnf
  · intro _
    exact ⟨.noDelta, rfl⟩
  · intro _
    exact .whnfNoDelta
  · intro _
    exact ⟨.noDeltaCheap, rfl⟩
  · intro _
    exact .whnfNoDeltaCheap
  · intro _
    exact ⟨.core, rfl⟩
  · intro _
    exact .whnfCore
  · intro _
    exact ⟨.coreCheap, rfl⟩
  · intro _
    exact .whnfCoreCheap
  · intro h
    cases h
  · rintro ⟨policy, h⟩
    cases h
  · intro h
    cases h
  · rintro ⟨policy, h⟩
    cases h

end ExprCacheKind

/-! ## Context-key interpretation and exact cache semantics -/

/-- Ghost interpretation of suffix-aware context addresses.  `Represents`
may relate one key to several definitionally equal contexts; K1 cache
validity is deliberately quantified over every represented context.  K2
constructs this model from `ctxAddrForLbr` plus suffix sufficiency. -/
structure WhnfContextKeys where
  uvars : Nat
  /-- `Represents lbr key Δ` interprets `key` as the suffix requested at
  loose-bvar radius `lbr`.  The radius is part of the cache key's semantic
  domain even though it is compressed into the emitted digest. -/
  Represents : UInt64 → Address → KVLCtx → Prop

namespace WhnfContextKeys

/-- Closed expressions use the distinguished empty-context key. -/
def closed (uvars : Nat) : WhnfContextKeys where
  uvars := uvars
  Represents lbr key Δ := lbr = 0 ∧ key = emptyCtxAddr ∧ Δ = []

@[simp] theorem closed_represents {uvars : Nat} {lbr : UInt64} {key : Address}
    {Δ : KVLCtx} :
    (closed uvars).Represents lbr key Δ ↔
      lbr = 0 ∧ key = emptyCtxAddr ∧ Δ = [] :=
  Iff.rfl

/-- A represented semantic context tied to the actual production cache-key
computation in a concrete state.  Constructing this witness—not merely
postulating `Represents`—is the K1/K2 context-key proof obligation. -/
def Matches (keys : WhnfContextKeys) (trProj : RawProjRel)
    (world : VerifyWorld) (s : TcState .anon) (Δ : KVLCtx)
    (source : KExpr .anon) (key : Address × Address) : Prop :=
  CtxRecon world.venv keys.uvars world.nameOf trProj s Δ ∧
    keys.Represents source.lbr key.2 Δ ∧
    ∃ s', TcM.whnfKey source s = .ok key s'

end WhnfContextKeys

/-- Exact state frame of suffix-key computation.  The memo table may grow;
every other checker-state field is fixed.  In particular, this is stronger
than merely saying the environment and logical context are unchanged. -/
def ContextKeyFrame (before after : TcState .anon) : Prop :=
  after = { before with ctxAddrCache := after.ctxAddrCache }

/-- Exact state frame of an `InternM` computation lifted through
`TcM.runIntern`: only the intern table may change. -/
def InternUpdateFrame (before after : TcState .anon) : Prop :=
  after = { before with env := { before.env with intern := after.env.intern } }

/-- The empty projection relation satisfies every structural closure law
vacuously.  This is the canonical K1 fixture interpretation for fragments
that contain no projection nodes. -/
theorem RawProjRel.none_ok (env : Lean4Lean.VEnv) (uvars : Nat) :
    TrProjOK env uvars RawProjRel.none := by
  constructor <;> intros <;> contradiction

namespace TcM

@[simp] theorem ctxAddrForLbr_zero (s : TcState .anon) :
    TcM.ctxAddrForLbr 0 s = .ok emptyCtxAddr s := by
  rfl

/-- With no legacy de-Bruijn frames, every suffix request denotes the empty
context and does not populate the memo table.  Fvar frames are intentionally
irrelevant: `ctxAddrForLbr` keys only the legacy stack. -/
theorem ctxAddrForLbr_empty {s : TcState .anon}
    (hempty : s.ctx.isEmpty = true) (lbr : UInt64) :
    TcM.ctxAddrForLbr lbr s = .ok emptyCtxAddr s := by
  unfold TcM.ctxAddrForLbr
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [hempty]
  rfl

/-- Closed expressions compute the distinguished empty-context key without
mutating even the context-address memo. -/
theorem whnfKey_closed {source : KExpr .anon} {s : TcState .anon}
    (hclosed : source.lbr = 0) :
    TcM.whnfKey source s = .ok (source.addr, emptyCtxAddr) s := by
  unfold TcM.whnfKey
  rw [hclosed]
  change EStateM.bind (TcM.ctxAddrForLbr 0)
    (fun addr => pure (source.addr, addr)) s = _
  unfold EStateM.bind
  rw [TcM.ctxAddrForLbr_zero]
  rfl

/-- The first component produced by the concrete WHNF-key computation is
the source expression's address, independent of suffix hashing and its memo
state. -/
theorem whnfKey_fst {s s' : TcState .anon} {source : KExpr .anon}
    {key : Address × Address}
    (h : TcM.whnfKey source s = .ok key s') :
    key.1 = source.addr := by
  unfold TcM.whnfKey at h
  change EStateM.bind (TcM.ctxAddrForLbr source.lbr)
    (fun addr => pure (source.addr, addr)) s = .ok key s' at h
  unfold EStateM.bind at h
  split at h
  · cases h
    rfl
  · contradiction

/-- The second component and post-state of a successful WHNF-key run come
from the underlying suffix-address computation exactly. -/
theorem whnfKey_ctx {s s' : TcState .anon} {source : KExpr .anon}
    {key : Address × Address}
    (h : TcM.whnfKey source s = .ok key s') :
    TcM.ctxAddrForLbr source.lbr s = .ok key.2 s' := by
  unfold TcM.whnfKey at h
  change EStateM.bind (TcM.ctxAddrForLbr source.lbr)
    (fun addr => pure (source.addr, addr)) s = .ok key s' at h
  unfold EStateM.bind at h
  split at h
  · next addr after hctx =>
    cases h
    exact hctx
  · contradiction

end TcM

namespace WhnfContextKeys.Matches

theorem sourceAddr {keys : WhnfContextKeys} {trProj : RawProjRel}
    {world : VerifyWorld} {s : TcState .anon} {Δ : KVLCtx}
    {source : KExpr .anon} {key : Address × Address}
    (h : keys.Matches trProj world s Δ source key) :
    source.addr = key.1 := by
  obtain ⟨_, _, s', hkey⟩ := h
  exact (TcM.whnfKey_fst hkey).symm

end WhnfContextKeys.Matches

namespace CacheSemantics

/-- Minimal fallback used by reducer-only verification slices: cached block
errors remain replayable, and a cached success is accepted exactly when its
immutable block catalog entry is nonempty and every exact member is trusted.
Every non-block semantic family is rejected. -/
def blockResults : CacheSemantics where
  Valid authority _ entry :=
    match entry with
    | .blockResult block (.ok ()) => authority.world.AcceptedBlock block
    | .blockResult _ (.error _) => True
    | _ => False
  mono := by
    intro before after support entry hle h
    cases entry with
    | blockResult block result =>
      cases result with
      | ok value =>
        cases value
        exact h.mono hle.world
      | error => trivial
    | _ => exact h
  Equiv _ _ := Eq
  equivEquivalence := by
    intro authority support
    exact ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  equivMono := by
    intro before after support left right hle h
    exact h
  blockError := by
    intro authority support block err
    trivial
  blockSuccess := by
    intro authority support block h
    exact h
  blockSuccessSound := by
    intro authority support block h
    exact h

/-- Compatibility spelling retained for existing K1/K2 clients.  Unlike its
pre-E0 definition, successful block verdicts now have the exact sound meaning
specified by `blockResults`. -/
abbrev blockErrorsOnly : CacheSemantics := blockResults

end CacheSemantics

/-- Validity owned by the operational recursion-classifier cache.

An `.isRec` entry is permitted exactly when its address names a trusted
anonymous declaration.  The cached Boolean intentionally has no stronger
meaning: `true` is also used as a conservative re-entrancy marker and may
survive a declaration-discovery error, while any struct-eta success reached
through `false` is justified independently by the checked iota semantic
boundary.  The fallback owns every other cache family. -/
def IsRecCacheValid (fallback : CacheSemantics)
    (authority : CacheAuthority) (support : RunSupport) : CacheEntry → Prop
  | .isRec ind _ =>
      ∃ id : KId .anon, authority.world.trusted id ∧ id.addr = ind
  | entry => fallback.Valid authority support entry

namespace IsRecCacheValid

/-- Trusted classifier addresses remain trusted when the semantic world
grows; all other entries inherit the fallback's monotonicity. -/
theorem mono {fallback : CacheSemantics}
    {before after : CacheAuthority} {support : RunSupport}
    {entry : CacheEntry} (hle : before ≤ after)
    (h : IsRecCacheValid fallback before support entry) :
    IsRecCacheValid fallback after support entry := by
  cases entry with
  | isRec ind value =>
      obtain ⟨id, htrusted, haddr⟩ := h
      exact ⟨id, hle.world.trusted htrusted, haddr⟩
  | expr | defEq | defEqFailure | unfold | natSuccStuck | isProp |
      recursor | recMajors | blockPeer | blockResult =>
      exact fallback.mono hle h

/-- Any Boolean for a trusted anonymous inductive address is accepted by the
classifier cache contract. -/
theorem trusted {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {ind : KId .anon} {value : Bool}
    (htrusted : authority.world.trusted ind) :
    IsRecCacheValid fallback authority support (.isRec ind.addr value) :=
  ⟨ind, htrusted, rfl⟩

end IsRecCacheValid

/-- Overlay the operational recursion-classifier family on an arbitrary
fallback cache semantics. -/
def isRecCacheSemantics (fallback : CacheSemantics) : CacheSemantics where
  Valid := IsRecCacheValid fallback
  mono := IsRecCacheValid.mono
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

/-- Exact K1 validity for one tagged entry.  The fallback owns every non-K1
cache family.  A WHNF entry must be sound for every finite-support source
whose address is its first key component and every context represented by
its second component. -/
def WhnfCacheValid (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .expr .whnf key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents source.lbr key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfNoDelta key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents source.lbr key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfNoDeltaCheap key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents source.lbr key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfCore key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents source.lbr key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfCoreCheap key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents source.lbr key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .natSuccStuck _ => True
  | entry => fallback.Valid authority support entry

namespace WhnfCacheValid

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {before after : CacheAuthority}
    {support : RunSupport} {entry : CacheEntry} (hle : before ≤ after)
    (h : WhnfCacheValid keys trProj fallback before support entry) :
    WhnfCacheValid keys trProj fallback after support entry := by
  cases entry with
  | expr kind key value =>
    cases kind with
    | whnf | whnfNoDelta | whnfNoDeltaCheap | whnfCore | whnfCoreCheap =>
      intro source hsource haddr Δ hctx
      exact (h source hsource haddr Δ hctx).mono hle.world
    | infer | inferOnly =>
      exact fallback.mono hle h
  | natSuccStuck => trivial
  | defEq | defEqFailure | unfold | isProp | isRec |
      recursor | recMajors | blockPeer | blockResult =>
    exact fallback.mono hle h

/-- Project the concrete reduction meaning from any of the five K1 cache
families. -/
theorem expr {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {value source : KExpr .anon}
    (hkind : kind.IsWhnf)
    (h : WhnfCacheValid keys trProj fallback authority support
      (.expr kind key value))
    (hsource : support source) (haddr : source.addr = key.1)
    {Δ : KVLCtx} (hctx : keys.Represents source.lbr key.2 Δ) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value := by
  cases hkind <;> exact h source hsource haddr Δ hctx

/-- A stuck-successor marker carries no positive reduction claim.  Its
semantic component is therefore unconditional; finite support and trusted
reference authorization remain mandatory in `CacheProvenance`. -/
theorem natSuccStuck {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address × Address} :
    WhnfCacheValid keys trProj fallback authority support
      (.natSuccStuck key) := by
  trivial

end WhnfCacheValid

/-- Overlay the exact K1 meanings on an existing semantic family. -/
def whnfCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := WhnfCacheValid keys trProj fallback
  mono := WhnfCacheValid.mono
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

/-- Construct K1 provenance for a negative successor marker.  Unlike a
cached expression result, the marker needs no Theory reduction witness; it
still records a supported source address and proves that every supported
source sharing that address refers only to trusted declarations. -/
theorem whnfNatSuccStuck
    {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {world : VerifyWorld}
    {support : RunSupport} {key : Address × Address}
    (hsupported : support.HasExprAddr key.1)
    (hreferences : ∀ {id},
      CacheEntry.SourceReferences support key.1 id → world.trusted id) :
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support (.natSuccStuck key) := by
  refine ⟨hsupported, ?_, WhnfCacheValid.natSuccStuck
    (keys := keys) (trProj := trProj) (fallback := fallback)
    (authority := CacheAuthority.stable world) (support := support)
    (key := key)⟩
  intro id href
  exact .inl (hreferences href)

/-- A provenance-certified K1 hit exposes concrete Theory reduction
meaning; support and dependency facts remain available in `h`. -/
theorem whnfMeaning {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {value source : KExpr .anon}
    (h : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      authority support (.expr kind key value))
    (hkind : kind.IsWhnf) (hsource : support source)
    (haddr : source.addr = key.1) {Δ : KVLCtx}
    (hctx : keys.Represents source.lbr key.2 Δ) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value := by
  exact WhnfCacheValid.expr hkind h.valid hsource haddr hctx

/-- Operationally matched form of `whnfMeaning`: the concrete key execution
supplies the address equality and represented context together. -/
theorem whnfMeaningOfMatches {keys : WhnfContextKeys}
    {trProj : RawProjRel} {fallback : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {kind : ExprCacheKind} {key : Address × Address}
    {value source : KExpr .anon} {s : TcState .anon} {Δ : KVLCtx}
    (h : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      authority support (.expr kind key value))
    (hkind : kind.IsWhnf) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Δ source key) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value :=
  h.whnfMeaning hkind hsource hmatch.sourceAddr hmatch.2.1

end CacheProvenance

namespace CacheInvariant

/-- Physical hit plus the exact K1 cache invariant yields its Theory
meaning. -/
theorem whnfHit {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {env : KEnv .anon} {kind : ExprCacheKind}
    {key : Address × Address} {value source : KExpr .anon}
    (h : CacheInvariant (whnfCacheSemantics keys trProj fallback)
      authority support env)
    (hhit : env.HasCacheEntry (.expr kind key value))
    (hkind : kind.IsWhnf) (hsource : support source)
    (haddr : source.addr = key.1) {Δ : KVLCtx}
    (hctx : keys.Represents source.lbr key.2 Δ) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value :=
  (h.hit hhit).whnfMeaning hkind hsource haddr hctx

/-- Physical-hit form using the concrete key computation/context match. -/
theorem whnfHitOfMatches {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {env : KEnv .anon} {kind : ExprCacheKind}
    {key : Address × Address} {value source : KExpr .anon}
    {s : TcState .anon} {Δ : KVLCtx}
    (h : CacheInvariant (whnfCacheSemantics keys trProj fallback)
      authority support env)
    (hhit : env.HasCacheEntry (.expr kind key value))
    (hkind : kind.IsWhnf) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Δ source key) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value :=
  (h.hit hhit).whnfMeaningOfMatches hkind hsource hmatch

end CacheInvariant

/-! ## Conditional recursive-method interface -/

/-- The theorem layers used by K1. `structuralNoAccel` is deliberately
restricted to syntax-directed fixtures: it pins the acceleration gate but
does not claim that the state's primitive table is the production anon
table. The two production layers both bind every observable table address to
`PrimAddrs.canonical`; `noAccel` additionally pins the gate, while
`accelerated` permits native helpers and hence requires `NativeOracle` at
their successful branches. -/
inductive WhnfLayer where
  | structuralNoAccel
  | noAccel
  | accelerated
  deriving Repr, DecidableEq

namespace Primitives

/-- Erase an anon primitive table to exactly the addresses observed by the
kernel. `Primitives` omits the two PProd entries that live only in
`PrimAddrs`; those components are fixed directly to the canonical table. -/
def addressTable (p : Primitives .anon) : PrimAddrs where
  nat := p.nat.addr
  natZero := p.natZero.addr
  natSucc := p.natSucc.addr
  natAdd := p.natAdd.addr
  natPred := p.natPred.addr
  natSub := p.natSub.addr
  natMul := p.natMul.addr
  natPow := p.natPow.addr
  natGcd := p.natGcd.addr
  natMod := p.natMod.addr
  natDiv := p.natDiv.addr
  natBitwise := p.natBitwise.addr
  natBeq := p.natBeq.addr
  natBle := p.natBle.addr
  natLand := p.natLand.addr
  natLor := p.natLor.addr
  natXor := p.natXor.addr
  natShiftLeft := p.natShiftLeft.addr
  natShiftRight := p.natShiftRight.addr
  boolType := p.boolType.addr
  boolTrue := p.boolTrue.addr
  boolFalse := p.boolFalse.addr
  string := p.string.addr
  stringMk := p.stringMk.addr
  charType := p.charType.addr
  charMk := p.charMk.addr
  charOfNat := p.charOfNat.addr
  stringOfList := p.stringOfList.addr
  stringToByteArray := p.stringToByteArray.addr
  byteArrayEmpty := p.byteArrayEmpty.addr
  list := p.list.addr
  listNil := p.listNil.addr
  listCons := p.listCons.addr
  eq := p.eq.addr
  eqRefl := p.eqRefl.addr
  quotType := p.quotType.addr
  quotCtor := p.quotCtor.addr
  quotLift := p.quotLift.addr
  quotInd := p.quotInd.addr
  reduceBool := p.reduceBool.addr
  reduceNat := p.reduceNat.addr
  eagerReduce := p.eagerReduce.addr
  systemPlatformNumBits := p.systemPlatformNumBits.addr
  systemPlatformGetNumBits := p.systemPlatformGetNumBits.addr
  subtypeVal := p.subtypeVal.addr
  natDecLe := p.natDecLe.addr
  natDecEq := p.natDecEq.addr
  natDecLt := p.natDecLt.addr
  decidableRec := p.decidableRec.addr
  decidableIsTrue := p.decidableIsTrue.addr
  decidableIsFalse := p.decidableIsFalse.addr
  natLeOfBleEqTrue := p.natLeOfBleEqTrue.addr
  natNotLeOfNotBleEqTrue := p.natNotLeOfNotBleEqTrue.addr
  natEqOfBeqEqTrue := p.natEqOfBeqEqTrue.addr
  natNeOfBeqEqFalse := p.natNeOfBeqEqFalse.addr
  fin := p.fin.addr
  boolNoConfusion := p.boolNoConfusion.addr
  int := p.int.addr
  intOfNat := p.intOfNat.addr
  intNegSucc := p.intNegSucc.addr
  intAdd := p.intAdd.addr
  intSub := p.intSub.addr
  intMul := p.intMul.addr
  intNeg := p.intNeg.addr
  intEmod := p.intEmod.addr
  intEdiv := p.intEdiv.addr
  intBmod := p.intBmod.addr
  intBdiv := p.intBdiv.addr
  intNatAbs := p.intNatAbs.addr
  intPow := p.intPow.addr
  intDecEq := p.intDecEq.addr
  intDecLe := p.intDecLe.addr
  intDecLt := p.intDecLt.addr
  punit := p.punit.addr
  pprod := PrimAddrs.canonical.pprod
  pprodMk := PrimAddrs.canonical.pprodMk
  natRec := p.natRec.addr
  natCasesOn := p.natCasesOn.addr
  bitVec := p.bitVec.addr
  bitVecToNat := p.bitVecToNat.addr
  bitVecOfNat := p.bitVecOfNat.addr
  bitVecUlt := p.bitVecUlt.addr
  decidableDecide := p.decidableDecide.addr
  ltLt := p.ltLt.addr
  ofNatOfNat := p.ofNatOfNat.addr
  unit := p.unit.addr
  punitSizeOf1 := p.punitSizeOf1.addr
  sizeOfSizeOf := p.sizeOfSizeOf.addr
  stringBack := p.stringBack.addr
  stringLegacyBack := p.stringLegacyBack.addr
  stringUtf8ByteSize := p.stringUtf8ByteSize.addr
  stringAppend := p.stringAppend.addr
  stringDecEq := p.stringDecEq.addr

/-- The production anon primitive condition. It constrains every address the
kernel can observe, while deliberately ignoring diagnostic name payloads. -/
def CanonicalAnon (p : Primitives .anon) : Prop :=
  p.addressTable = PrimAddrs.canonical

/-- The table installed by `TcState.ofEnvAnon` and the lazy anon driver is
canonical by construction. -/
theorem ofAnonAddrs_canonical :
    CanonicalAnon Primitives.ofAnonAddrs := by
  simp only [CanonicalAnon, addressTable, Primitives.ofAnonAddrs,
    Primitives.ofResolve]

end Primitives

def WhnfLayer.StateOK : WhnfLayer → TcState .anon → Prop
  | .structuralNoAccel, s => s.noAccel = true
  | .noAccel, s =>
      s.noAccel = true ∧ s.prims.CanonicalAnon
  | .accelerated, s => s.prims.CanonicalAnon

/-- Fixed-world state invariant for one method call.  Ordinary reduction
does not promote declarations.  Cache/intern coherence, concrete/ghost
context reconciliation, and the selected acceleration policy are all
preserved on success and error. -/
def WhnfStateInv (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Δ : KVLCtx) (s : TcState .anon) : Prop :=
  KernelStateWF semantics trProj world support s ∧
    CtxRecon world.venv uvars world.nameOf trProj s Δ ∧
    layer.StateOK s

namespace WhnfStateInv

/-- Transport a fixed-state method invariant across ghost-only trusted-world
growth.  The larger-world core is supplied by the promotion theorem; context,
cache, and equivalence facts are monotone because promotion fixes the catalog
and address-to-name map. -/
theorem rebaseWorld
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {beforeWorld afterWorld : VerifyWorld}
    {support : RunSupport} {uvars : Nat} {Δ : KVLCtx}
    {s : TcState .anon}
    (hle : beforeWorld ≤ afterWorld)
    (hcore : TcStateWF trProj s afterWorld)
    (h : WhnfStateInv layer semantics trProj beforeWorld support uvars Δ s) :
    WhnfStateInv layer semantics trProj afterWorld support uvars Δ s := by
  refine ⟨h.1.rebaseWorld hle hcore, ?_, h.2.2⟩
  simpa only [← hle.nameOf] using h.2.1.mono hle.venv

/-- Changing only operational bookkeeping fields preserves the complete
fixed-world WHNF invariant.  The explicit field equations keep fuel and
instrumentation updates from being mistaken for semantic state changes. -/
theorem of_semantic_fields_eq
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {before after : TcState .anon}
    (h : WhnfStateInv layer semantics trProj world support uvars Δ before)
    (henv : after.env = before.env)
    (hctx : after.ctx = before.ctx)
    (hlet : after.letVals = before.letVals)
    (hnum : after.numLetBindings = before.numLetBindings)
    (hlctx : after.lctx = before.lctx)
    (hprims : after.prims = before.prims)
    (hnoAccel : after.noAccel = before.noAccel)
    (hequiv : after.equivManager = before.equivManager) :
    WhnfStateInv layer semantics trProj world support uvars Δ after := by
  rcases h with ⟨hkernel, hrecon, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hkernel.core.of_env_eq henv
      internSupport := by simpa only [henv] using hkernel.internSupport
      caches := by simpa only [henv] using hkernel.caches
      equivalences := by simpa only [hequiv] using hkernel.equivalences }
  · exact hrecon.of_fields_eq hctx hlet hnum hlctx (by simp [henv])
  · cases layer with
    | structuralNoAccel =>
        simpa only [WhnfLayer.StateOK, hnoAccel] using hlayer
    | noAccel =>
        simpa only [WhnfLayer.StateOK, hprims, hnoAccel] using hlayer
    | accelerated =>
        simpa only [WhnfLayer.StateOK, hprims] using hlayer

/-- Replace only the equivalence manager after separately proving its
semantic representation invariant.  This is the sole state bridge used by
DefEq manager queries, path compression, and justified union operations. -/
theorem setEquivManager
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    (h : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (manager : EquivManager)
    (hmanager : EquivManager.WF
      (semantics.Equiv (CacheAuthority.stable world) support) manager) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with equivManager := manager} := by
  rcases h with ⟨hkernel, hctx, hlayer⟩
  exact ⟨{
      core := hkernel.core.of_env_eq rfl
      internSupport := hkernel.internSupport
      caches := hkernel.caches
      equivalences := hmanager },
    hctx.of_fields_eq rfl rfl rfl rfl (by simp), by
      cases layer <;> simpa [WhnfLayer.StateOK] using hlayer⟩

/-- The production no-acceleration invariant fixes the complete anon
primitive table, not merely the `noAccel` Boolean gate. -/
theorem noAccel_primitives
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    (h : WhnfStateInv .noAccel semantics trProj world support uvars Δ s) :
    s.prims.CanonicalAnon :=
  h.2.2.2

/-- Accelerated production runs use the same canonical anon primitive table.
Only the native execution gate differs. -/
theorem accelerated_primitives
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    (h : WhnfStateInv .accelerated semantics trProj world support uvars Δ s) :
    s.prims.CanonicalAnon :=
  h.2.2

/-- Rebudgeting recursive fuel is operational bookkeeping only.  Naming this
frame is useful for Nat's open-argument reducer, which lowers the budget before
a recursive WHNF callback and restores the caller-visible remainder on every
callback outcome. -/
theorem set_recFuel
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    (h : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (fuel : UInt64) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with recFuel := fuel} :=
  h.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl

end WhnfStateInv

namespace ContextKeyFrame

/-- Populating the suffix-key memo preserves the complete K1 invariant.
The proof projects the exact frame rather than treating the memo operation as
pure; this catches future writes to context, environment, fuel, or flags. -/
theorem whnfStateInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {before after : TcState .anon}
    (hframe : ContextKeyFrame before after)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ before) :
    WhnfStateInv layer semantics trProj world support uvars Δ after := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  have henv : after.env = before.env := by
    simpa [ContextKeyFrame] using congrArg TcState.env hframe
  have hctxEq : after.ctx = before.ctx := by
    simpa [ContextKeyFrame] using congrArg TcState.ctx hframe
  have hlet : after.letVals = before.letVals := by
    simpa [ContextKeyFrame] using congrArg TcState.letVals hframe
  have hnum : after.numLetBindings = before.numLetBindings := by
    simpa [ContextKeyFrame] using congrArg TcState.numLetBindings hframe
  have hlctx : after.lctx = before.lctx := by
    simpa [ContextKeyFrame] using congrArg TcState.lctx hframe
  have hnoAccel : after.noAccel = before.noAccel := by
    simpa [ContextKeyFrame] using congrArg TcState.noAccel hframe
  have hprims : after.prims = before.prims := by
    simpa [ContextKeyFrame] using congrArg TcState.prims hframe
  have hequiv : after.equivManager = before.equivManager := by
    simpa [ContextKeyFrame] using congrArg TcState.equivManager hframe
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hkernel.core.of_env_eq henv
      internSupport := by simpa [henv] using hkernel.internSupport
      caches := by simpa [henv] using hkernel.caches
      equivalences := by simpa [hequiv] using hkernel.equivalences }
  · exact hctx.of_fields_eq hctxEq hlet hnum hlctx (by simp [henv])
  · cases layer with
    | structuralNoAccel =>
        simpa [WhnfLayer.StateOK, hnoAccel] using hlayer
    | noAccel =>
        simpa [WhnfLayer.StateOK, hprims, hnoAccel] using hlayer
    | accelerated =>
        simpa [WhnfLayer.StateOK, hprims] using hlayer

end ContextKeyFrame

namespace InternUpdateFrame

/-- Doing no interning is the identity intern-only frame. -/
@[refl] theorem refl (s : TcState .anon) : InternUpdateFrame s s := by
  rfl

/-- Sequential intern-only computations compose to one intern-only frame. -/
theorem trans {s₀ s₁ s₂ : TcState .anon}
    (h₁ : InternUpdateFrame s₀ s₁)
    (h₂ : InternUpdateFrame s₁ s₂) : InternUpdateFrame s₀ s₂ := by
  unfold InternUpdateFrame at *
  rw [h₂, h₁]

/-- Intern-table growth preserves the context and acceleration components of
the K1 invariant once the post-state kernel invariant has been re-established.
Keeping the kernel premise explicit lets the finite-support walker proofs
supply its new intern-table coherence and coverage facts. -/
theorem whnfStateInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {before after : TcState .anon}
    (hframe : InternUpdateFrame before after)
    (hkernel : KernelStateWF semantics trProj world support after)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ before) :
    WhnfStateInv layer semantics trProj world support uvars Δ after := by
  rcases hI with ⟨_, hctx, hlayer⟩
  have hctxEq : after.ctx = before.ctx := by
    simpa [InternUpdateFrame] using congrArg TcState.ctx hframe
  have hlet : after.letVals = before.letVals := by
    simpa [InternUpdateFrame] using congrArg TcState.letVals hframe
  have hnum : after.numLetBindings = before.numLetBindings := by
    simpa [InternUpdateFrame] using congrArg TcState.numLetBindings hframe
  have hlctx : after.lctx = before.lctx := by
    simpa [InternUpdateFrame] using congrArg TcState.lctx hframe
  have hnext : after.env.nextFVarId = before.env.nextFVarId := by
    simpa [InternUpdateFrame] using
      congrArg (fun s : TcState .anon => s.env.nextFVarId) hframe
  have hnoAccel : after.noAccel = before.noAccel := by
    simpa [InternUpdateFrame] using congrArg TcState.noAccel hframe
  have hprims : after.prims = before.prims := by
    simpa [InternUpdateFrame] using congrArg TcState.prims hframe
  refine ⟨hkernel, ?_, ?_⟩
  · exact hctx.of_fields_eq hctxEq hlet hnum hlctx (by simp [hnext])
  · cases layer with
    | structuralNoAccel =>
        simpa [WhnfLayer.StateOK, hnoAccel] using hlayer
    | noAccel =>
        simpa [WhnfLayer.StateOK, hprims, hnoAccel] using hlayer
    | accelerated =>
        simpa [WhnfLayer.StateOK, hprims] using hlayer

end InternUpdateFrame

namespace TcM

/-- Lift an exact `InternM` specification to the complete K1 state invariant.
This is the common state bridge for beta/zeta walkers: the intern table may
grow, but contexts, flags, loaded declarations, and semantic caches frame. -/
theorem runIntern_whnf_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {x : InternM .anon α} {expected : α}
    {s : TcState .anon}
    (hspec : ∀ it : InternTable .anon, it.WF →
      support.CoversIntern it →
      (x it).1 = expected ∧ (x it).2.WF ∧
        support.CoversIntern (x it).2) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.runIntern x)
      (fun result s' => result = expected ∧ InternUpdateFrame s s') := by
  intro hI
  have hkernel := hI.1
  rcases hrun : x s.env.intern with ⟨result, intern⟩
  have hpost := hspec s.env.intern hkernel.core.intern hkernel.internSupport
  rw [hrun] at hpost
  simp only [TcM.runIntern, hrun]
  have hframe : InternUpdateFrame s
      { s with env := { s.env with intern } } := rfl
  have hkernel' : KernelStateWF semantics trProj world support
      { s with env := { s.env with intern } } :=
    ⟨hkernel.core.of_consts_eq rfl hpost.2.1,
      hpost.2.2, hkernel.caches.of_intern_update,
      hkernel.equivalences⟩
  exact ⟨hframe.whnfStateInv hkernel' hI, hpost.1, hframe⟩

/-- Executable form of `runIntern_whnf_wf`.  `InternM` cannot throw, so an
inhabited pre-state yields a concrete successful state and the exact expected
result, while retaining the complete invariant and intern-only frame. -/
theorem runIntern_whnf_eval {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {x : InternM .anon α} {expected : α}
    {s : TcState .anon}
    (hspec : ∀ it : InternTable .anon, it.WF →
      support.CoversIntern it →
      (x it).1 = expected ∧ (x it).2.WF ∧
        support.CoversIntern (x it).2)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s', TcM.runIntern x s = .ok expected s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  rcases hrun : x s.env.intern with ⟨result, intern⟩
  have hwf := TcM.runIntern_whnf_wf (s := s) hspec hI
  simp only [TcM.runIntern, hrun] at hwf
  refine ⟨{ s with env := { s.env with intern } }, ?_, hwf.1, hwf.2.2⟩
  simp only [TcM.runIntern, hrun]
  rw [hwf.2.1]

/-- Direct expression interning needs only finite support for the requested
node and collision freedom on that same run domain.  This is the request-list
independent form used by primitive reducers whose generated syntax is already
enumerated by their verification context. -/
theorem internExpr_support_spec
    {support : RunSupport} (hcollision : support.CollisionFree)
    {e : KExpr .anon} (hsupport : support e)
    (it : InternTable .anon) (hwf : it.WF)
    (hcover : support.CoversIntern it) :
    (it.internExpr e).1 = e ∧
      (it.internExpr e).2.WF ∧
      support.CoversIntern (it.internExpr e).2 := by
  have hkcf : KExpr.KeyCollisionFree
      (fun value => it.ExprSupport value ∨ value = e) :=
    KExpr.keyCollisionFree_anon.mpr <|
      hcollision.expr.mono fun value hvalue =>
        hvalue.elim (hcover.expr value) fun h => h ▸ hsupport
  have hcanon : (it.internExpr e).1 = e := by
    have heq := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at heq
  refine ⟨hcanon, hwf.internExpr e, ?_⟩
  constructor
  · intro value hvalue
    rcases InternTable.ExprSupport.of_internExpr hvalue with hvalue | rfl
    · exact hcover.expr value hvalue
    · exact hsupport
  · intro u hu
    exact hcover.univ u (by
      simpa only [InternTable.UnivSupport,
        InternTable.internExpr_univs] using hu)

/-- Hoare form of direct primitive-result interning over a finite collision-
free support.  The returned expression is the requested anon node exactly,
and only the intern table may change. -/
theorem intern_whnf_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {s : TcState .anon}
    (hcollision : support.CollisionFree) (hsupport : support e) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.intern e)
      (fun result s' => result = e ∧ InternUpdateFrame s s') := by
  exact TcM.runIntern_whnf_wf
    (x := internExprM e) (expected := e)
    (fun it hwf hcover =>
      internExpr_support_spec hcollision hsupport it hwf hcover)

/-- Executable form of `intern_whnf_wf`; direct interning cannot throw. -/
theorem intern_whnf_eval {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {s : TcState .anon}
    (hcollision : support.CollisionFree) (hsupport : support e)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s', TcM.intern e s = .ok e s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  exact TcM.runIntern_whnf_eval
    (x := internExprM e) (expected := e)
    (fun it hwf hcover =>
      internExpr_support_spec hcollision hsupport it hwf hcover) hI

private theorem get_bind_run {α : Type} (s : TcState .anon)
    (f : TcState .anon → TcM .anon α) :
    ((get >>= f : TcM .anon α) s) = f s s := rfl

/-- Exact evaluator for the successful legacy-let read.  The array premise
is deliberately the production `getElem!` observation; context
reconciliation supplies it from the safer optional read in the combined
zeta theorem below. -/
theorem lookupLetVal_eval {idx : UInt64}
    {val result : KExpr .anon} {s s' : TcState .anon}
    (hidx : idx.toNat < s.ctx.size)
    (hval : s.letVals[s.ctx.size - 1 - idx.toNat]! = some val)
    (hlift : TcM.runIntern (lift val (idx + 1) 0) s = .ok result s') :
    TcM.lookupLetVal idx s = .ok (some result) s' := by
  unfold TcM.lookupLetVal
  rw [get_bind_run]
  rw [if_neg (by omega)]
  rw [hval]
  change EStateM.bind (TcM.runIntern (lift val (idx + 1) 0))
    (fun r => pure (some r)) s = _
  unfold EStateM.bind
  rw [hlift]
  rfl

/-- A successful `lookupLetVal` miss is state-pure.  The only stateful arm
    runs `lift` and always wraps its successful result in `some`; therefore it
    cannot witness an `.ok none` outcome, even if the lift changes state. -/
theorem lookupLetVal_none_state {idx : UInt64}
    {s s' : TcState .anon}
    (h : TcM.lookupLetVal idx s = .ok none s') : s' = s := by
  unfold TcM.lookupLetVal at h
  rw [get_bind_run] at h
  split at h
  · cases h
    rfl
  · simp only [letFun] at h
    cases hval : s.letVals[s.ctx.size - 1 - idx.toNat]! with
    | none =>
      rw [hval] at h
      cases h
      rfl
    | some val =>
      rw [hval] at h
      change EStateM.bind (TcM.runIntern (lift val (idx + 1) 0))
        (fun r => pure (some r)) s = _ at h
      unfold EStateM.bind at h
      cases hrun : TcM.runIntern (lift val (idx + 1) 0) s <;>
        rw [hrun] at h <;> cases h

/-- Implementation-level frame theorem for `ctxAddrForLbr`.  It is
polymorphic in the invariant: clients only need to prove closure under the
single permitted memo-table write. -/
theorem ctxAddrForLbr_wf {I : TcState .anon → Prop}
    (hframe : ∀ {before after}, I before → ContextKeyFrame before after →
      I after) (lbr : UInt64) (s : TcState .anon) :
    TcM.WF I s (TcM.ctxAddrForLbr lbr)
      (fun _ s' => ContextKeyFrame s s') := by
  unfold TcM.ctxAddrForLbr
  apply TcM.WF.bind (Q₁ := fun read s' => read = s ∧ s' = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read before ⟨rfl, rfl⟩
  simp only [letFun]
  split
  · exact TcM.WF.pure fun _ => rfl
  · split
    · exact TcM.WF.pure fun _ => rfl
    · refine TcM.WF.bind
        (Q₁ := fun _ after => ContextKeyFrame before after) ?_ ?_
      · exact TcM.WF.modifyGet
          (fun hI => hframe hI
            (show ContextKeyFrame before _ from rfl))
          (fun _ => show ContextKeyFrame before _ from rfl)
      · intro _ after hafter
        exact TcM.WF.pure fun _ => hafter

/-- `whnfKey` preserves K1 state and fixes the expression-address component
of the returned key. -/
theorem whnfKey_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {source : KExpr .anon}
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.whnfKey source)
      (fun key s' => key.1 = source.addr ∧ ContextKeyFrame s s') := by
  unfold TcM.whnfKey
  apply TcM.WF.bind
    (TcM.ctxAddrForLbr_wf
      (fun hI hframe => hframe.whnfStateInv hI) source.lbr s)
  intro addr after hframe
  exact TcM.WF.pure fun _ => ⟨rfl, hframe⟩

/-- Operational context-match constructor.  `hrep` is deliberately the only
remaining ghost obligation: K1 cannot infer suffix sufficiency from a hash,
and K2 will discharge it from the concrete context-closure algorithm. -/
theorem whnfKey_matches_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {keys : WhnfContextKeys}
    {Δ : KVLCtx} {source : KExpr .anon} {s : TcState .anon}
    (hrep : ∀ key s',
      CtxRecon world.venv keys.uvars world.nameOf trProj s Δ →
      TcM.whnfKey source s = .ok key s' →
        keys.Represents source.lbr key.2 Δ) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support keys.uvars Δ) s
      (TcM.whnfKey source)
      (fun key s' => keys.Matches trProj world s Δ source key ∧
        ContextKeyFrame s s') := by
  intro hI
  have hwf := TcM.whnfKey_wf (layer := layer) (semantics := semantics)
    (trProj := trProj) (world := world) (support := support)
    (uvars := keys.uvars) (Δ := Δ) (source := source) (s := s) hI
  match hrun : TcM.whnfKey source s with
  | .ok key s' =>
      rw [hrun] at hwf
      exact ⟨hwf.1,
        ⟨⟨hI.2.1, hrep key s' hI.2.1 hrun, ⟨s', hrun⟩⟩, hwf.2.2⟩⟩
  | .error err s' =>
      rw [hrun] at hwf
      exact hwf

/-- `isLetVar` is a read-only prefix test.  Recording its exact state frame
    lets the public WHNF dispatch theorem handle legacy variables without an
    extra operational oracle. -/
theorem isLetVar_wf {I : TcState .anon -> Prop} (idx : UInt64)
    (s : TcState .anon) :
    TcM.WF I s (TcM.isLetVar idx)
      (fun _ s' => s' = s) := by
  unfold TcM.isLetVar
  apply TcM.WF.bind
    (Q₁ := fun read s' => read = s ∧ s' = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read s' ⟨rfl, rfl⟩
  simp only
  split <;> exact TcM.WF.pure (fun _ => rfl)

/-- Step journaling has no semantic state effect, whether enabled or not. -/
theorem stepTrace_whnf_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} (tag : String) (payload : Unit -> String)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.stepTrace tag payload) (fun _ _ => True) := by
  unfold TcM.stepTrace
  apply TcM.WF.bind
    (Q₁ := fun read s' => read = s ∧ s' = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read s' ⟨rfl, rfl⟩
  simp only
  split <;> exact TcM.WF.pure (fun _ => trivial)

/-- A statistics update preserves WHNF state whenever its semantic fields
    frame.  The production call/miss counter updates instantiate every
    premise by reflexivity. -/
theorem bumpStats_whnf_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} (f : TcState .anon -> TcState .anon)
    (henv : forall s, (f s).env = s.env)
    (hctx : forall s, (f s).ctx = s.ctx)
    (hlet : forall s, (f s).letVals = s.letVals)
    (hnum : forall s, (f s).numLetBindings = s.numLetBindings)
    (hlctx : forall s, (f s).lctx = s.lctx)
    (hprims : forall s, (f s).prims = s.prims)
    (hnoAccel : forall s, (f s).noAccel = s.noAccel)
    (hequiv : forall s, (f s).equivManager = s.equivManager)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.bumpStats f) (fun _ _ => True) := by
  unfold TcM.bumpStats
  apply TcM.WF.bind
    (Q₁ := fun read s' => read = s ∧ s' = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro read s' ⟨rfl, rfl⟩
  split
  · exact TcM.WF.modifyGet
      (fun hI => hI.of_semantic_fields_eq (henv s') (hctx s') (hlet s')
        (hnum s') (hlctx s') (hprims s') (hnoAccel s') (hequiv s'))
      (fun _ => trivial)
  · exact TcM.WF.pure (fun _ => trivial)

/-! ### Exact instrumentation and fuel equations -/

/-- A disabled step journal is an exact state-preserving no-op. -/
theorem stepTrace_disabled {s : TcState .anon}
    (h : s.stepTrace = false) (tag : String) (payload : Unit → String) :
    TcM.stepTrace tag payload s = .ok () s := by
  unfold TcM.stepTrace
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [h]
  rfl

/-- Disabled statistics make every counter update an exact no-op. -/
theorem bumpStats_disabled {s : TcState .anon}
    (h : s.stats = false) (f : TcState .anon → TcState .anon) :
    TcM.bumpStats f s = .ok () s := by
  unfold TcM.bumpStats
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [h]
  rfl

/-- A positive fuel counter is decremented exactly once. -/
theorem tick_success {s : TcState .anon}
    (h : (s.recFuel == 0) = false) :
    TcM.tick s = .ok () {s with recFuel := s.recFuel - 1} := by
  unfold TcM.tick
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only [h, Bool.false_eq_true, if_false]
  rfl

end TcM

namespace RunAssumptions

/-- One certified expression-intern request returns the requested raw
expression exactly, preserves the complete K1 invariant, and changes only the
intern table.  Collision freedom and finite support are supplied by the
execution-indexed request rather than assumed for an arbitrary expression. -/
theorem internExpr_whnf_eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon}
    (hmem : WalkerRequest.internExpr e ∈ requests)
    {s : TcState .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s', TcM.intern e s = .ok e s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  exact TcM.runIntern_whnf_eval
    (fun _ hwf hsup => h.internExpr_spec hmem hwf hsup) hI

/-- The verified single-substitution walker preserves the complete K1
invariant.  This is the explicit-let sibling of `simulSubst_whnf_wf`:
production substitutes the let value into its body while only the intern
table may grow. -/
theorem subst_whnf_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {body arg : KExpr .anon} {depth : UInt64}
    (hmem : WalkerRequest.subst body arg depth ∈ requests)
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.runIntern (subst body arg depth))
      (fun result s' => result = KExpr.substSpec body arg depth ∧
        InternUpdateFrame s s') :=
  TcM.runIntern_whnf_wf fun _ hwf hsup =>
    h.subst_spec hmem hwf hsup

/-- Concrete-success projection of `subst_whnf_wf`, used by the production
explicit-let step. -/
theorem subst_whnf_eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {body arg : KExpr .anon} {depth : UInt64}
    (hmem : WalkerRequest.subst body arg depth ∈ requests)
    {s : TcState .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s', TcM.runIntern (subst body arg depth) s =
        .ok (KExpr.substSpec body arg depth) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' :=
  TcM.runIntern_whnf_eval
    (fun _ hwf hsup => h.subst_spec hmem hwf hsup) hI

/-- The verified lifting walker preserves the complete K1 invariant.  This
is the legacy-zeta sibling of `simulSubst_whnf_wf`: the stored let value is
rebased to the current de Bruijn depth while only the intern table may grow. -/
theorem lift_whnf_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {shift cutoff : UInt64}
    (hmem : WalkerRequest.lift e shift cutoff ∈ requests)
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.runIntern (lift e shift cutoff))
      (fun result s' => result = KExpr.liftSpec e shift cutoff ∧
        InternUpdateFrame s s') :=
  TcM.runIntern_whnf_wf fun _ hwf hsup =>
    h.lift_spec hmem hwf hsup

/-- Concrete-success projection of `lift_whnf_wf`, used to rewrite the
production `lookupLetVal` branch. -/
theorem lift_whnf_eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {shift cutoff : UInt64}
    (hmem : WalkerRequest.lift e shift cutoff ∈ requests)
    {s : TcState .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s', TcM.runIntern (lift e shift cutoff) s =
        .ok (KExpr.liftSpec e shift cutoff) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' :=
  TcM.runIntern_whnf_eval
    (fun _ hwf hsup => h.lift_spec hmem hwf hsup) hI

/-- The verified simultaneous-substitution walker preserves the complete K1
invariant, not merely intern-table coherence.  Its request membership keeps
finite collision/support and UInt64 resource assumptions tied to an actual
execution certificate. -/
theorem simulSubst_whnf_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    (hmem : WalkerRequest.simulSubst body substs depth ∈ requests)
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.runIntern (simulSubst body substs depth))
      (fun result s' =>
        result = KExpr.simulSubstSpec body substs depth ∧
        InternUpdateFrame s s') :=
  TcM.runIntern_whnf_wf fun _ hwf hsup =>
    h.simulSubst_spec hmem hwf hsup

/-- Concrete-success projection of `simulSubst_whnf_wf`, suitable for
rewriting the production beta branch. -/
theorem simulSubst_whnf_eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    (hmem : WalkerRequest.simulSubst body substs depth ∈ requests)
    {s : TcState .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s',
      TcM.runIntern (simulSubst body substs depth) s =
        .ok (KExpr.simulSubstSpec body substs depth) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' :=
  TcM.runIntern_whnf_eval
    (fun _ hwf hsup => h.simulSubst_spec hmem hwf hsup) hI

end RunAssumptions

/-- Successful reduction postcondition relative to the structural
translation of the input. -/
def WhnfPost (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Δ : KVLCtx) (sourceV : VExpr)
    (result : KExpr .anon) : Prop :=
  ∃ resultV,
    TrKExprS world.venv uvars world.nameOf trProj Δ result resultV ∧
    world.venv.IsDefEqU uvars Δ.toCtx sourceV resultV

/-- Theory-side assumptions needed to turn a structural translation into a
well-formed expression.  Literal typing and projection closure are explicit;
the ordered environment comes from `VerifyWorld.venvWF`. -/
structure WhnfTheory (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) : Prop where
  literalWF : ∀ literal, world.venv.ContainsLits literal →
    VExpr.WF world.venv uvars [] (VExpr.trLiteral literal)
  projections : TrProjOK world.venv uvars trProj

namespace WhnfTheory

theorem exprWF {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars) {s : TcState .anon}
    {Δ : KVLCtx} (hctx :
      CtxRecon world.venv uvars world.nameOf trProj s Δ)
    {e : KExpr .anon} {ve : VExpr}
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e ve) :
    VExpr.WF world.venv uvars Δ.toCtx ve :=
  htr.wf world.venvWF.ordered theory.literalWF theory.projections.wf
    hctx.wf

/-- Compose two concrete reduction meanings.  The middle concrete term may
have two different structural translations; `TrKExprS.uniq` bridges them
before Theory transitivity is applied.  This is the semantic loop invariant
used by the forthcoming bounded WHNF proofs. -/
theorem transMeaning {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {Δ : KVLCtx} (hΔ : KVLCtx.WF world.venv uvars Δ)
    {source middle result : KExpr .anon}
    (h₁ : WhnfMeaning trProj world uvars Δ source middle)
    (h₂ : WhnfMeaning trProj world uvars Δ middle result) :
    WhnfMeaning trProj world uvars Δ source result := by
  obtain ⟨sourceV, middleV₁, hsource, hmiddle₁, hdefeq₁⟩ := h₁
  obtain ⟨middleV₂, resultV, hmiddle₂, hresult, hdefeq₂⟩ := h₂
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hΔ
  have hmiddle := hmiddle₁.uniq world.venvWF theory.literalWF
    theory.projections hctx hmiddle₂
  refine ⟨sourceV, resultV, hsource, hresult, ?_⟩
  exact hdefeq₁.trans world.venvWF hΔ <|
    hmiddle.trans world.venvWF hΔ hdefeq₂

end WhnfTheory

namespace WhnfMeaning

/-- Legacy de-Bruijn zeta meaning.  `lookupLetVal` and `KVLCtx.find?`
perform the same re-basing: the concrete walker lifts the stored value by
`idx + 1`, while the translation context inlines that lifted value at the
variable use site. -/
theorem zetaVar {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {s : TcState .anon} {Δ : KVLCtx}
    {idx : UInt64} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {ty val : KExpr .anon}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj s Δ)
    (htp : TrProjOK world.venv uvars trProj)
    (hidx : idx.toNat < s.ctx.size) (hsz : s.ctx.size < UInt64.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some (some val))
    (hbig : Δ.bvars + val.size < UInt64.size) :
    WhnfMeaning trProj world uvars Δ (.var idx name md)
      (KExpr.liftSpec val (idx + 1) 0) := by
  obtain ⟨e, A, hfind, hresult⟩ := hctx.lookupLetVal
    world.venvWF.ordered htp hidx hsz hty hov hbig
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.var idx name md) e := .var hfind
  have hwf : VExpr.WF world.venv uvars Δ.toCtx e :=
    ⟨A, hctx.wf.find?_wf world.venvWF.ordered hfind⟩
  exact ⟨e, e, hsource, hresult, hwf⟩

/-- Let-bound fvar zeta meaning under the exact condition needed by the
production branch: the stored value has no loose legacy bvars, so returning
it without a shift agrees with the mixed-context lookup. -/
theorem zetaFVar {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {s : TcState .anon} {Δ : KVLCtx}
    {fv : FVarId} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {declName : Mode.anon.F Name} {ty val : KExpr .anon}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj s Δ)
    (htp : TrProjOK world.venv uvars trProj)
    (hfind : s.lctx.find? fv = some (.ldecl declName ty val))
    (hcon : KExpr.Constructed val) (hclosed : val.lbr = 0)
    (hbig : Δ.bvars + val.size < UInt64.size) :
    WhnfMeaning trProj world uvars Δ (.fvar fv name md) val := by
  obtain ⟨e, A, hresolve, hresult⟩ := hctx.lctxFindLetVal
    world.venvWF.ordered htp hfind hcon hclosed hbig
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.fvar fv name md) e := .fvar hresolve
  have hwf : VExpr.WF world.venv uvars Δ.toCtx e :=
    ⟨A, hctx.wf.find?_wf world.venvWF.ordered hresolve⟩
  exact ⟨e, e, hsource, hresult, hwf⟩

/-- One explicit-let zeta step.  `TrKExprS` already inlines the source let
into `bodyV`; `TrKExprS.inst_let_lbr` proves that production's concrete
`substSpec` result translates to that same Theory expression.  Thus the
semantic equality is reflexive, but only after the mixed-context
instantiation theorem has connected the two concrete terms. -/
theorem letE {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {s : TcState .anon} {Δ : KVLCtx}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj s Δ)
    {name : Mode.anon.F Name} {ty val body : KExpr .anon}
    {nondep : Bool} {info : ExprInfo .anon} {bodyV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.letE name ty val body nondep info) bodyV)
    (hvalCon : KExpr.Constructed val)
    (hbig : val.lbr.toNat + val.size + body.size < UInt64.size) :
    WhnfMeaning trProj world uvars Δ
      (.letE name ty val body nondep info) (KExpr.substSpec body val 0) := by
  let .letE hvalTy hty hval hbody := hsource
  have hresult : TrKExprS world.venv uvars world.nameOf trProj Δ
      (KExpr.substSpec body val 0) bodyV :=
    TrKExprS.inst_let_lbr world.venvWF.ordered theory.projections.weakN
      hvalCon hbody hval hbig
  exact ⟨bodyV, bodyV, hsource, hresult,
    Lean4Lean.VEnv.IsDefEqU.refl (theory.exprWF hctx hresult)⟩

/-- One concrete beta step.  The result is the same `substSpec` computed by
the verified substitution walker; the proof uses `TrKExprS.instN` and the
Theory's beta rule, so no syntactic address equality stands in for reduction
meaning.  The resource bound is exactly the walker's UInt64 safety premise. -/
theorem beta {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (projections : TrProjOK world.venv uvars trProj)
    {Δ : KVLCtx} {nm : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {lamMd appMd : ExprInfo .anon}
    {A bodyV argV B : VExpr} {u : Lean4Lean.VLevel}
    (hty : TrKExprS world.venv uvars world.nameOf trProj Δ ty A)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam A) :: Δ) body bodyV)
    (harg : TrKExprS world.venv uvars world.nameOf trProj Δ arg argV)
    (hA : world.venv.HasType uvars Δ.toCtx A (.sort u))
    (hbodyTy : world.venv.HasType uvars (A :: Δ.toCtx) bodyV B)
    (hargTy : world.venv.HasType uvars Δ.toCtx argV A)
    (hbig : Δ.bvars + body.size + arg.size < UInt64.size) :
    WhnfMeaning trProj world uvars Δ
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (KExpr.substSpec body arg 0) := by
  have hlam : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.lam nm bi ty body lamMd) (.lam A bodyV) :=
    .lam ⟨u, hA⟩ hty hbody
  have hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (.app (.lam A bodyV) argV) :=
    .app (Lean4Lean.VEnv.HasType.lam hA hbodyTy) hargTy hlam harg
  have hresult : TrKExprS world.venv uvars world.nameOf trProj Δ
      (KExpr.substSpec body arg 0) (bodyV.inst argV) :=
    TrKExprS.instN world.venvWF.ordered projections.weakN
      projections.instN harg hargTy hbody (.zero) rfl hbig
  exact ⟨_, _, hsource, hresult, ⟨_, .beta hbodyTy hargTy⟩⟩

/-- Bridge the Theory beta rule's single-substitution result to the exact
singleton simultaneous-substitution specification used by production WHNF.
The equality remains explicit: it is a pure walker lemma, not a consequence
of semantic definitional equality. -/
theorem betaSimul {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {nm : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {lamMd appMd : ExprInfo .anon}
    (hbeta : WhnfMeaning trProj world uvars Δ
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (KExpr.substSpec body arg 0))
    (hspec : KExpr.simulSubstSpec body #[arg] 0 =
      KExpr.substSpec body arg 0) :
    WhnfMeaning trProj world uvars Δ
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (KExpr.simulSubstSpec body #[arg] 0) := by
  rw [hspec]
  exact hbeta

/-- A projection result has reduction meaning when the source projection and
the concrete result translate to the same Theory expression selected by the
explicit projection relation.  This theorem deliberately consumes a
`trProj` witness; successful execution of the syntax-directed production
helper cannot manufacture one. -/
theorem projection {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {id : KId .anon} {field : UInt64}
    {value result : KExpr .anon} {info : ExprInfo .anon}
    {structName : Lean.Name} {valueV resultV : VExpr}
    (hname : world.nameOf id.addr = some structName)
    (hvalue :
      TrKExprS world.venv uvars world.nameOf trProj Δ value valueV)
    (hproj : trProj Δ.toCtx structName field.toNat valueV resultV)
    (hresult :
      TrKExprS world.venv uvars world.nameOf trProj Δ result resultV)
    (hwf : VExpr.WF world.venv uvars Δ.toCtx resultV) :
    WhnfMeaning trProj world uvars Δ (.prj id field value info) result :=
  ⟨resultV, resultV, .prj hname hvalue hproj, hresult, hwf⟩

/-- Turn one exact registered Theory computation equation into reduction
meaning.  The caller must translate the concrete source and result to the
instantiated left- and right-hand sides; mere membership of a raw recursor
rule does not determine the production argument spine. -/
theorem registeredDefEq {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {source result : KExpr .anon}
    {df : Lean4Lean.VDefEq} {levels : List Lean4Lean.VLevel}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ source
      (df.lhs.instL levels))
    (hresult : TrKExprS world.venv uvars world.nameOf trProj Δ result
      (df.rhs.instL levels))
    (hregistered : world.venv.defeqs df)
    (hlevels : ∀ level ∈ levels, level.WF uvars)
    (harity : levels.length = df.uvars) :
    WhnfMeaning trProj world uvars Δ source result :=
  ⟨_, _, hsource, hresult,
    ⟨_, .extra hregistered hlevels harity⟩⟩

end WhnfMeaning

namespace WhnfPost

theorem refl {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {e : KExpr .anon} {sourceV : VExpr}
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV)
    (hwf : VExpr.WF world.venv uvars Δ.toCtx sourceV) :
    WhnfPost trProj world uvars Δ sourceV e :=
  ⟨sourceV, htr, hwf⟩

/-- Extend a postcondition through one locally sound reduction step.  The
    concrete middle expression may have two structural translations; their
    uniqueness is the only bridge used before Theory transitivity. -/
theorem transMeaning {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {sourceV : VExpr}
    {middle result : KExpr .anon} (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpost : WhnfPost trProj world uvars Delta sourceV middle)
    (hstep : WhnfMeaning trProj world uvars Delta middle result) :
    WhnfPost trProj world uvars Delta sourceV result := by
  obtain ⟨middleV1, hmiddle1, hdefeq1⟩ := hpost
  obtain ⟨middleV2, resultV, hmiddle2, hresult, hdefeq2⟩ := hstep
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have hmiddle := hmiddle1.uniq world.venvWF theory.literalWF
    theory.projections hctx hmiddle2
  refine ⟨resultV, hresult, ?_⟩
  exact hdefeq1.trans world.venvWF hDelta <|
    hmiddle.trans world.venvWF hDelta hdefeq2

/-- Recover the concrete source/result reduction meaning when the caller
    retains the source translation used to state `WhnfPost`. -/
theorem meaning {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
    {sourceV : VExpr} {result : KExpr .anon}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hpost : WhnfPost trProj world uvars Delta sourceV result) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨resultV, hresult, hdefeq⟩ := hpost
  exact ⟨sourceV, resultV, hsource, hresult, hdefeq⟩

end WhnfPost

/-- Successful inference callback postcondition used inside WHNF's K/struct
fallbacks.  K2 proves this field for the concrete method table. -/
def InferPost (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Δ : KVLCtx) (sourceV : VExpr)
    (ty : KExpr .anon) : Prop :=
  ∃ tyV,
    TrKExpr world.venv uvars world.nameOf trProj Δ ty tyV ∧
    world.venv.HasType uvars Δ.toCtx sourceV tyV

namespace Methods

/-- Semantic closure of all six recursive back-edges at one declaration
universe count.

Every recursive method call made while checking a declaration stays at that
declaration's `uvars`; only the local context changes.  Indexing this record
by `uvars` therefore matches production execution and permits the cache
semantics to interpret universe-sensitive WHNF keys honestly.  The older
unindexed `Methods.WF` below is retained as the strictly stronger
all-universe package used by compatibility statements. -/
structure WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (methods : Methods .anon) : Prop where
  whnf : ∀ {Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnf e)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfCore : ∀ {Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCore e)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfMode : ∀ {Δ s e sourceV} {mode : NatSuccMode},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfMode e mode)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfCoreFlags : ∀ {Δ s e sourceV} {flags : WhnfFlags},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCoreFlags e flags)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  infer : ∀ {Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.infer e)
      (fun ty _ => support ty ∧ InferPost trProj world uvars Δ sourceV ty)
  isDefEq : ∀ {Δ s a b va vb},
    support a →
    support b →
    TrKExprS world.venv uvars world.nameOf trProj Δ a va →
    TrKExprS world.venv uvars world.nameOf trProj Δ b vb →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Δ.toCtx va vb)

/-- Conditional semantic closure of all six K0 method-table back-edges.
K1 consumes this record while proving WHNF; K2 proves the inference/defeq
fields and closes `methodsN` by induction. -/
structure WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) : Prop where
  whnf : ∀ {uvars Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnf e)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfCore : ∀ {uvars Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCore e)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfMode : ∀ {uvars Δ s e sourceV} {mode : NatSuccMode},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfMode e mode)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  whnfCoreFlags : ∀ {uvars Δ s e sourceV} {flags : WhnfFlags},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCoreFlags e flags)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result)
  infer : ∀ {uvars Δ s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.infer e)
      (fun ty _ => support ty ∧ InferPost trProj world uvars Δ sourceV ty)
  isDefEq : ∀ {uvars Δ s a b va vb},
    support a →
    support b →
    TrKExprS world.venv uvars world.nameOf trProj Δ a va →
    TrKExprS world.venv uvars world.nameOf trProj Δ b vb →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Δ.toCtx va vb)

namespace WF

/-- Forget the all-universe strength of the legacy method contract and use it
at the universe count of the active checker run. -/
theorem atUvars {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    (h : Methods.WF layer semantics trProj world support methods)
    (uvars : Nat) :
    Methods.WFAt layer semantics trProj world support uvars methods where
  whnf := h.whnf
  whnfCore := h.whnfCore
  whnfMode := h.whnfMode
  whnfCoreFlags := h.whnfCoreFlags
  infer := h.infer
  isDefEq := h.isDefEq

end WF

end Methods

/-! ## Projection/iota semantic boundary -/

/-- Conditional semantic boundary for the two inductive structural reducers.

The production helpers are intentionally syntax-directed: a loaded
constructor-shaped constant is enough for them to select a projection field
or recursor rule.  Therefore helper success alone is not semantic evidence.
Each clause additionally requires a structural translation of the original
source and is indexed by the exact callback/helper equations used by the
production branch.

This record is proof debt, not a new axiom.  Projection theory must construct
`projection` from the concrete `trProj` implementation.  Inductive-block
verification must construct `iota` from the registered defeq and the exact
parameter/motive/minor/field/trailing-argument correspondence.  The existing
`RawRecursorRuleRel` records the registered rule but intentionally does not
yet imply that spine correspondence. -/
structure InductiveReductionOracle (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  projection : ∀ {uvars Δ methods s s₁ s₂ id field value wvalue result info
      flags sourceV},
    Methods.WFAt layer semantics trProj world support uvars methods →
    TrKExprS world.venv uvars world.nameOf trProj Δ
      (.prj id field value info) sourceV →
    WhnfStateInv layer semantics trProj world support uvars Δ s →
    (if flags.cheapProj then
        (RecM.whnfCoreFlagsRec value flags).run methods s
      else (RecM.whnfRec value).run methods s) = .ok wvalue s₁ →
    (RecM.tryProjReduce id field wvalue).run methods s₁ =
      .ok (some result) s₂ →
    WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfMeaning trProj world uvars Δ
        (.prj id field value info) result
  iota : ∀ {uvars Δ methods s s₁ s₂ recId us headInfo appInfo f arg args
      result flags sourceV},
    Methods.WFAt layer semantics trProj world support uvars methods →
    TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app f arg appInfo) sourceV →
    WhnfStateInv layer semantics trProj world support uvars Δ s →
    (.app f arg appInfo : KExpr .anon).collectSpine =
      (.const recId us headInfo, args) →
    methods.whnfCoreFlags (.const recId us headInfo) flags s =
      .ok (.const recId us headInfo) s₁ →
    ((.const recId us headInfo : KExpr .anon) !=
      .const recId us headInfo) = false →
    (RecM.tryIotaWithFlags (.app f arg appInfo) flags).run methods s₁ =
      .ok (some result) s₂ →
    WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfMeaning trProj world uvars Δ (.app f arg appInfo) result

namespace RecM

/-- Reader-level Hoare triple conditional on a semantically closed method
table.  Quantification over every `Methods.WF` table is what lets K1 land
before K2 ties the total recursive knot. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Δ : KVLCtx) (s : TcState .anon) (x : RecM .anon α)
    (Q : α → TcState .anon → Prop)
    (E : TcError .anon → TcState .anon → Prop := fun _ _ => True) : Prop :=
  ∀ methods, methods.WFAt layer semantics trProj world support uvars →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (x.run methods) Q E

namespace WF

theorem pure {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {a : α}
    (h : WhnfStateInv layer semantics trProj world support uvars Δ s →
      Q a s) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (pure a) Q E := by
  intro methods hmethods
  exact TcM.WF.pure h

theorem throw {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {err : TcError .anon}
    (h : WhnfStateInv layer semantics trProj world support uvars Δ s →
      E err s) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (throw err) Q E := by
  intro methods hmethods
  exact TcM.WF.throw h

theorem mono {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {Q Q' : α → TcState .anon → Prop}
    {E E' : TcError .anon → TcState .anon → Prop}
    (hx : RecM.WF layer semantics trProj world support uvars Δ s x Q E)
    (hq : ∀ a s', Q a s' → Q' a s')
    (he : ∀ err s', E err s' → E' err s') :
    RecM.WF layer semantics trProj world support uvars Δ s x Q' E' := by
  intro methods hmethods
  exact TcM.WF.mono (hx methods hmethods) hq he

/-- Expose the invariant already guaranteed by a Hoare triple inside its
success postcondition.  This strengthening is useful when a later generated
term is indexed by the concrete callback post-state; the error predicate is
left unchanged so the result composes through ordinary `bind`. -/
theorem withInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : RecM.WF layer semantics trProj world support uvars Δ s x Q E) :
    RecM.WF layer semantics trProj world support uvars Δ s x
      (fun result after =>
        WhnfStateInv layer semantics trProj world support uvars Δ after ∧
          Q result after)
      E := by
  intro methods hmethods hI
  have hpost := hx methods hmethods hI
  match hrun : x.run methods s with
  | .ok result after =>
      rw [hrun] at hpost
      simp only at hpost ⊢
      exact ⟨hpost.1, hpost.1, hpost.2⟩
  | .error err after =>
      rw [hrun] at hpost
      simp only at hpost ⊢
      exact hpost

theorem bind {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {f : α → RecM .anon β}
    {Q₁ : α → TcState .anon → Prop} {Q₂ : β → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : RecM.WF layer semantics trProj world support uvars Δ s x Q₁ E)
    (hf : ∀ a s', Q₁ a s' →
      RecM.WF layer semantics trProj world support uvars Δ s'
        (f a) Q₂ E) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (x >>= f) Q₂ E := by
  intro methods hmethods
  exact TcM.WF.bind (hx methods hmethods) fun a s' ha =>
    hf a s' ha methods hmethods

/-- Reader-level non-backtracking catch.  The handler receives the exact
partial post-state certified by the body, matching `EStateM` rather than a
rollback-style exception transformer. -/
theorem tryCatch {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {handler : TcError .anon → RecM .anon α}
    {Q : α → TcState .anon → Prop}
    {E₁ E₂ : TcError .anon → TcState .anon → Prop}
    (hx : RecM.WF layer semantics trProj world support uvars Δ s x Q E₁)
    (hh : ∀ err s', E₁ err s' →
      RecM.WF layer semantics trProj world support uvars Δ s'
        (handler err) Q E₂) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (tryCatch x handler) Q E₂ := by
  intro methods hmethods
  change TcM.WF
    (WhnfStateInv layer semantics trProj world support uvars Δ) s
    (EStateM.tryCatch (x.run methods)
      (fun err => (handler err).run methods)) Q E₂
  exact TcM.WF.tryCatch (hx methods hmethods) fun err s' herr =>
    hh err s' herr methods hmethods

/-- Lift a verified base `TcM` action through the method-table reader. -/
theorem liftTcM {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {x : TcM .anon alpha} {Q : alpha -> TcState .anon -> Prop}
    {E : TcError .anon -> TcState .anon -> Prop}
    (hx : TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s x Q E) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (liftM x) Q E := by
  intro methods hmethods
  exact hx

/-- Reader-level state observation preserves the K1 invariant exactly. -/
theorem get {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {Q : TcState .anon -> TcState .anon -> Prop}
    {E : TcError .anon -> TcState .anon -> Prop}
    (h : WhnfStateInv layer semantics trProj world support uvars Delta s ->
      Q s s) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (get : RecM .anon (TcState .anon)) Q E := by
  intro methods hmethods
  exact TcM.WF.get h

/-- Reader-level state update rule used by the three WHNF cache shells. -/
theorem modifyGet {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {f : TcState .anon -> alpha × TcState .anon}
    {Q : alpha -> TcState .anon -> Prop}
    {E : TcError .anon -> TcState .anon -> Prop}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s ->
      WhnfStateInv layer semantics trProj world support uvars Delta (f s).2)
    (hQ : WhnfStateInv layer semantics trProj world support uvars Delta s ->
      Q (f s).1 (f s).2) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (modifyGet f : RecM .anon alpha) Q E := by
  intro methods hmethods
  exact TcM.WF.modifyGet hI hQ

theorem modify {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {f : TcState .anon -> TcState .anon}
    {Q : Unit -> TcState .anon -> Prop}
    {E : TcError .anon -> TcState .anon -> Prop}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s ->
      WhnfStateInv layer semantics trProj world support uvars Delta (f s))
    (hQ : WhnfStateInv layer semantics trProj world support uvars Delta s ->
      Q () (f s)) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (modify f : RecM .anon Unit) Q E := by
  intro methods hmethods
  exact TcM.WF.modifyGet hI hQ

end WF

/-- The direct recursive full-WHNF callback inherits the smaller method
table's semantic contract.  Keeping this adapter at `RecM.WF` level lets
helper proofs compose without reopening the reader implementation. -/
theorem whnfRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (hsource : support source)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (whnfRec source)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result) := by
  intro methods hmethods
  exact hmethods.whnf hsource htr

/-- The policy-sensitive recursive WHNF callback inherits the corresponding
method-table contract.  This is the callback used by the successor-collapse
loop, where `.stuck` deliberately prevents recursive successor collapsing. -/
theorem whnfModeRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr} {mode : NatSuccMode}
    (hsource : support source)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (whnfModeRec source mode)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Δ sourceV result) := by
  intro methods hmethods
  exact hmethods.whnfMode hsource htr

/-- Reading the production primitive table is state-transparent.  Naming the
exact reader frame avoids repeatedly unfolding `get` in primitive helpers. -/
theorem prims_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon} :
    RecM.WF layer semantics trProj world support uvars Δ s prims
      (fun result after => result = s.prims ∧ after = s) := by
  unfold prims
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = s ∧ after = s)
    (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
  rintro observed after ⟨rfl, rfl⟩
  exact RecM.WF.pure fun _ => ⟨rfl, rfl⟩

/-- The arithmetic classifier only reads the primitive table. -/
theorem isNatBinArithAddr_inv_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon} (addr : Address) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (isNatBinArithAddr addr) (fun _ after => after = s) := by
  unfold isNatBinArithAddr
  apply RecM.WF.bind (prims_wf (s := s))
  intro prims after hread
  rcases hread with ⟨rfl, rfl⟩
  exact RecM.WF.pure fun _ => rfl

/-- The predicate classifier is likewise an exact state-transparent read. -/
theorem isNatBinPredAddr_inv_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon} (addr : Address) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (isNatBinPredAddr addr) (fun _ after => after = s) := by
  unfold isNatBinPredAddr
  apply RecM.WF.bind (prims_wf (s := s))
  intro prims after hread
  rcases hread with ⟨rfl, rfl⟩
  exact RecM.WF.pure fun _ => rfl

/-- The arithmetic classifier has a concrete, state-transparent execution.
This equation is useful when inverting the production dispatcher: no
classifier outcome or intermediate state has to be postulated. -/
theorem isNatBinArithAddr_eval
    (methods : Methods .anon) (s : TcState .anon) (addr : Address) :
    (isNatBinArithAddr addr).run methods s = .ok
      (addr == s.prims.natAdd.addr || addr == s.prims.natSub.addr
        || addr == s.prims.natMul.addr || addr == s.prims.natDiv.addr
        || addr == s.prims.natMod.addr || addr == s.prims.natPow.addr
        || addr == s.prims.natGcd.addr || addr == s.prims.natLand.addr
        || addr == s.prims.natLor.addr || addr == s.prims.natXor.addr
        || addr == s.prims.natShiftLeft.addr
        || addr == s.prims.natShiftRight.addr) s := by
  rfl

/-- The predicate classifier has a concrete, state-transparent execution. -/
theorem isNatBinPredAddr_eval
    (methods : Methods .anon) (s : TcState .anon) (addr : Address) :
    (isNatBinPredAddr addr).run methods s = .ok
      (addr == s.prims.natBeq.addr || addr == s.prims.natBle.addr) s := by
  rfl

/-- A positive predicate-classifier result identifies one of the two
production predicate addresses. -/
theorem isNatBinPredAddr_true
    {methods : Methods .anon} {s : TcState .anon} {addr : Address}
    (hrun : (isNatBinPredAddr addr).run methods s = .ok true s) :
    addr = s.prims.natBeq.addr ∨ addr = s.prims.natBle.addr := by
  rw [isNatBinPredAddr_eval] at hrun
  have hdecision :
      (addr == s.prims.natBeq.addr || addr == s.prims.natBle.addr) = true := by
    exact EStateM.Result.ok.inj hrun |>.1
  simpa only [Bool.or_eq_true, beq_iff_eq] using hdecision

/-- Nat's shared argument normalizer preserves the complete WHNF invariant
through both execution policies.  Closed/eager arguments use the recursive
WHNF callback directly.  Open arguments temporarily lower `recFuel`, retain
all callback state on error, restore the caller-visible remaining budget, and
turn only depth/fuel exhaustion into `none`.  A successful result carries the
same semantic WHNF meaning as the callback. -/
theorem whnfNatReducerArg_post_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {arg : KExpr .anon} {argV : VExpr}
    (harg : support arg)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ arg argV) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (whnfNatReducerArg arg)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfPost trProj world uvars Δ argV reduced) := by
  unfold whnfNatReducerArg
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = after)
    (RecM.WF.get fun _ => rfl)
  intro observed s₀ hobserved
  subst observed
  split
  · apply RecM.WF.bind (whnfRec_wf harg htr)
    intro reduced s₁ hred
    exact RecM.WF.pure fun _ => hred
  · apply RecM.WF.bind
      (Q₁ := fun observed after => observed = after)
      (RecM.WF.get fun _ => rfl)
    intro saved s₁ hsaved
    subst saved
    simp only [letFun]
    apply RecM.WF.bind
      (Q₁ := fun _ after => after =
        {s₁ with recFuel :=
          (min s₁.recFuel natReducerOpenArgRecFuel)})
    · exact RecM.WF.modify
        (Q := fun _ after => after =
          {s₁ with recFuel :=
            (min s₁.recFuel natReducerOpenArgRecFuel)})
        (f := fun state =>
          {state with
            recFuel := min s₁.recFuel natReducerOpenArgRecFuel})
        (fun hI => hI.set_recFuel _)
        (fun _ => rfl)
    · intro _ limited hlimited
      subst limited
      apply RecM.WF.bind
        (Q₁ := fun result : Except (TcError .anon) (KExpr .anon) =>
          fun _ => match result with
          | .ok reduced =>
              support reduced ∧
                WhnfPost trProj world uvars Δ argV reduced
          | .error _ => True)
      · apply RecM.WF.tryCatch (E₁ := fun _ _ => True)
        · apply RecM.WF.bind (whnfRec_wf harg htr)
          intro reduced after hred
          exact RecM.WF.pure fun _ => hred
        · intro err after _
          exact RecM.WF.pure fun _ => trivial
      · intro result afterCallback hresult
        apply RecM.WF.bind
          (Q₁ := fun observed after => observed = after)
          (RecM.WF.get fun _ => rfl)
        intro observed afterRead hobserved
        subst observed
        apply RecM.WF.bind
          (Q₁ := fun _ restored => restored =
            {afterRead with recFuel := s₁.recFuel -
              (min s₁.recFuel
                (min s₁.recFuel natReducerOpenArgRecFuel -
                  afterRead.recFuel))})
        · exact RecM.WF.modify
            (Q := fun _ restored => restored =
              {afterRead with recFuel := s₁.recFuel -
                (min s₁.recFuel
                  (min s₁.recFuel natReducerOpenArgRecFuel -
                    afterRead.recFuel))})
            (f := fun state =>
              {state with recFuel := s₁.recFuel -
                (min s₁.recFuel
                  (min s₁.recFuel natReducerOpenArgRecFuel -
                    afterRead.recFuel))})
            (fun hI => hI.set_recFuel _)
            (fun _ => rfl)
        · intro _ restored hrestored
          subst restored
          cases result with
          | ok reduced =>
              exact RecM.WF.pure fun _ => hresult
          | error err =>
              cases err <;>
                first
                | exact RecM.WF.pure fun _ => trivial
                | exact RecM.WF.throw fun _ => trivial

/-- Evaluate the shared Nat callback contract at any successful outcome.  In
particular, both production `none` and `some` preserve the complete WHNF
invariant after the open-argument fuel budget has been restored. -/
theorem whnfNatReducerArg_ok_inv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s' : TcState .anon} {arg : KExpr .anon} {argV : VExpr}
    {result : Option (KExpr .anon)}
    (harg : support arg)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ arg argV)
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hrun : (whnfNatReducerArg arg).run methods s = .ok result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s' := by
  have hpost := whnfNatReducerArg_post_wf harg htr methods hmethods hI
  rw [hrun] at hpost
  exact hpost.1

/-- Evaluate the shared Nat callback contract at an error.  The error's
partial state—not the entry state—satisfies the complete invariant after the
open-argument fuel budget has been restored. -/
theorem whnfNatReducerArg_error_inv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s' : TcState .anon} {arg : KExpr .anon} {argV : VExpr}
    {err : TcError .anon}
    (harg : support arg)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ arg argV)
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hrun : (whnfNatReducerArg arg).run methods s = .error err s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s' := by
  have hpost := whnfNatReducerArg_post_wf harg htr methods hmethods hI
  rw [hrun] at hpost
  exact hpost.1

/-- Existential reduction meaning is the translation-independent projection
of `whnfNatReducerArg_post_wf`.  Most outer reducer proofs should use the
stronger theorem so the application arguments retain the translations
obtained from the source spine. -/
theorem whnfNatReducerArg_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {arg : KExpr .anon} {argV : VExpr}
    (harg : support arg)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ arg argV) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (whnfNatReducerArg arg)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Δ arg reduced) := by
  apply RecM.WF.mono (whnfNatReducerArg_post_wf harg htr)
  · intro result after hresult
    cases result with
    | none => trivial
    | some reduced =>
        exact ⟨hresult.1, WhnfPost.meaning htr hresult.2⟩
  · intro _ _ _
    trivial

/-- Generic invariant rule for K0's total bounded-loop driver.  Exhaustion
is explicit in `hexhaust`; every successful `.next` re-establishes `P`, and
every `.done` establishes the final postcondition. -/
theorem runBounded_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx}
    {step : σ → RecM .anon (BoundedStep σ α)}
    {P : σ → Prop} {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hstep : ∀ state s, P state →
      RecM.WF layer semantics trProj world support uvars Δ s (step state)
        (fun action s' => match action with
          | .next next => P next
          | .done result => Q result s') E)
    (hexhaust : ∀ s,
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      E .maxRecDepth s) :
    ∀ fuel state s, P state →
      RecM.WF layer semantics trProj world support uvars Δ s
        (runBounded step fuel state) Q E
  | 0, state, s, hP => by
      rw [runBounded]
      exact RecM.WF.throw (hexhaust s)
  | fuel + 1, state, s, hP => by
      rw [runBounded]
      apply RecM.WF.bind (hstep state s hP)
      intro action s' haction
      cases action with
      | next next =>
        exact runBounded_wf hstep hexhaust fuel next s' haction
      | done result =>
        exact RecM.WF.pure fun _ => haction

/-! ### Semantic bounded-step closure -/

/-- Errors from a bounded semantic loop are classified without conflating
    driver exhaustion with an error raised by the production step. -/
def WhnfLoopError (stepError : TcError .anon -> TcState .anon -> Prop)
    (err : TcError .anon) (s : TcState .anon) : Prop :=
  err = .maxRecDepth ∨ stepError err s

namespace WhnfStep

/-- Semantic admissibility of the expression observed by one loop state.
    This premise is load-bearing: `WhnfStateInv` constrains the checker state,
    but does not make every arbitrary `KExpr` translatable. -/
def Source {sigma : Type} (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (view : sigma -> KExpr .anon) (state : sigma) : Prop :=
  support (view state) ∧
    exists sourceV,
      TrKExprS world.venv uvars world.nameOf trProj Delta (view state) sourceV

/-- Local semantic payload required from one successful bounded step. -/
def Meaning {sigma : Type} (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (view : sigma -> KExpr .anon)
    (state : sigma) (action : BoundedStep sigma (KExpr .anon)) : Prop :=
  match action with
  | .next next =>
      support (view next) ∧
        WhnfMeaning trProj world uvars Delta (view state) (view next)
  | .done result =>
      support result ∧
        WhnfMeaning trProj world uvars Delta (view state) result

/-- Branch-local contract consumed by the bounded-loop closure theorem.
    It is intentionally one iteration wide and requires an actual structural
    translation of the current expression.  Successful `.next` meaning then
    supplies the translation required by the following iteration; this keeps
    unsupported raw syntax out of the semantic loop induction. -/
def WF {sigma : Type} (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (view : sigma -> KExpr .anon)
    (step : sigma -> RecM .anon (BoundedStep sigma (KExpr .anon)))
    (stepError : TcError .anon -> TcState .anon -> Prop) : Prop :=
  forall state s,
    Source trProj world support uvars Delta view state ->
    RecM.WF layer semantics trProj world support uvars Delta s (step state)
      (fun action _ =>
        Meaning trProj world support uvars Delta view state action)
      stepError

end WhnfStep

/-- Execution-indexed semantic certificate for the production structural
WHNF loop.  Its fuel index is the actual fuel presented to `runBounded`.
Every iteration records the exact production equation, the fixed
world/context invariant on both sides, and the local Theory meaning.

This is intentionally stronger than successful raw execution: neither a
callback result nor syntax-directed projection/iota success can manufacture
the `WhnfMeaning` field.  Conversely, zero fuel has no constructor, matching
the production exhaustion error. -/
inductive WhnfCoreTrace (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Δ : KVLCtx) (methods : Methods .anon)
    (flags : WhnfFlags) :
    Nat → KExpr .anon → TcState .anon → KExpr .anon → TcState .anon → Prop
  | done {fuel : Nat} {cur result : KExpr .anon} {s s' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfCoreWithFlagsStep cur flags).run methods s =
        .ok (.done result) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur result →
      WhnfCoreTrace layer semantics trProj world support uvars Δ methods flags
        (fuel + 1) cur s result s'
  | next {fuel : Nat} {cur middle result : KExpr .anon}
      {s s' s'' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfCoreWithFlagsStep cur flags).run methods s =
        .ok (.next middle) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur middle →
      WhnfCoreTrace layer semantics trProj world support uvars Δ methods flags
        fuel middle s' result s'' →
      WhnfCoreTrace layer semantics trProj world support uvars Δ methods flags
        (fuel + 1) cur s result s''

namespace WhnfCoreTrace

/-- Exhaustion cannot be mislabeled as a certified structural reduction. -/
theorem no_zero {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {s s' : TcState .anon} :
    ¬WhnfCoreTrace layer semantics trProj world support uvars Δ methods flags
      0 source s result s' := by
  intro h
  cases h

/-- A local semantic contract is sufficient to reconstruct the exact
    execution-indexed trace for every successful bounded run.  On failure,
    the same induction preserves the K1 invariant and says whether the loop
    exhausted its own bound or the production step raised the error. -/
theorem complete {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {flags : WhnfFlags}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta id
      (fun cur => whnfCoreWithFlagsStep cur flags) stepError)
    {methods : Methods .anon}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    {fuel : Nat} {source : KExpr .anon} {s : TcState .anon}
    (hsource : WhnfStep.Source trProj world support uvars Delta id source)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    match (runBounded (fun cur => whnfCoreWithFlagsStep cur flags)
      fuel source).run methods s with
    | .ok result s' =>
        support result ∧
          WhnfCoreTrace layer semantics trProj world support uvars Delta
            methods flags fuel source s result s'
    | .error err s' =>
        WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
          WhnfLoopError stepError err s' := by
  induction fuel generalizing source s with
  | zero =>
      rw [runBounded]
      exact ⟨hI, Or.inl rfl⟩
  | succ fuel ih =>
      have hlocal := hstep source s hsource methods hmethods hI
      match hrun : (whnfCoreWithFlagsStep source flags).run methods s with
      | .error err s' =>
          rw [hrun] at hlocal
          rw [runBounded, ReaderT.run_bind]
          change match EStateM.bind
            ((whnfCoreWithFlagsStep source flags).run methods) _ s with
            | .ok result s'' =>
                support result ∧
                  WhnfCoreTrace layer semantics trProj world support uvars
                    Delta methods flags (fuel + 1) source s result s''
            | .error err s'' =>
                WhnfStateInv layer semantics trProj world support uvars Delta
                    s'' ∧
                  WhnfLoopError stepError err s''
          unfold EStateM.bind
          rw [hrun]
          exact ⟨hlocal.1, Or.inr hlocal.2⟩
      | .ok action s' =>
          rw [hrun] at hlocal
          cases action with
          | done result =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source
                  result := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfCoreWithFlagsStep source flags).run methods) _ s with
                | .ok result s'' =>
                    support result ∧
                      WhnfCoreTrace layer semantics trProj world support uvars
                        Delta methods flags (fuel + 1) source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              exact ⟨hlocal.2.1,
                .done hI hrun hlocal.1 hlocal.2.2⟩
          | next next =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source
                  next := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              have hnextSource : WhnfStep.Source trProj world support uvars
                  Delta id next := by
                obtain ⟨_, nextV, _, hnext, _⟩ := hmeaning
                exact ⟨hlocal.2.1, nextV, hnext⟩
              have htail := ih (source := next) (s := s') hnextSource hlocal.1
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfCoreWithFlagsStep source flags).run methods) _ s with
                | .ok result s'' =>
                    support result ∧
                      WhnfCoreTrace layer semantics trProj world support uvars
                        Delta methods flags (fuel + 1) source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              simp only
              match htailRun :
                  (runBounded (fun cur => whnfCoreWithFlagsStep cur flags)
                    fuel next).run methods s' with
              | .ok result s'' =>
                  rw [htailRun] at htail
                  exact ⟨htail.1,
                    .next hI hrun hlocal.1 hmeaning htail.2⟩
              | .error err s'' =>
                  rw [htailRun] at htail
                  exact htail

/-- Erase the semantic payload to the exact successful production execution.
This direction is deliberately one-way: raw success alone is not a semantic
certificate. -/
theorem eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {fuel : Nat} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags fuel source s result s') :
    (runBounded (fun cur => whnfCoreWithFlagsStep cur flags) fuel source).run
      methods s = .ok result s' := by
  induction h with
  | done hI hstep hI' hmeaning =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfCoreWithFlagsStep _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      rfl
  | next hI hstep hI' hmeaning htail ih =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfCoreWithFlagsStep _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      exact ih

/-- The first state in a trace satisfies the same fixed K1 invariant carried
by every later state. -/
theorem initialInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {fuel : Nat} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s := by
  cases h <;> assumption

/-- The last state in a trace still satisfies the fixed K1 invariant. -/
theorem finalInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {fuel : Nat} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s' := by
  induction h with
  | done hI hstep hI' hmeaning => exact hI'
  | next hI hstep hI' hmeaning htail ih => exact ih

/-- Compose every local reduction meaning in a trace.  Translation
uniqueness at an intermediate concrete term is discharged by
`WhnfTheory.transMeaning`; no syntactic address equality is assumed. -/
theorem meaning {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {fuel : Nat} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags fuel source s result s') :
    WhnfMeaning trProj world uvars Δ source result := by
  induction h with
  | done hI hstep hI' hmeaning => exact hmeaning
  | next hI hstep hI' hmeaning htail ih =>
      exact theory.transMeaning hI.2.1.wf hmeaning ih

/-- Specialize trace execution to the actual 10,000-fuel uncached driver. -/
theorem uncached_eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags maxWhnfFuel.toNat source s result s') :
    (whnfCoreWithFlagsUncached source flags).run methods s = .ok result s' := by
  unfold whnfCoreWithFlagsUncached
  exact h.eval

/-- K1 structural-loop acceptance package: exact production execution,
initial/final fixed-world invariants, and the transitively composed Theory
meaning. -/
theorem uncached_acceptance {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {flags : WhnfFlags}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (h : WhnfCoreTrace layer semantics trProj world support uvars Δ methods
      flags maxWhnfFuel.toNat source s result s') :
    (whnfCoreWithFlagsUncached source flags).run methods s = .ok result s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      WhnfMeaning trProj world uvars Δ source result :=
  ⟨h.uncached_eval, h.initialInv, h.finalInv, h.meaning theory⟩

/-- Conditional Hoare closure for the complete structural loop.  Success is
    obtained by constructing and folding `WhnfCoreTrace`; failure preserves
    the invariant and retains the exhaustion/step-error distinction. -/
theorem uncached_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {flags : WhnfFlags}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world uvars)
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta id
      (fun cur => whnfCoreWithFlagsStep cur flags) stepError)
    {source : KExpr .anon} {sourceV : VExpr} {s : TcState .anon}
    (hsupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfCoreWithFlagsUncached source flags)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
      (WhnfLoopError stepError) := by
  intro methods hmethods hI
  have hcomplete := WhnfCoreTrace.complete hstep hmethods
    (fuel := maxWhnfFuel.toNat) (source := source) (s := s)
    ⟨hsupport, sourceV, hsource⟩ hI
  unfold whnfCoreWithFlagsUncached
  match hrun :
      (runBounded (fun cur => whnfCoreWithFlagsStep cur flags)
        maxWhnfFuel.toNat source).run methods s with
  | .ok result s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      refine ⟨hcomplete.2.finalInv, hcomplete.1, ?_⟩
      have hstart := WhnfPost.refl hsource
        (theory.exprWF hI.2.1 hsource)
      exact hstart.transMeaning theory hI.2.1.wf
        (hcomplete.2.meaning theory)
  | .error err s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      exact hcomplete

end WhnfCoreTrace

/-! ## Outer structural-WHNF cache composition -/

/-- Forms that pass the syntactic leaf/legacy-variable prefix and enter the
keyed structural-WHNF body without consulting `isLetVar`. -/
inductive WhnfCoreNonLeaf : KExpr .anon → Prop
  | fvar {id name info} : WhnfCoreNonLeaf (.fvar id name info)
  | app {f a info} : WhnfCoreNonLeaf (.app f a info)
  | letE {name ty value body nondep info} :
      WhnfCoreNonLeaf (.letE name ty value body nondep info)
  | prj {id field value info} : WhnfCoreNonLeaf (.prj id field value info)

namespace WhnfCoreNonLeaf

/-- Exact bridge from the public structural entry point to its keyed body. -/
theorem enter {e : KExpr .anon} (h : WhnfCoreNonLeaf e)
    (flags : WhnfFlags) :
    whnfCoreWithFlags e flags = whnfCoreWithFlagsNonLeaf e flags := by
  cases h <;> rfl

end WhnfCoreNonLeaf

/-- A legacy variable that is not backed by a let frame returns before key
computation, exactly like the syntactic leaf forms. -/
theorem whnfCoreWithFlags_varNotLet
    {methods : Methods .anon} {s s' : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    (hlet : TcM.isLetVar idx s = .ok false s') :
    (whnfCoreWithFlags (.var idx name info) flags).run methods s =
      .ok (.var idx name info) s' := by
  unfold whnfCoreWithFlags
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.isLetVar idx) _ s = _
  unfold EStateM.bind
  rw [hlet]
  rfl

/-- A let-backed legacy variable crosses the public prefix and enters the
same keyed cache body as every direct non-leaf form. -/
theorem whnfCoreWithFlags_varEnter
    {methods : Methods .anon} {s s' : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    (hlet : TcM.isLetVar idx s = .ok true s') :
    (whnfCoreWithFlags (.var idx name info) flags).run methods s =
      (whnfCoreWithFlagsNonLeaf (.var idx name info) flags).run methods s' := by
  unfold whnfCoreWithFlags
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.isLetVar idx) _ s = _
  unfold EStateM.bind
  rw [hlet]
  rfl

/-- Execution-indexed evidence that the public structural entry point reaches
its keyed body.  Direct non-leaves preserve the state; a legacy variable may
first execute `isLetVar`. -/
inductive WhnfCoreKeyedEntry (methods : Methods .anon) (flags : WhnfFlags) :
    KExpr .anon → TcState .anon → TcState .anon → Prop
  | direct {source s} (h : WhnfCoreNonLeaf source) :
      WhnfCoreKeyedEntry methods flags source s s
  | varLet {idx name info s s'}
      (hlet : TcM.isLetVar idx s = .ok true s') :
      WhnfCoreKeyedEntry methods flags (.var idx name info) s s'

namespace WhnfCoreKeyedEntry

theorem eval {methods : Methods .anon} {flags : WhnfFlags}
    {source : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfCoreKeyedEntry methods flags source s s') :
    (whnfCoreWithFlags source flags).run methods s =
      (whnfCoreWithFlagsNonLeaf source flags).run methods s' := by
  cases h with
  | direct h => rw [h.enter]
  | varLet hlet => exact whnfCoreWithFlags_varEnter hlet

end WhnfCoreKeyedEntry

/-- Exact full-policy cache-hit execution after key and transient checks. -/
theorem whnfCoreWithFlagsNonLeaf_fullHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfCoreCache[key]? = some cached) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok cached s₂ := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

/-- Exact cheap-policy cache-hit execution after key and transient checks. -/
theorem whnfCoreWithFlagsNonLeaf_cheapHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfCoreCheapCache[key]? = some cached) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok cached s₂ := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hcheap]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

/-- Exact full-policy miss execution, including the physical insertion. -/
theorem whnfCoreWithFlagsNonLeaf_fullMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfCoreCache[key]? = none)
    (hrun : (whnfCoreWithFlagsUncached source flags).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfCoreCache := s₃.env.whnfCoreCache.insert key result}} := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfCoreWithFlagsUncached source flags).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

/-- Exact cheap-policy miss execution, including its separate insertion. -/
theorem whnfCoreWithFlagsNonLeaf_cheapMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfCoreCheapCache[key]? = none)
    (hrun : (whnfCoreWithFlagsUncached source flags).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfCoreCheapCache := s₃.env.whnfCoreCheapCache.insert key result}} := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [hcheap]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfCoreWithFlagsUncached source flags).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

/-- Transient Nat work bypasses both cache reads and cache writes under
either flag policy. -/
theorem whnfCoreWithFlagsNonLeaf_transient
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok true s₂)
    (hrun : (whnfCoreWithFlagsUncached source flags).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsNonLeaf source flags).run methods s =
      .ok result s₃ := by
  unfold whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  cases flags.isFull <;> simp [hrun]

namespace WhnfCoreCacheUpdate

/-- Inserting one provenance-certified full-core result preserves the entire
fixed-world WHNF state invariant. -/
theorem full_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .whnfCore key result)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with
        whnfCoreCache := s.env.whnfCoreCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfCore hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Inserting one provenance-certified cheap-core result preserves the full
invariant without changing the full-policy partition. -/
theorem cheap_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .whnfCoreCheap key result)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with
        whnfCoreCheapCache := s.env.whnfCoreCheapCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfCoreCheap hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end WhnfCoreCacheUpdate

namespace NatSuccStuckCacheUpdate

/-- The exact state frame for either successor-loop stuck exit.  All visited
markers must already carry cache provenance; under that condition the fold
changes only `natSuccStuck` and preserves the complete fixed-world invariant. -/
theorem fold_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    (visited : Array (Address × Address))
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : ∀ key ∈ visited,
      CacheProvenance semantics (CacheAuthority.stable world) support
        (.natSuccStuck key)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with natSuccStuck :=
        (visited.foldl (·.insert ·) s.env.natSuccStuck) } } := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertNatSuccStuckArray visited hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end NatSuccStuckCacheUpdate

/-- A physical full-core hit is accepted only with both a semantic cache
invariant and an executed/context-reconciled key match. -/
theorem whnfCoreWithFlags_fullHit_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source cached : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ : TcState .anon}
    (hentry : WhnfCoreKeyedEntry methods flags source s s₀)
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfCoreCache[key]? = some cached)
    (hI : WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ s₂)
    (hsource : support source)
    (hmatch : keys.Matches trProj world s₂ Δ source key) :
    (whnfCoreWithFlags source flags).run methods s = .ok cached s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfMeaning trProj world keys.uvars Δ source cached := by
  refine ⟨?_, hI, ?_⟩
  · rw [hentry.eval]
    exact whnfCoreWithFlagsNonLeaf_fullHit hfull hkey htransient hhit
  · exact hI.1.caches.whnfHitOfMatches (.whnfCore hhit)
      .whnfCore hsource hmatch

/-- Cheap-core hits are read only from the cheap partition and carry the
same semantic consequence as full-core hits. -/
theorem whnfCoreWithFlags_cheapHit_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source cached : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ : TcState .anon}
    (hentry : WhnfCoreKeyedEntry methods flags source s s₀)
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfCoreCheapCache[key]? = some cached)
    (hI : WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ s₂)
    (hsource : support source)
    (hmatch : keys.Matches trProj world s₂ Δ source key) :
    (whnfCoreWithFlags source flags).run methods s = .ok cached s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfMeaning trProj world keys.uvars Δ source cached := by
  refine ⟨?_, hI, ?_⟩
  · rw [hentry.eval]
    exact whnfCoreWithFlagsNonLeaf_cheapHit hcheap hkey htransient hhit
  · exact hI.1.caches.whnfHitOfMatches (.whnfCoreCheap hhit)
      .whnfCoreCheap hsource hmatch

/-- A full-core miss may populate the cache only after the uncached trace
certifies this execution and the new entry has universal cache provenance. -/
theorem whnfCoreWithFlags_fullMiss_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfCoreKeyedEntry methods flags source s s₀)
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfCoreCache[key]? = none)
    (htrace : WhnfCoreTrace layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ methods flags maxWhnfFuel.toNat
      source s₂ result s₃)
    (hnew : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support (.expr .whnfCore key result)) :
    let s₄ := {s₃ with env := {s₃.env with
      whnfCoreCache := s₃.env.whnfCoreCache.insert key result}}
    (whnfCoreWithFlags source flags).run methods s = .ok result s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  dsimp only
  refine ⟨?_, htrace.initialInv, ?_, htrace.meaning theory⟩
  · rw [hentry.eval]
    exact whnfCoreWithFlagsNonLeaf_fullMiss hfull hkey htransient hmiss
      htrace.uncached_eval
  · exact WhnfCoreCacheUpdate.full_whnfStateInv htrace.finalInv hnew

/-- Cheap misses insert only into the cheap partition; as for full misses,
raw uncached success is insufficient without a trace and entry provenance. -/
theorem whnfCoreWithFlags_cheapMiss_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfCoreKeyedEntry methods flags source s s₀)
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfCoreCheapCache[key]? = none)
    (htrace : WhnfCoreTrace layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ methods flags maxWhnfFuel.toNat
      source s₂ result s₃)
    (hnew : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfCoreCheap key result)) :
    let s₄ := {s₃ with env := {s₃.env with
      whnfCoreCheapCache := s₃.env.whnfCoreCheapCache.insert key result}}
    (whnfCoreWithFlags source flags).run methods s = .ok result s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  dsimp only
  refine ⟨?_, htrace.initialInv, ?_, htrace.meaning theory⟩
  · rw [hentry.eval]
    exact whnfCoreWithFlagsNonLeaf_cheapMiss hcheap hkey htransient hmiss
      htrace.uncached_eval
  · exact WhnfCoreCacheUpdate.cheap_whnfStateInv htrace.finalInv hnew

/-- Transient Nat-literal work executes the certified uncached path without
reading or writing either core cache. -/
theorem whnfCoreWithFlags_transient_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfCoreKeyedEntry methods flags source s s₀)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok true s₂)
    (htrace : WhnfCoreTrace layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ methods flags maxWhnfFuel.toNat
      source s₂ result s₃) :
    (whnfCoreWithFlags source flags).run methods s = .ok result s₃ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₃ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  refine ⟨?_, htrace.initialInv, htrace.finalInv, htrace.meaning theory⟩
  rw [hentry.eval]
  exact whnfCoreWithFlagsNonLeaf_transient hkey htransient
    htrace.uncached_eval

/-! ## No-delta and full-WHNF driver composition -/

/-- Execution-indexed semantic certificate for the production no-delta
WHNF loop.  Each constructor records the exact named step equation, the
fixed K1 invariant on both sides, and the local Theory meaning. -/
inductive WhnfNoDeltaTrace (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (Δ : KVLCtx) (methods : Methods .anon) (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) :
    Nat → KExpr .anon → TcState .anon → KExpr .anon → TcState .anon → Prop
  | done {fuel : Nat} {cur result : KExpr .anon} {s s' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfNoDeltaImplStep flags natSuccMode cur).run methods s =
        .ok (.done result) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur result →
      WhnfNoDeltaTrace layer semantics trProj world support uvars Δ methods
        flags natSuccMode (fuel + 1) cur s result s'
  | next {fuel : Nat} {cur middle result : KExpr .anon}
      {s s' s'' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfNoDeltaImplStep flags natSuccMode cur).run methods s =
        .ok (.next middle) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur middle →
      WhnfNoDeltaTrace layer semantics trProj world support uvars Δ methods
        flags natSuccMode fuel middle s' result s'' →
      WhnfNoDeltaTrace layer semantics trProj world support uvars Δ methods
        flags natSuccMode (fuel + 1) cur s result s''

namespace WhnfNoDeltaTrace

theorem no_zero {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {source result : KExpr .anon} {s s' : TcState .anon} :
    ¬WhnfNoDeltaTrace layer semantics trProj world support uvars Δ methods
      flags natSuccMode 0 source s result s' := by
  intro h
  cases h

/-- Construct the production no-delta trace from a one-step semantic
    contract, retaining invariant-preserving step failures separately from
    bounded-loop exhaustion. -/
theorem complete {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta id
      (whnfNoDeltaImplStep flags natSuccMode) stepError)
    {methods : Methods .anon}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    {fuel : Nat} {source : KExpr .anon} {s : TcState .anon}
    (hsource : WhnfStep.Source trProj world support uvars Delta id source)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    match (runBounded (whnfNoDeltaImplStep flags natSuccMode)
      fuel source).run methods s with
    | .ok result s' =>
        support result ∧
          WhnfNoDeltaTrace layer semantics trProj world support uvars Delta
            methods flags natSuccMode fuel source s result s'
    | .error err s' =>
        WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
          WhnfLoopError stepError err s' := by
  induction fuel generalizing source s with
  | zero =>
      rw [runBounded]
      exact ⟨hI, Or.inl rfl⟩
  | succ fuel ih =>
      have hlocal := hstep source s hsource methods hmethods hI
      match hrun :
          (whnfNoDeltaImplStep flags natSuccMode source).run methods s with
      | .error err s' =>
          rw [hrun] at hlocal
          rw [runBounded, ReaderT.run_bind]
          change match EStateM.bind
            ((whnfNoDeltaImplStep flags natSuccMode source).run methods) _ s
            with
            | .ok result s'' =>
                support result ∧
                  WhnfNoDeltaTrace layer semantics trProj world support uvars
                    Delta methods flags natSuccMode (fuel + 1) source s result
                    s''
            | .error err s'' =>
                WhnfStateInv layer semantics trProj world support uvars Delta
                    s'' ∧
                  WhnfLoopError stepError err s''
          unfold EStateM.bind
          rw [hrun]
          exact ⟨hlocal.1, Or.inr hlocal.2⟩
      | .ok action s' =>
          rw [hrun] at hlocal
          cases action with
          | done result =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source
                  result := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfNoDeltaImplStep flags natSuccMode source).run methods) _
                  s with
                | .ok result s'' =>
                    support result ∧
                      WhnfNoDeltaTrace layer semantics trProj world support
                        uvars Delta methods flags natSuccMode (fuel + 1)
                        source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              exact ⟨hlocal.2.1, .done hI hrun hlocal.1 hmeaning⟩
          | next next =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source
                  next := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              have hnextSource : WhnfStep.Source trProj world support uvars
                  Delta id next := by
                obtain ⟨_, nextV, _, hnext, _⟩ := hmeaning
                exact ⟨hlocal.2.1, nextV, hnext⟩
              have htail := ih (source := next) (s := s') hnextSource hlocal.1
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfNoDeltaImplStep flags natSuccMode source).run methods) _
                  s with
                | .ok result s'' =>
                    support result ∧
                      WhnfNoDeltaTrace layer semantics trProj world support
                        uvars Delta methods flags natSuccMode (fuel + 1)
                        source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              simp only
              match htailRun :
                  (runBounded (whnfNoDeltaImplStep flags natSuccMode)
                    fuel next).run methods s' with
              | .ok result s'' =>
                  rw [htailRun] at htail
                  exact ⟨htail.1,
                    .next hI hrun hlocal.1 hmeaning htail.2⟩
              | .error err s'' =>
                  rw [htailRun] at htail
                  exact htail

theorem eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode} {fuel : Nat}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode fuel source s result s') :
    (runBounded (whnfNoDeltaImplStep flags natSuccMode) fuel source).run
      methods s = .ok result s' := by
  induction h with
  | done hI hstep hI' hmeaning =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfNoDeltaImplStep _ _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      rfl
  | next hI hstep hI' hmeaning htail ih =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfNoDeltaImplStep _ _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      exact ih

theorem initialInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode} {fuel : Nat}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s := by
  cases h <;> assumption

theorem finalInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode} {fuel : Nat}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s' := by
  induction h with
  | done hI hstep hI' hmeaning => exact hI'
  | next hI hstep hI' hmeaning htail ih => exact ih

theorem meaning {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode} {fuel : Nat}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode fuel source s result s') :
    WhnfMeaning trProj world uvars Δ source result := by
  induction h with
  | done hI hstep hI' hmeaning => exact hmeaning
  | next hI hstep hI' hmeaning htail ih =>
      exact theory.transMeaning hI.2.1.wf hmeaning ih

theorem uncached_eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode maxWhnfFuel.toNat source s result s') :
    (whnfNoDeltaImplUncached source flags natSuccMode).run methods s =
      .ok result s' := by
  unfold whnfNoDeltaImplUncached
  exact h.eval

theorem uncached_acceptance {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {source result : KExpr .anon}
    {s s' : TcState .anon} (theory : WhnfTheory trProj world uvars)
    (h : WhnfNoDeltaTrace layer semantics trProj world support uvars Δ
      methods flags natSuccMode maxWhnfFuel.toNat source s result s') :
    (whnfNoDeltaImplUncached source flags natSuccMode).run methods s =
        .ok result s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      WhnfMeaning trProj world uvars Δ source result :=
  ⟨h.uncached_eval, h.initialInv, h.finalInv, h.meaning theory⟩

/-- Conditional Hoare closure for the no-delta bounded loop. -/
theorem uncached_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world uvars)
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta id
      (whnfNoDeltaImplStep flags natSuccMode) stepError)
    {source : KExpr .anon} {sourceV : VExpr} {s : TcState .anon}
    (hsupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfNoDeltaImplUncached source flags natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
      (WhnfLoopError stepError) := by
  intro methods hmethods hI
  have hcomplete := WhnfNoDeltaTrace.complete hstep hmethods
    (fuel := maxWhnfFuel.toNat) (source := source) (s := s)
    ⟨hsupport, sourceV, hsource⟩ hI
  unfold whnfNoDeltaImplUncached
  match hrun :
      (runBounded (whnfNoDeltaImplStep flags natSuccMode)
        maxWhnfFuel.toNat source).run methods s with
  | .ok result s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      refine ⟨hcomplete.2.finalInv, hcomplete.1, ?_⟩
      have hstart := WhnfPost.refl hsource
        (theory.exprWF hI.2.1 hsource)
      exact hstart.transMeaning theory hI.2.1.wf
        (hcomplete.2.meaning theory)
  | .error err s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      exact hcomplete

end WhnfNoDeltaTrace

/-- Execution-indexed semantic certificate for the production full-WHNF
loop.  The loop state also records its cycle-detection set; semantic meaning
is attached only to the expression component. -/
inductive WhnfFullTrace (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Δ : KVLCtx) (methods : Methods .anon)
    (natSuccMode : NatSuccMode) :
    Nat → (KExpr .anon × HashSet Address) → TcState .anon →
      KExpr .anon → TcState .anon → Prop
  | done {fuel : Nat} {cur : KExpr .anon × HashSet Address}
      {result : KExpr .anon} {s s' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfWithNatSuccModeStep natSuccMode cur).run methods s =
        .ok (.done result) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur.1 result →
      WhnfFullTrace layer semantics trProj world support uvars Δ methods
        natSuccMode (fuel + 1) cur s result s'
  | next {fuel : Nat} {cur middle : KExpr .anon × HashSet Address}
      {result : KExpr .anon} {s s' s'' : TcState .anon} :
      WhnfStateInv layer semantics trProj world support uvars Δ s →
      (whnfWithNatSuccModeStep natSuccMode cur).run methods s =
        .ok (.next middle) s' →
      WhnfStateInv layer semantics trProj world support uvars Δ s' →
      WhnfMeaning trProj world uvars Δ cur.1 middle.1 →
      WhnfFullTrace layer semantics trProj world support uvars Δ methods
        natSuccMode fuel middle s' result s'' →
      WhnfFullTrace layer semantics trProj world support uvars Δ methods
        natSuccMode (fuel + 1) cur s result s''

namespace WhnfFullTrace

theorem no_zero {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {source : KExpr .anon × HashSet Address}
    {result : KExpr .anon} {s s' : TcState .anon} :
    ¬WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode 0 source s result s' := by
  intro h
  cases h

/-- Construct the full-WHNF trace from a one-step semantic contract.  The
    cycle-detection set remains operational state; only each pair's
    expression component participates in `WhnfMeaning`. -/
theorem complete {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    {methods : Methods .anon}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    {fuel : Nat} {source : KExpr .anon × HashSet Address}
    {s : TcState .anon}
    (hsource : WhnfStep.Source trProj world support uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1) source)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    match (runBounded (whnfWithNatSuccModeStep natSuccMode)
      fuel source).run methods s with
    | .ok result s' =>
        support result ∧
          WhnfFullTrace layer semantics trProj world support uvars Delta
            methods natSuccMode fuel source s result s'
    | .error err s' =>
        WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
          WhnfLoopError stepError err s' := by
  induction fuel generalizing source s with
  | zero =>
      rw [runBounded]
      exact ⟨hI, Or.inl rfl⟩
  | succ fuel ih =>
      have hlocal := hstep source s hsource methods hmethods hI
      match hrun :
          (whnfWithNatSuccModeStep natSuccMode source).run methods s with
      | .error err s' =>
          rw [hrun] at hlocal
          rw [runBounded, ReaderT.run_bind]
          change match EStateM.bind
            ((whnfWithNatSuccModeStep natSuccMode source).run methods) _ s
            with
            | .ok result s'' =>
                support result ∧
                  WhnfFullTrace layer semantics trProj world support uvars
                    Delta methods natSuccMode (fuel + 1) source s result s''
            | .error err s'' =>
                WhnfStateInv layer semantics trProj world support uvars Delta
                    s'' ∧
                  WhnfLoopError stepError err s''
          unfold EStateM.bind
          rw [hrun]
          exact ⟨hlocal.1, Or.inr hlocal.2⟩
      | .ok action s' =>
          rw [hrun] at hlocal
          cases action with
          | done result =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source.1
                  result := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfWithNatSuccModeStep natSuccMode source).run methods) _ s
                with
                | .ok result s'' =>
                    support result ∧
                      WhnfFullTrace layer semantics trProj world support uvars
                        Delta methods natSuccMode (fuel + 1) source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              exact ⟨hlocal.2.1, .done hI hrun hlocal.1 hmeaning⟩
          | next next =>
              have hmeaning : WhnfMeaning trProj world uvars Delta source.1
                  next.1 := by
                simpa [WhnfStep.Meaning] using hlocal.2.2
              have hnextSource : WhnfStep.Source trProj world support uvars Delta
                  (fun state : KExpr .anon × HashSet Address => state.1)
                  next := by
                obtain ⟨_, nextV, _, hnext, _⟩ := hmeaning
                exact ⟨hlocal.2.1, nextV, hnext⟩
              have htail := ih (source := next) (s := s') hnextSource hlocal.1
              rw [runBounded, ReaderT.run_bind]
              change match EStateM.bind
                ((whnfWithNatSuccModeStep natSuccMode source).run methods) _ s
                with
                | .ok result s'' =>
                    support result ∧
                      WhnfFullTrace layer semantics trProj world support uvars
                        Delta methods natSuccMode (fuel + 1) source s result s''
                | .error err s'' =>
                    WhnfStateInv layer semantics trProj world support uvars
                        Delta s'' ∧
                      WhnfLoopError stepError err s''
              unfold EStateM.bind
              rw [hrun]
              simp only
              match htailRun :
                  (runBounded (whnfWithNatSuccModeStep natSuccMode)
                    fuel next).run methods s' with
              | .ok result s'' =>
                  rw [htailRun] at htail
                  exact ⟨htail.1,
                    .next hI hrun hlocal.1 hmeaning htail.2⟩
              | .error err s'' =>
                  rw [htailRun] at htail
                  exact htail

theorem eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {fuel : Nat}
    {source : KExpr .anon × HashSet Address} {result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode fuel source s result s') :
    (runBounded (whnfWithNatSuccModeStep natSuccMode) fuel source).run
      methods s = .ok result s' := by
  induction h with
  | done hI hstep hI' hmeaning =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfWithNatSuccModeStep _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      rfl
  | next hI hstep hI' hmeaning htail ih =>
      rw [runBounded, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (whnfWithNatSuccModeStep _ _) _) _ _ = _
      unfold EStateM.bind
      rw [hstep]
      exact ih

theorem initialInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {fuel : Nat}
    {source : KExpr .anon × HashSet Address} {result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s := by
  cases h <;> assumption

theorem finalInv {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {fuel : Nat}
    {source : KExpr .anon × HashSet Address} {result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode fuel source s result s') :
    WhnfStateInv layer semantics trProj world support uvars Δ s' := by
  induction h with
  | done hI hstep hI' hmeaning => exact hI'
  | next hI hstep hI' hmeaning htail ih => exact ih

theorem meaning {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {fuel : Nat}
    {source : KExpr .anon × HashSet Address} {result : KExpr .anon}
    {s s' : TcState .anon} (theory : WhnfTheory trProj world uvars)
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode fuel source s result s') :
    WhnfMeaning trProj world uvars Δ source.1 result := by
  induction h with
  | done hI hstep hI' hmeaning => exact hmeaning
  | next hI hstep hI' hmeaning htail ih =>
      exact theory.transMeaning hI.2.1.wf hmeaning ih

theorem uncached_eval {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {source result : KExpr .anon}
    {s s' : TcState .anon}
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode maxWhnfFuel.toNat (source, {}) s result s') :
    (whnfWithNatSuccModeUncached source natSuccMode).run methods s =
      .ok result s' := by
  unfold whnfWithNatSuccModeUncached
  exact h.eval

theorem uncached_acceptance {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {natSuccMode : NatSuccMode}
    {source result : KExpr .anon} {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (h : WhnfFullTrace layer semantics trProj world support uvars Δ methods
      natSuccMode maxWhnfFuel.toNat (source, {}) s result s') :
    (whnfWithNatSuccModeUncached source natSuccMode).run methods s =
        .ok result s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      WhnfMeaning trProj world uvars Δ source result :=
  ⟨h.uncached_eval, h.initialInv, h.finalInv, h.meaning theory⟩

/-- Conditional Hoare closure for the full-WHNF bounded loop. -/
theorem uncached_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world uvars)
    (hstep : WhnfStep.WF layer semantics trProj world support uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    {source : KExpr .anon} {sourceV : VExpr} {s : TcState .anon}
    (hsupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfWithNatSuccModeUncached source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
      (WhnfLoopError stepError) := by
  intro methods hmethods hI
  have hcomplete := WhnfFullTrace.complete hstep hmethods
    (fuel := maxWhnfFuel.toNat) (source := (source, {})) (s := s)
    ⟨hsupport, sourceV, hsource⟩ hI
  unfold whnfWithNatSuccModeUncached
  match hrun :
      (runBounded (whnfWithNatSuccModeStep natSuccMode)
        maxWhnfFuel.toNat (source, {})).run methods s with
  | .ok result s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      refine ⟨hcomplete.2.finalInv, hcomplete.1, ?_⟩
      have hstart := WhnfPost.refl hsource
        (theory.exprWF hI.2.1 hsource)
      exact hstart.transMeaning theory hI.2.1.wf
        (hcomplete.2.meaning theory)
  | .error err s' =>
      rw [hrun] at hcomplete
      simp only at hcomplete ⊢
      exact hcomplete

end WhnfFullTrace

/-! ### Public-driver shell obligations -/

namespace WhnfKey

/-- The context-suffix fact still owed by the concrete key algorithm.  It is
    quantified over the actual pre/post execution so public-driver proofs do
    not turn address equality into a context theorem. -/
def Represents (keys : WhnfContextKeys) (trProj : RawProjRel)
    (world : VerifyWorld) (source : KExpr .anon) (Delta : KVLCtx) : Prop :=
  forall before key after,
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta ->
    TcM.whnfKey source before = .ok key after ->
      keys.Represents source.lbr key.2 Delta

/-- K2's suffix transport is unnecessary for a syntactically closed source:
    production returns the distinguished empty-context key exactly. -/
theorem closed_represents {uvars : Nat} {source : KExpr .anon}
    {trProj : RawProjRel} {world : VerifyWorld}
    (hclosed : source.lbr = 0) :
    Represents (WhnfContextKeys.closed uvars) trProj world source [] := by
  intro before key after hctx hrun
  have hexact := TcM.whnfKey_closed (s := before) hclosed
  rw [hexact] at hrun
  cases hrun
  exact ⟨hclosed, rfl, rfl⟩

end WhnfKey

namespace TransientNatWork

/-- State-preservation contract for the production transient-work probe.
    Its trusted constant reads and lazy-ingress behavior are independent of
    reduction meaning and therefore remain a named shell obligation. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (source : KExpr .anon) : Prop :=
  forall s,
    RecM.WF layer semantics trProj world support uvars Delta s
      (isTransientNatLiteralWork source) (fun _ _ => True)

end TransientNatWork

/-- Collision-robust provenance needed at the three outer cache insertion
    sites.  A meaning proof for the executed source alone is insufficient:
    cache validity quantifies over every supported source sharing the key's
    address and every represented context.  Keeping this interface explicit
    prevents a hash-collision assumption from entering K1 unnoticed. -/
structure WhnfCacheWriteOracle (keys : WhnfContextKeys)
    (trProj : RawProjRel) (fallback : CacheSemantics)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  noDelta : forall {Delta source key result s},
    support source ->
    support result ->
    keys.Matches trProj world s Delta source key ->
    WhnfMeaning trProj world keys.uvars Delta source result ->
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfNoDelta key result)
  noDeltaCheap : forall {Delta source key result s},
    support source ->
    support result ->
    keys.Matches trProj world s Delta source key ->
    WhnfMeaning trProj world keys.uvars Delta source result ->
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfNoDeltaCheap key result)
  full : forall {Delta source key result s},
    support source ->
    support result ->
    keys.Matches trProj world s Delta source key ->
    WhnfMeaning trProj world keys.uvars Delta source result ->
    CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support (.expr .whnf key result)

namespace WhnfCacheWriteOracle

/-- Construct all three outer write rules for closed expressions.  Expression
    collision freedom identifies every supported source at the address key;
    the remaining premise is exactly direct-reference authorization for the
    concrete cache entry.  Open-context transport is deliberately absent and
    remains K2 work. -/
theorem closed
    {uvars : Nat} {trProj : RawProjRel} {fallback : CacheSemantics}
    {world : VerifyWorld} {support : RunSupport}
    (hcollision : support.CollisionFree)
    (hreferences : forall {kind key source result},
      (kind = .whnfNoDelta ∨ kind = .whnfNoDeltaCheap ∨ kind = .whnf) ->
      support source -> support result -> source.addr = key.1 ->
      (CacheEntry.expr kind key result).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    WhnfCacheWriteOracle (WhnfContextKeys.closed uvars) trProj fallback
      world support := by
  have build : forall {kind : ExprCacheKind} {Delta source key result s},
      (kind = .whnfNoDelta ∨ kind = .whnfNoDeltaCheap ∨ kind = .whnf) ->
      support source ->
      support result ->
      (WhnfContextKeys.closed uvars).Matches trProj world s Delta source key ->
      WhnfMeaning trProj world uvars Delta source result ->
      CacheProvenance
        (whnfCacheSemantics (WhnfContextKeys.closed uvars) trProj fallback)
        (CacheAuthority.stable world) support (.expr kind key result) := by
    intro kind Delta source key result s hkind hsource hresult hmatch hmeaning
    have hDelta : Delta = [] := hmatch.2.1.2.2
    subst Delta
    refine ⟨⟨⟨source, hsource, hmatch.sourceAddr⟩, hresult⟩,
      hreferences hkind hsource hresult hmatch.sourceAddr, ?_⟩
    have his : kind.IsWhnf := by
      rcases hkind with hkind | hkind
      · subst kind
        exact .whnfNoDelta
      · rcases hkind with hkind | hkind
        · subst kind
          exact .whnfNoDeltaCheap
        · subst kind
          exact .whnf
    have htransport : forall other, support other -> other.addr = key.1 ->
        forall Delta,
          (WhnfContextKeys.closed uvars).Represents other.lbr key.2 Delta ->
          WhnfMeaning trProj world uvars Delta other result := by
      intro other hother haddr Delta hrepresented
      have heq : source = other := by
        have herase := hcollision.expr hsource hother
          (hmatch.sourceAddr.trans haddr.symm)
        simpa only [KExpr.eraseMeta_anon] using herase
      subst other
      have hDelta : Delta = [] := hrepresented.2.2
      subst Delta
      exact hmeaning
    cases his <;> exact htransport
  refine ⟨?_, ?_, ?_⟩
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inl rfl) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr (.inl rfl)) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr (.inr rfl)) hsource hresult hmatch hmeaning

end WhnfCacheWriteOracle

/-- Non-leaf forms shared by the no-delta and full-WHNF public prefixes. -/
inductive WhnfDriverNonLeaf : KExpr .anon → Prop
  | const {id us info} : WhnfDriverNonLeaf (.const id us info)
  | fvar {id name info} : WhnfDriverNonLeaf (.fvar id name info)
  | app {f a info} : WhnfDriverNonLeaf (.app f a info)
  | letE {name ty value body nondep info} :
      WhnfDriverNonLeaf (.letE name ty value body nondep info)
  | prj {id field value info} : WhnfDriverNonLeaf (.prj id field value info)

namespace WhnfDriverNonLeaf

theorem noDelta_enter {e : KExpr .anon} (h : WhnfDriverNonLeaf e)
    (flags : WhnfFlags) (natSuccMode : NatSuccMode) :
    whnfNoDeltaImpl e flags natSuccMode =
      whnfNoDeltaImplNonLeaf e flags natSuccMode := by
  cases h <;> rfl

theorem full_enter {e : KExpr .anon} (h : WhnfDriverNonLeaf e)
    (natSuccMode : NatSuccMode) :
    whnfWithNatSuccMode e natSuccMode =
      whnfWithNatSuccModeNonLeaf e natSuccMode := by
  cases h <;> rfl

end WhnfDriverNonLeaf

/-- Both outer drivers share the same syntactic prefix.  A direct non-leaf
preserves state; a legacy variable enters only after an executed let test. -/
inductive WhnfDriverEntry (methods : Methods .anon) :
    KExpr .anon → TcState .anon → TcState .anon → Prop
  | direct {source s} (h : WhnfDriverNonLeaf source) :
      WhnfDriverEntry methods source s s
  | varLet {idx name info s s'}
      (hlet : TcM.isLetVar idx s = .ok true s') :
      WhnfDriverEntry methods (.var idx name info) s s'

namespace WhnfDriverEntry

theorem noDelta_eval {methods : Methods .anon}
    {source : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfDriverEntry methods source s s') (flags : WhnfFlags)
    (natSuccMode : NatSuccMode) :
    (whnfNoDeltaImpl source flags natSuccMode).run methods s =
      (whnfNoDeltaImplNonLeaf source flags natSuccMode).run methods s' := by
  cases h with
  | direct h => rw [h.noDelta_enter]
  | varLet hlet =>
      unfold whnfNoDeltaImpl
      rw [ReaderT.run_bind]
      change EStateM.bind (TcM.isLetVar _ ) _ _ = _
      unfold EStateM.bind
      rw [hlet]
      rfl

theorem full_eval {methods : Methods .anon}
    {source : KExpr .anon} {s s' : TcState .anon}
    (h : WhnfDriverEntry methods source s s')
    (natSuccMode : NatSuccMode) :
    (whnfWithNatSuccMode source natSuccMode).run methods s =
      (whnfWithNatSuccModeNonLeaf source natSuccMode).run methods s' := by
  cases h with
  | direct h => rw [h.full_enter]
  | varLet hlet =>
      unfold whnfWithNatSuccMode
      rw [ReaderT.run_bind]
      change EStateM.bind (TcM.isLetVar _) _ _ = _
      unfold EStateM.bind
      rw [hlet]
      rfl

end WhnfDriverEntry

/-- With tracing and statistics disabled, the full-WHNF prefix is an exact
state-preserving no-op. -/
theorem whnfWithNatSuccModePrefix_disabled
    {methods : Methods .anon} {source : KExpr .anon} {s : TcState .anon}
    (htrace : s.stepTrace = false) (hstats : s.stats = false) :
    (whnfWithNatSuccModePrefix source).run methods s = .ok () s := by
  unfold whnfWithNatSuccModePrefix
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.stepTrace "whnf+" (fun _ => TcM.addr8 source.addr)) _ s = _
  unfold EStateM.bind
  rw [TcM.stepTrace_disabled htrace]
  exact TcM.bumpStats_disabled hstats _

/-- With statistics disabled and positive fuel, a full-WHNF cache miss
performs exactly its single fuel decrement and no other state change. -/
theorem whnfWithNatSuccModeMissCharge_disabled
    {methods : Methods .anon} {s : TcState .anon}
    (hstats : s.stats = false) (hfuel : (s.recFuel == 0) = false) :
    (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods s =
      .ok () {s with recFuel := s.recFuel - 1} := by
  unfold whnfWithNatSuccModeMissCharge
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.bumpStats (fun s => {s with whnfMisses := s.whnfMisses + 1})) _
      s = _
  unfold EStateM.bind
  rw [TcM.bumpStats_disabled hstats]
  exact TcM.tick_success hfuel

/-! ### Exact no-delta cache equations -/

private theorem natSuccMode_collapse_beq :
    (NatSuccMode.collapse == NatSuccMode.collapse) = true := rfl

private theorem natSuccMode_stuck_beq :
    (NatSuccMode.stuck == NatSuccMode.collapse) = false := rfl

theorem whnfNoDeltaImplNonLeaf_fullHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfNoDeltaCache[key]? = some cached) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok cached s₂ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

theorem whnfNoDeltaImplNonLeaf_cheapHit
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source cached : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfNoDeltaCheapCache[key]? = some cached) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok cached s₂ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hcheap]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hhit]
  rfl

theorem whnfNoDeltaImplNonLeaf_fullMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCache[key]? = none)
    (hrun : (whnfNoDeltaImplUncached source flags .collapse).run methods s₂ =
      .ok result s₃)
    (hnative : s₃.inNativeReduce = false) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfNoDeltaCache := s₃.env.whnfNoDeltaCache.insert key result}} := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hfull]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only
  rw [if_pos hnative]
  rfl

theorem whnfNoDeltaImplNonLeaf_cheapMiss
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCheapCache[key]? = none)
    (hrun : (whnfNoDeltaImplUncached source flags .collapse).run methods s₂ =
      .ok result s₃)
    (hnative : s₃.inNativeReduce = false) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok result {s₃ with env := {s₃.env with
        whnfNoDeltaCheapCache :=
          s₃.env.whnfNoDeltaCheapCache.insert key result}} := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq, hcheap]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only
  rw [if_pos hnative]
  rfl

/-- Stuck-succ mode reads and writes neither no-delta cache partition. -/
theorem whnfNoDeltaImplNonLeaf_stuck
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address} {transient : Bool}
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok transient s₂)
    (hrun : (whnfNoDeltaImplUncached source flags .stuck).run methods s₂ =
      .ok result s₃) :
    (whnfNoDeltaImplNonLeaf source flags .stuck).run methods s =
      .ok result s₃ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_stuck_beq]
  change EStateM.bind
    ((whnfNoDeltaImplUncached source flags .stuck).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

/-- Transient Nat work bypasses both no-delta cache partitions. -/
theorem whnfNoDeltaImplNonLeaf_transient
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok true s₂)
    (hrun : (whnfNoDeltaImplUncached source flags .collapse).run methods s₂ =
      .ok result s₃) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok result s₃ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind
    ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

/-- Native-reduction re-entry may read a stable entry but never inserts a
new no-delta result after a miss. -/
theorem whnfNoDeltaImplNonLeaf_nativeNoInsert
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    {key : Address × Address}
    (hkey : TcM.whnfKey source s = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : if flags.isFull then
        s₂.env.whnfNoDeltaCache[key]? = none
      else s₂.env.whnfNoDeltaCheapCache[key]? = none)
    (hrun : (whnfNoDeltaImplUncached source flags .collapse).run methods s₂ =
      .ok result s₃)
    (hnative : s₃.inNativeReduce = true) :
    (whnfNoDeltaImplNonLeaf source flags .collapse).run methods s =
      .ok result s₃ := by
  unfold whnfNoDeltaImplNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [htransient]
  cases hfull : flags.isFull
  · have hmiss' : s₂.env.whnfNoDeltaCheapCache[key]? = none := by
      simpa [hfull] using hmiss
    simp [natSuccMode_collapse_beq]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
    simp only [hmiss']
    rw [ReaderT.run_bind]
    change EStateM.bind
      ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
    unfold EStateM.bind
    rw [hrun]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
    simp [hnative]
    rfl
  · have hmiss' : s₂.env.whnfNoDeltaCache[key]? = none := by
      simpa [hfull] using hmiss
    simp [natSuccMode_collapse_beq]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₂ = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) s₂ = .ok s₂ s₂ from rfl]
    simp only [hmiss']
    rw [ReaderT.run_bind]
    change EStateM.bind
      ((whnfNoDeltaImplUncached source flags .collapse).run methods) _ s₂ = _
    unfold EStateM.bind
    rw [hrun]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
    unfold EStateM.bind
    rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
    simp [hnative]
    rfl

namespace WhnfDriverCacheUpdate

theorem noDelta_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .whnfNoDelta key result)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with
        whnfNoDeltaCache := s.env.whnfNoDeltaCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfNoDelta hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

theorem noDeltaCheap_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .whnfNoDeltaCheap key result)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with
        whnfNoDeltaCheapCache :=
          s.env.whnfNoDeltaCheapCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfNoDeltaCheap hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

theorem full_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {result : KExpr .anon}
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.expr .whnf key result)) :
    WhnfStateInv layer semantics trProj world support uvars Δ
      {s with env := {s.env with
        whnfCache := s.env.whnfCache.insert key result}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnf hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end WhnfDriverCacheUpdate

/-- Conditional Hoare closure for the keyed no-delta shell.  The bounded
    semantic loop is proved above; this theorem discharges the cache-control
    flow and leaves only context-key reconciliation, transient lookup state
    preservation, and collision-robust insertion provenance as named
    premises. -/
theorem whnfNoDeltaImplNonLeaf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id (whnfNoDeltaImplStep flags natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s
      (whnfNoDeltaImplNonLeaf source flags natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hinner : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfNoDeltaImplUncached source flags natSuccMode)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.mono
      (WhnfNoDeltaTrace.uncached_wf theory hstep (s := s0) hsupport hsource)
      (fun _ _ h => h) (fun _ _ _ => trivial)
  have hinnerRead : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (do
          let result ← whnfNoDeltaImplUncached source flags natSuccMode
          let _ ← (get : RecM .anon (TcState .anon))
          pure result)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) := by
    intro s0
    apply RecM.WF.bind (hinner s0)
    intro result s3 hpost
    apply RecM.WF.bind
      (Q₁ := fun observed after => observed = s3 ∧ after = s3)
      (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
    intro observed after hread
    rcases hread with ⟨hObserved, hAfter⟩
    subst observed
    subst after
    exact RecM.WF.pure fun _ => hpost
  unfold whnfNoDeltaImplNonLeaf
  apply RecM.WF.bind
    (Q₁ := fun key _ => keys.Matches trProj world s Delta source key)
  · apply RecM.WF.liftTcM
    exact TcM.WF.mono
      (TcM.whnfKey_matches_wf
        (fun key after hctx hrun => hkeyRep s key after hctx hrun))
      (fun key _ h => h.1) (fun _ _ h => h)
  · intro key s1 hmatch
    apply RecM.WF.bind (htransient s1)
    intro transient s2 _
    cases natSuccMode with
    | stuck =>
        simpa [natSuccMode_stuck_beq] using hinnerRead s2
    | collapse =>
        cases transient with
        | true =>
            simpa [natSuccMode_collapse_beq] using hinnerRead s2
        | false =>
            cases hfull : flags.isFull with
            | true =>
                simp only [natSuccMode_collapse_beq, Bool.not_false,
                  Bool.true_and, if_true]
                apply RecM.WF.bind
                  (Q₁ := fun observed after => observed = s2 ∧ after = s2)
                  (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
                intro observed after hread
                rcases hread with ⟨hObserved, hAfter⟩
                subst observed
                subst after
                let found := s2.env.whnfNoDeltaCache[key]?
                cases hfound : found with
                | some cached =>
                    have hcache : s2.env.whnfNoDeltaCache[key]? =
                        some cached := by
                      simpa [found] using hfound
                    simp only [hcache]
                    exact RecM.WF.pure fun hI2 => by
                      have hcached :=
                        (hI2.1.caches.hit (.whnfNoDelta hcache)).supported.2
                      have hmeaning := hI2.1.caches.whnfHitOfMatches
                        (.whnfNoDelta hcache) .whnfNoDelta hsupport hmatch
                      have hstart := WhnfPost.refl hsource
                        (theory.exprWF hI2.2.1 hsource)
                      exact ⟨hcached,
                        hstart.transMeaning theory hI2.2.1.wf hmeaning⟩
                | none =>
                    have hcache : s2.env.whnfNoDeltaCache[key]? = none := by
                      simpa [found] using hfound
                    simp only [hcache]
                    apply RecM.WF.bind (hinner s2)
                    intro result s3 hpost
                    apply RecM.WF.bind
                      (Q₁ := fun observed after => observed = s3 ∧ after = s3)
                      (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
                    intro observed after hread
                    rcases hread with ⟨hObserved, hAfter⟩
                    subst observed
                    subst after
                    cases hnative : s3.inNativeReduce with
                    | true =>
                        simp only [Bool.not_true, Bool.false_and,
                          Bool.false_eq_true, if_false]
                        exact RecM.WF.pure fun _ => hpost
                    | false =>
                        simp only [Bool.not_false, Bool.true_and,
                          if_true]
                        let next := {s3 with env := {s3.env with
                          whnfNoDeltaCache :=
                            s3.env.whnfNoDeltaCache.insert key result}}
                        apply RecM.WF.bind
                          (Q₁ := fun _ after => after = next)
                        · refine RecM.WF.modify (f := fun st =>
                            {st with env := {st.env with
                            whnfNoDeltaCache :=
                              st.env.whnfNoDeltaCache.insert key result}}) ?_
                            (fun _ => rfl)
                          intro hI3
                          exact WhnfDriverCacheUpdate.noDelta_whnfStateInv
                            hI3 (hwrites.noDelta hsupport hpost.1 hmatch
                              (hpost.2.meaning hsource))
                        · intro _ s4 hs4
                          subst s4
                          exact RecM.WF.pure fun _ => hpost
            | false =>
                simp only [natSuccMode_collapse_beq, Bool.not_false,
                  Bool.true_and, if_true]
                apply RecM.WF.bind
                  (Q₁ := fun observed after => observed = s2 ∧ after = s2)
                  (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
                intro observed after hread
                rcases hread with ⟨hObserved, hAfter⟩
                subst observed
                subst after
                let found := s2.env.whnfNoDeltaCheapCache[key]?
                cases hfound : found with
                | some cached =>
                    have hcache : s2.env.whnfNoDeltaCheapCache[key]? =
                        some cached := by
                      simpa [found] using hfound
                    simp only [hcache]
                    exact RecM.WF.pure fun hI2 => by
                      have hcached :=
                        (hI2.1.caches.hit
                          (.whnfNoDeltaCheap hcache)).supported.2
                      have hmeaning := hI2.1.caches.whnfHitOfMatches
                        (.whnfNoDeltaCheap hcache) .whnfNoDeltaCheap
                        hsupport hmatch
                      have hstart := WhnfPost.refl hsource
                        (theory.exprWF hI2.2.1 hsource)
                      exact ⟨hcached,
                        hstart.transMeaning theory hI2.2.1.wf hmeaning⟩
                | none =>
                    have hcache : s2.env.whnfNoDeltaCheapCache[key]? =
                        none := by
                      simpa [found] using hfound
                    simp only [hcache]
                    apply RecM.WF.bind (hinner s2)
                    intro result s3 hpost
                    apply RecM.WF.bind
                      (Q₁ := fun observed after => observed = s3 ∧ after = s3)
                      (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
                    intro observed after hread
                    rcases hread with ⟨hObserved, hAfter⟩
                    subst observed
                    subst after
                    cases hnative : s3.inNativeReduce with
                    | true =>
                        simp only [Bool.not_true, Bool.false_and,
                          Bool.false_eq_true, if_false]
                        exact RecM.WF.pure fun _ => hpost
                    | false =>
                        simp only [Bool.not_false, Bool.true_and,
                          if_true]
                        let next := {s3 with env := {s3.env with
                          whnfNoDeltaCheapCache :=
                            s3.env.whnfNoDeltaCheapCache.insert key result}}
                        apply RecM.WF.bind
                          (Q₁ := fun _ after => after = next)
                        · refine RecM.WF.modify (f := fun st =>
                            {st with env := {st.env with
                            whnfNoDeltaCheapCache :=
                              st.env.whnfNoDeltaCheapCache.insert key result}})
                            ?_ (fun _ => rfl)
                          intro hI3
                          exact
                            WhnfDriverCacheUpdate.noDeltaCheap_whnfStateInv
                              hI3 (hwrites.noDeltaCheap hsupport hpost.1 hmatch
                                (hpost.2.meaning hsource))
                        · intro _ s4 hs4
                          subst s4
                          exact RecM.WF.pure fun _ => hpost

/-- Public no-delta entry for every form that bypasses the legacy-variable
    prefix.  The equation bridge is exact; all semantic assumptions are the
    shell obligations exposed by `whnfNoDeltaImplNonLeaf_wf`. -/
theorem whnfNoDeltaImpl_nonLeaf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hnonleaf : WhnfDriverNonLeaf source)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id (whnfNoDeltaImplStep flags natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfNoDeltaImpl source flags natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  rw [hnonleaf.noDelta_enter]
  exact whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
    hsupport hsource

/-- Conditional Hoare closure for the keyed full-WHNF shell.  Prefix
    instrumentation and the post-miss fuel charge are kept as separate
    operational contracts; the semantic loop, hit validity, and insertion
    invariant are proved compositionally. -/
theorem whnfWithNatSuccModeNonLeaf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hprefix : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (whnfWithNatSuccModePrefix source)
        (fun _ _ => True))
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hcharge : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfWithNatSuccModeMissCharge : RecM .anon Unit)
        (fun _ _ => True))
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s
      (whnfWithNatSuccModeNonLeaf source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hinner : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfWithNatSuccModeUncached source natSuccMode)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.mono
      (WhnfFullTrace.uncached_wf theory hstep (s := s0) hsupport hsource)
      (fun _ _ h => h) (fun _ _ _ => trivial)
  have hwork : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (do
          whnfWithNatSuccModeMissCharge
          let result ← whnfWithNatSuccModeUncached source natSuccMode
          let _ ← (get : RecM .anon (TcState .anon))
          pure result)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) := by
    intro s0
    apply RecM.WF.bind (hcharge s0)
    intro _ s1 _
    apply RecM.WF.bind (hinner s1)
    intro result s2 hpost
    apply RecM.WF.bind
      (Q₁ := fun observed after => observed = s2 ∧ after = s2)
      (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
    intro observed after hread
    rcases hread with ⟨hObserved, hAfter⟩
    subst observed
    subst after
    exact RecM.WF.pure fun _ => hpost
  unfold whnfWithNatSuccModeNonLeaf
  apply RecM.WF.bind (hprefix s)
  intro _ s0 _
  simp only
  apply RecM.WF.bind
    (Q₁ := fun key _ => keys.Matches trProj world s0 Delta source key)
  · apply RecM.WF.liftTcM
    exact TcM.WF.mono
      (TcM.whnfKey_matches_wf
        (fun key after hctx hrun => hkeyRep s0 key after hctx hrun))
      (fun key _ h => h.1) (fun _ _ h => h)
  · intro key s1 hmatch
    apply RecM.WF.bind (htransient s1)
    intro transient s2 _
    cases natSuccMode with
    | stuck =>
        simpa [natSuccMode_stuck_beq] using hwork s2
    | collapse =>
        cases transient with
        | true =>
            simpa [natSuccMode_collapse_beq] using hwork s2
        | false =>
            simp only [natSuccMode_collapse_beq, Bool.not_false,
              Bool.true_and, if_true]
            apply RecM.WF.bind
              (Q₁ := fun observed after => observed = s2 ∧ after = s2)
              (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
            intro observed after hread
            rcases hread with ⟨hObserved, hAfter⟩
            subst observed
            subst after
            let found := s2.env.whnfCache[key]?
            cases hfound : found with
            | some cached =>
                have hcache : s2.env.whnfCache[key]? = some cached := by
                  simpa [found] using hfound
                simp only [hcache]
                exact RecM.WF.pure fun hI2 => by
                  have hcached :=
                    (hI2.1.caches.hit (.whnf hcache)).supported.2
                  have hmeaning := hI2.1.caches.whnfHitOfMatches
                    (.whnf hcache) .whnf hsupport hmatch
                  have hstart := WhnfPost.refl hsource
                    (theory.exprWF hI2.2.1 hsource)
                  exact ⟨hcached,
                    hstart.transMeaning theory hI2.2.1.wf hmeaning⟩
            | none =>
                have hcache : s2.env.whnfCache[key]? = none := by
                  simpa [found] using hfound
                simp only [hcache]
                apply RecM.WF.bind (hcharge s2)
                intro _ s3 _
                apply RecM.WF.bind (hinner s3)
                intro result s4 hpost
                apply RecM.WF.bind
                  (Q₁ := fun observed after => observed = s4 ∧ after = s4)
                  (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
                intro observed after hread
                rcases hread with ⟨hObserved, hAfter⟩
                subst observed
                subst after
                cases hnative : s4.inNativeReduce with
                | true =>
                    simp only [Bool.not_true, Bool.false_and,
                      Bool.false_eq_true, if_false]
                    exact RecM.WF.pure fun _ => hpost
                | false =>
                    simp only [Bool.not_false, Bool.true_and, if_true]
                    let next := {s4 with env := {s4.env with
                      whnfCache := s4.env.whnfCache.insert key result}}
                    apply RecM.WF.bind
                      (Q₁ := fun _ after => after = next)
                    · refine RecM.WF.modify (f := fun st =>
                          {st with env := {st.env with
                            whnfCache := st.env.whnfCache.insert key result}})
                        ?_ (fun _ => rfl)
                      intro hI4
                      exact WhnfDriverCacheUpdate.full_whnfStateInv hI4
                        (hwrites.full hsupport hpost.1 hmatch
                          (hpost.2.meaning hsource))
                    · intro _ s5 hs5
                      subst s5
                      exact RecM.WF.pure fun _ => hpost

/-- Public full-WHNF entry for every direct non-leaf form. -/
theorem whnfWithNatSuccMode_nonLeaf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hnonleaf : WhnfDriverNonLeaf source)
    (hprefix : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (whnfWithNatSuccModePrefix source)
        (fun _ _ => True))
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hcharge : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfWithNatSuccModeMissCharge : RecM .anon Unit)
        (fun _ _ => True))
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfWithNatSuccMode source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  rw [hnonleaf.full_enter]
  exact whnfWithNatSuccModeNonLeaf_wf theory hprefix hkeyRep htransient
    hcharge hstep hwrites hsupport hsource

/-- The full-WHNF trace/statistics prefix preserves every semantic component
    of the K1 state invariant, independently of instrumentation settings. -/
theorem whnfWithNatSuccModePrefix_wf
    {semantics : CacheSemantics} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} (source : KExpr .anon)
    (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfWithNatSuccModePrefix source) (fun _ _ => True) := by
  unfold whnfWithNatSuccModePrefix
  apply RecM.WF.bind
  · apply RecM.WF.liftTcM
    exact TcM.stepTrace_whnf_wf "whnf+" (fun _ => TcM.addr8 source.addr) s
  · intro _ s1 _
    apply RecM.WF.liftTcM
    exact TcM.bumpStats_whnf_wf
      (fun st => {st with whnfCalls := st.whnfCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1

/-- The full-WHNF miss charge preserves the K1 invariant on both outcomes.
    Its only possible error is the underlying `.maxRecFuel`; the bounded-loop
    `.maxRecDepth` classification remains separate in `WhnfLoopError`. -/
theorem whnfWithNatSuccModeMissCharge_wf
    {semantics : CacheSemantics} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfWithNatSuccModeMissCharge : RecM .anon Unit)
      (fun _ _ => True) := by
  unfold whnfWithNatSuccModeMissCharge
  apply RecM.WF.bind
  · apply RecM.WF.liftTcM
    exact TcM.bumpStats_whnf_wf
      (fun st => {st with whnfMisses := st.whnfMisses + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s
  · intro _ s1 _
    apply RecM.WF.liftTcM
    exact TcM.WF.mono
      (TcM.tick.wf (fun _ hI => hI.of_semantic_fields_eq
        rfl rfl rfl rfl rfl rfl rfl rfl))
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)

/-- Full-WHNF public non-leaf closure with the mechanical prefix and charge
    obligations discharged. -/
theorem whnfWithNatSuccMode_nonLeaf_semantic_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hnonleaf : WhnfDriverNonLeaf source)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfWithNatSuccMode source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) :=
  whnfWithNatSuccMode_nonLeaf_wf theory hnonleaf
    (whnfWithNatSuccModePrefix_wf source) hkeyRep htransient
    whnfWithNatSuccModeMissCharge_wf hstep hwrites hsupport hsource

/-- Conditional closure of the actual public no-delta dispatcher for every
    expression form.  Immediate leaves return reflexively; a legacy variable
    performs the proved read-only let test and enters the same keyed shell
    only when necessary. -/
theorem whnfNoDeltaImpl_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id (whnfNoDeltaImplStep flags natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfNoDeltaImpl source flags natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hreflexive : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (pure source)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.pure fun hI =>
      ⟨hsupport, WhnfPost.refl hsource (theory.exprWF hI.2.1 hsource)⟩
  cases source with
  | sort u info =>
      simpa [whnfNoDeltaImpl] using hreflexive s
  | all name bi ty body info =>
      simpa [whnfNoDeltaImpl] using hreflexive s
  | lam name bi ty body info =>
      simpa [whnfNoDeltaImpl] using hreflexive s
  | nat value blob info =>
      simpa [whnfNoDeltaImpl] using hreflexive s
  | str value blob info =>
      simpa [whnfNoDeltaImpl] using hreflexive s
  | const id us info =>
      simpa [whnfNoDeltaImpl] using
        (whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
          hsupport (s := s) hsource)
  | fvar id name info =>
      simpa [whnfNoDeltaImpl] using
        (whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
          hsupport (s := s) hsource)
  | app f arg info =>
      simpa [whnfNoDeltaImpl] using
        (whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
          hsupport (s := s) hsource)
  | letE name ty value body nondep info =>
      simpa [whnfNoDeltaImpl] using
        (whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
          hsupport (s := s) hsource)
  | prj id field value info =>
      simpa [whnfNoDeltaImpl] using
        (whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep hwrites
          hsupport (s := s) hsource)
  | var idx name info =>
      unfold whnfNoDeltaImpl
      apply RecM.WF.bind
      · apply RecM.WF.liftTcM
        exact TcM.isLetVar_wf idx s
      · intro isLet s1 hs1
        subst s1
        cases isLet with
        | false =>
            simpa using hreflexive s
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              pure_bind]
            exact whnfNoDeltaImplNonLeaf_wf theory hkeyRep htransient hstep
              hwrites hsupport (s := s) hsource

/-- Conditional closure of the actual full-WHNF dispatcher for every input
    form and both successor policies. -/
theorem whnfWithNatSuccMode_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {natSuccMode : NatSuccMode}
    {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfWithNatSuccMode source natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) := by
  have hreflexive : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0 (pure source)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => RecM.WF.pure fun hI =>
      ⟨hsupport, WhnfPost.refl hsource (theory.exprWF hI.2.1 hsource)⟩
  have hshell : forall s0,
      RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
        support keys.uvars Delta s0
        (whnfWithNatSuccModeNonLeaf source natSuccMode)
        (fun result _ => support result ∧
          WhnfPost trProj world keys.uvars Delta sourceV result) :=
    fun s0 => whnfWithNatSuccModeNonLeaf_wf theory
      (whnfWithNatSuccModePrefix_wf source) hkeyRep htransient
      whnfWithNatSuccModeMissCharge_wf hstep hwrites hsupport (s := s0)
      hsource
  cases source with
  | sort u info =>
      simpa [whnfWithNatSuccMode] using hreflexive s
  | all name bi ty body info =>
      simpa [whnfWithNatSuccMode] using hreflexive s
  | lam name bi ty body info =>
      simpa [whnfWithNatSuccMode] using hreflexive s
  | nat value blob info =>
      simpa [whnfWithNatSuccMode] using hreflexive s
  | str value blob info =>
      simpa [whnfWithNatSuccMode] using hreflexive s
  | const id us info =>
      simpa [whnfWithNatSuccMode] using hshell s
  | fvar id name info =>
      simpa [whnfWithNatSuccMode] using hshell s
  | app f arg info =>
      simpa [whnfWithNatSuccMode] using hshell s
  | letE name ty value body nondep info =>
      simpa [whnfWithNatSuccMode] using hshell s
  | prj id field value info =>
      simpa [whnfWithNatSuccMode] using hshell s
  | var idx name info =>
      unfold whnfWithNatSuccMode
      apply RecM.WF.bind
      · apply RecM.WF.liftTcM
        exact TcM.isLetVar_wf idx s
      · intro isLet s1 hs1
        subst s1
        cases isLet with
        | false =>
            simpa using hreflexive s
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              pure_bind]
            exact hshell s

/-- Public `RecM.whnfNoDelta` specialization of the conditional dispatcher
    theorem. -/
theorem whnfNoDelta_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta id
      (whnfNoDeltaImplStep .FULL .collapse) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnfNoDelta source)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) :=
  whnfNoDeltaImpl_wf theory hkeyRep htransient hstep hwrites hsupport hsource

/-- Public `RecM.whnf` specialization.  K2 can use this theorem directly
    when proving the corresponding `Methods.WF.whnf` field for `methodsN`. -/
theorem whnf_wf
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Delta : KVLCtx} {source : KExpr .anon}
    {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world keys.uvars)
    (hkeyRep : WhnfKey.Represents keys trProj world source Delta)
    (htransient : TransientNatWork.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta source)
    (hstep : WhnfStep.WF layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × HashSet Address => state.1)
      (whnfWithNatSuccModeStep .collapse) stepError)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Delta s (whnf source)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Delta sourceV result) :=
  whnfWithNatSuccMode_wf theory hkeyRep htransient hstep hwrites hsupport
    hsource

theorem whnfNoDeltaImpl_fullHit_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source cached : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ : TcState .anon}
    (hentry : WhnfDriverEntry methods source s s₀)
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfNoDeltaCache[key]? = some cached)
    (hI : WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ s₂)
    (hsource : support source)
    (hmatch : keys.Matches trProj world s₂ Δ source key) :
    (whnfNoDeltaImpl source flags .collapse).run methods s =
        .ok cached s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfMeaning trProj world keys.uvars Δ source cached := by
  refine ⟨?_, hI, ?_⟩
  · rw [hentry.noDelta_eval flags .collapse]
    exact whnfNoDeltaImplNonLeaf_fullHit hfull hkey htransient hhit
  · exact hI.1.caches.whnfHitOfMatches (.whnfNoDelta hhit)
      .whnfNoDelta hsource hmatch

theorem whnfNoDeltaImpl_cheapHit_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source cached : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ : TcState .anon}
    (hentry : WhnfDriverEntry methods source s s₀)
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hhit : s₂.env.whnfNoDeltaCheapCache[key]? = some cached)
    (hI : WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ s₂)
    (hsource : support source)
    (hmatch : keys.Matches trProj world s₂ Δ source key) :
    (whnfNoDeltaImpl source flags .collapse).run methods s =
        .ok cached s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfMeaning trProj world keys.uvars Δ source cached := by
  refine ⟨?_, hI, ?_⟩
  · rw [hentry.noDelta_eval flags .collapse]
    exact whnfNoDeltaImplNonLeaf_cheapHit hcheap hkey htransient hhit
  · exact hI.1.caches.whnfHitOfMatches (.whnfNoDeltaCheap hhit)
      .whnfNoDeltaCheap hsource hmatch

theorem whnfNoDeltaImpl_fullMiss_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hfull : flags.isFull = true)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCache[key]? = none)
    (htrace : WhnfNoDeltaTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods flags .collapse maxWhnfFuel.toNat
      source s₂ result s₃)
    (hnative : s₃.inNativeReduce = false)
    (hnew : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfNoDelta key result)) :
    let s₄ := {s₃ with env := {s₃.env with
      whnfNoDeltaCache := s₃.env.whnfNoDeltaCache.insert key result}}
    (whnfNoDeltaImpl source flags .collapse).run methods s =
        .ok result s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  dsimp only
  refine ⟨?_, htrace.initialInv, ?_, htrace.meaning theory⟩
  · rw [hentry.noDelta_eval flags .collapse]
    exact whnfNoDeltaImplNonLeaf_fullMiss hfull hkey htransient hmiss
      htrace.uncached_eval hnative
  · exact WhnfDriverCacheUpdate.noDelta_whnfStateInv htrace.finalInv hnew

theorem whnfNoDeltaImpl_cheapMiss_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hcheap : flags.isFull = false)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok false s₂)
    (hmiss : s₂.env.whnfNoDeltaCheapCache[key]? = none)
    (htrace : WhnfNoDeltaTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods flags .collapse maxWhnfFuel.toNat
      source s₂ result s₃)
    (hnative : s₃.inNativeReduce = false)
    (hnew : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support
      (.expr .whnfNoDeltaCheap key result)) :
    let s₄ := {s₃ with env := {s₃.env with
      whnfNoDeltaCheapCache :=
        s₃.env.whnfNoDeltaCheapCache.insert key result}}
    (whnfNoDeltaImpl source flags .collapse).run methods s =
        .ok result s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  dsimp only
  refine ⟨?_, htrace.initialInv, ?_, htrace.meaning theory⟩
  · rw [hentry.noDelta_eval flags .collapse]
    exact whnfNoDeltaImplNonLeaf_cheapMiss hcheap hkey htransient hmiss
      htrace.uncached_eval hnative
  · exact WhnfDriverCacheUpdate.noDeltaCheap_whnfStateInv
      htrace.finalInv hnew

theorem whnfNoDeltaImpl_stuck_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {transient : Bool}
    {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok transient s₂)
    (htrace : WhnfNoDeltaTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods flags .stuck maxWhnfFuel.toNat
      source s₂ result s₃) :
    (whnfNoDeltaImpl source flags .stuck).run methods s = .ok result s₃ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₃ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  refine ⟨?_, htrace.initialInv, htrace.finalInv, htrace.meaning theory⟩
  rw [hentry.noDelta_eval flags .stuck]
  exact whnfNoDeltaImplNonLeaf_stuck hkey htransient htrace.uncached_eval

theorem whnfNoDeltaImpl_transient_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {flags : WhnfFlags} {source result : KExpr .anon}
    {key : Address × Address} {s s₀ s₁ s₂ s₃ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hkey : TcM.whnfKey source s₀ = .ok key s₁)
    (htransient : (isTransientNatLiteralWork source).run methods s₁ =
      .ok true s₂)
    (htrace : WhnfNoDeltaTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods flags .collapse maxWhnfFuel.toNat
      source s₂ result s₃) :
    (whnfNoDeltaImpl source flags .collapse).run methods s =
        .ok result s₃ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₂ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₃ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  refine ⟨?_, htrace.initialInv, htrace.finalInv, htrace.meaning theory⟩
  rw [hentry.noDelta_eval flags .collapse]
  exact whnfNoDeltaImplNonLeaf_transient hkey htransient
    htrace.uncached_eval

/-! ### Exact full-WHNF instrumentation/cache equations -/

theorem whnfWithNatSuccModeNonLeaf_hit
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {source cached : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hhit : s₃.env.whnfCache[key]? = some cached) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok cached s₃ := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only [hhit]
  rfl

theorem whnfWithNatSuccModeNonLeaf_miss
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hmiss : s₃.env.whnfCache[key]? = none)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (hrun : (whnfWithNatSuccModeUncached source .collapse).run methods s₄ =
      .ok result s₅)
    (hnative : s₅.inNativeReduce = false) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok result {s₅ with env := {s₅.env with
        whnfCache := s₅.env.whnfCache.insert key result}} := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hcharge]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeUncached source .collapse).run methods) _ s₄ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₅ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₅ = .ok s₅ s₅ from rfl]
  simp only
  rw [if_pos hnative]
  rfl

/-- Stuck-succ full WHNF still pays the miss charge but bypasses both the
outer cache read and write. -/
theorem whnfWithNatSuccModeNonLeaf_stuck
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    {transient : Bool}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok transient s₃)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (hrun : (whnfWithNatSuccModeUncached source .stuck).run methods s₄ =
      .ok result s₅) :
    (whnfWithNatSuccModeNonLeaf source .stuck).run methods s =
      .ok result s₅ := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_stuck_beq]
  change EStateM.bind
    ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hcharge]
  simp only
  change EStateM.bind
    ((whnfWithNatSuccModeUncached source .stuck).run methods) _ s₄ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

/-- Transient full-WHNF work is charged but cannot observe or populate the
outer cache. -/
theorem whnfWithNatSuccModeNonLeaf_transient
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok true s₃)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (hrun : (whnfWithNatSuccModeUncached source .collapse).run methods s₄ =
      .ok result s₅) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok result s₅ := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind
    ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hcharge]
  simp only
  change EStateM.bind
    ((whnfWithNatSuccModeUncached source .collapse).run methods) _ s₄ = _
  unfold EStateM.bind
  rw [hrun]
  rfl

theorem whnfWithNatSuccModeNonLeaf_nativeNoInsert
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {source result : KExpr .anon} {key : Address × Address}
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hmiss : s₃.env.whnfCache[key]? = none)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (hrun : (whnfWithNatSuccModeUncached source .collapse).run methods s₄ =
      .ok result s₅)
    (hnative : s₅.inNativeReduce = true) :
    (whnfWithNatSuccModeNonLeaf source .collapse).run methods s =
      .ok result s₅ := by
  unfold whnfWithNatSuccModeNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModePrefix source).run methods) _ s = _
  unfold EStateM.bind
  rw [hprefix]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ s₁ = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isTransientNatLiteralWork source).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [htransient]
  simp [natSuccMode_collapse_beq]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₃ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₃ = .ok s₃ s₃ from rfl]
  simp only [hmiss]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hcharge]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((whnfWithNatSuccModeUncached source .collapse).run methods) _ s₄ = _
  unfold EStateM.bind
  rw [hrun]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s₅ = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s₅ = .ok s₅ s₅ from rfl]
  simp [hnative]
  rfl

theorem whnfWithNatSuccMode_hit_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {source cached : KExpr .anon} {key : Address × Address}
    {s s₀ s₁ s₂ s₃ : TcState .anon}
    (hentry : WhnfDriverEntry methods source s s₀)
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s₀ =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hhit : s₃.env.whnfCache[key]? = some cached)
    (hI : WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
      trProj world support keys.uvars Δ s₃)
    (hsource : support source)
    (hmatch : keys.Matches trProj world s₃ Δ source key) :
    (whnfWithNatSuccMode source .collapse).run methods s =
        .ok cached s₃ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₃ ∧
      WhnfMeaning trProj world keys.uvars Δ source cached := by
  refine ⟨?_, hI, ?_⟩
  · rw [hentry.full_eval .collapse]
    exact whnfWithNatSuccModeNonLeaf_hit hprefix hkey htransient hhit
  · exact hI.1.caches.whnfHitOfMatches (.whnf hhit) .whnf hsource hmatch

theorem whnfWithNatSuccMode_miss_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {source result : KExpr .anon} {key : Address × Address}
    {s s₀ s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s₀ =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok false s₃)
    (hmiss : s₃.env.whnfCache[key]? = none)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (htrace : WhnfFullTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods .collapse maxWhnfFuel.toNat
      (source, {}) s₄ result s₅)
    (hnative : s₅.inNativeReduce = false)
    (hnew : CacheProvenance (whnfCacheSemantics keys trProj fallback)
      (CacheAuthority.stable world) support (.expr .whnf key result)) :
    let s₆ := {s₅ with env := {s₅.env with
      whnfCache := s₅.env.whnfCache.insert key result}}
    (whnfWithNatSuccMode source .collapse).run methods s =
        .ok result s₆ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₆ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  dsimp only
  refine ⟨?_, htrace.initialInv, ?_, htrace.meaning theory⟩
  · rw [hentry.full_eval .collapse]
    exact whnfWithNatSuccModeNonLeaf_miss hprefix hkey htransient hmiss
      hcharge htrace.uncached_eval hnative
  · exact WhnfDriverCacheUpdate.full_whnfStateInv htrace.finalInv hnew

theorem whnfWithNatSuccMode_stuck_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {source result : KExpr .anon} {key : Address × Address}
    {transient : Bool} {s s₀ s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s₀ =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok transient s₃)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (htrace : WhnfFullTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods .stuck maxWhnfFuel.toNat
      (source, {}) s₄ result s₅) :
    (whnfWithNatSuccMode source .stuck).run methods s = .ok result s₅ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₅ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  refine ⟨?_, htrace.initialInv, htrace.finalInv, htrace.meaning theory⟩
  rw [hentry.full_eval .stuck]
  exact whnfWithNatSuccModeNonLeaf_stuck hprefix hkey htransient hcharge
    htrace.uncached_eval

theorem whnfWithNatSuccMode_transient_acceptance
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {layer : WhnfLayer} {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {Δ : KVLCtx} {methods : Methods .anon}
    {source result : KExpr .anon} {key : Address × Address}
    {s s₀ s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hentry : WhnfDriverEntry methods source s s₀)
    (hprefix : (whnfWithNatSuccModePrefix source).run methods s₀ =
      .ok () s₁)
    (hkey : TcM.whnfKey source s₁ = .ok key s₂)
    (htransient : (isTransientNatLiteralWork source).run methods s₂ =
      .ok true s₃)
    (hcharge : (whnfWithNatSuccModeMissCharge : RecM .anon Unit).run
      methods s₃ = .ok () s₄)
    (htrace : WhnfFullTrace layer
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ methods .collapse maxWhnfFuel.toNat
      (source, {}) s₄ result s₅) :
    (whnfWithNatSuccMode source .collapse).run methods s =
        .ok result s₅ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₄ ∧
      WhnfStateInv layer (whnfCacheSemantics keys trProj fallback)
        trProj world support keys.uvars Δ s₅ ∧
      WhnfMeaning trProj world keys.uvars Δ source result := by
  refine ⟨?_, htrace.initialInv, htrace.finalInv, htrace.meaning theory⟩
  rw [hentry.full_eval .collapse]
  exact whnfWithNatSuccModeNonLeaf_transient hprefix hkey htransient
    hcharge htrace.uncached_eval

/-- Public full WHNF is exactly collapse-mode WHNF; the theorem is kept as a
named bridge for the eventual `Methods.WF` field. -/
theorem whnf_public_eq_whnfWithNatSuccMode (e : KExpr .anon) :
    whnf e = whnfWithNatSuccMode e .collapse := rfl

/-- Syntactic forms on which production `RecM.whnf` returns immediately,
before tracing, statistics, cache lookup, fuel, or any method back-edge. -/
inductive WhnfLeaf : KExpr .anon → Prop
  | sort {u info} : WhnfLeaf (.sort u info)
  | all {name bi ty body info} : WhnfLeaf (.all name bi ty body info)
  | lam {name bi ty body info} : WhnfLeaf (.lam name bi ty body info)
  | nat {value blob info} : WhnfLeaf (.nat value blob info)
  | str {value blob info} : WhnfLeaf (.str value blob info)

namespace WhnfLeaf

/-- Exact operational equation for every immediate-return form. -/
theorem eval {e : KExpr .anon} (h : WhnfLeaf e) :
    RecM.whnf e = pure e := by
  cases h <;> rfl

end WhnfLeaf

/-- Forms on which structural WHNF returns before key computation and cache
access.  Unlike full WHNF, constants are leaves because core reduction never
performs delta unfolding. -/
inductive WhnfCoreLeaf : KExpr .anon → Prop
  | sort {u info} : WhnfCoreLeaf (.sort u info)
  | all {name bi ty body info} : WhnfCoreLeaf (.all name bi ty body info)
  | lam {name bi ty body info} : WhnfCoreLeaf (.lam name bi ty body info)
  | nat {value blob info} : WhnfCoreLeaf (.nat value blob info)
  | str {value blob info} : WhnfCoreLeaf (.str value blob info)
  | const {id us info} : WhnfCoreLeaf (.const id us info)

namespace WhnfCoreLeaf

/-- Exact production equation, uniform over full and cheap projection flags. -/
theorem eval {e : KExpr .anon} (h : WhnfCoreLeaf e)
    (flags : WhnfFlags) :
    RecM.whnfCoreWithFlags e flags = pure e := by
  cases h <;> rfl

end WhnfCoreLeaf

/-- A recursive head-callback result that cannot enter the beta branch.
Although `collectSpine` never returns an application as its *input* head, a
semantically closed callback may return an application definitionally equal
to that head.  Production treats such a result in the ordinary changed or
unchanged non-lambda path, so the verification classifier must include it. -/
inductive WhnfCoreNonLambda : KExpr .anon → Prop
  | var {idx name info} : WhnfCoreNonLambda (.var idx name info)
  | fvar {id name info} : WhnfCoreNonLambda (.fvar id name info)
  | sort {u info} : WhnfCoreNonLambda (.sort u info)
  | app {f arg info} : WhnfCoreNonLambda (.app f arg info)
  | all {name bi ty body info} : WhnfCoreNonLambda (.all name bi ty body info)
  | letE {name ty val body nondep info} :
      WhnfCoreNonLambda (.letE name ty val body nondep info)
  | prj {id field val info} : WhnfCoreNonLambda (.prj id field val info)
  | nat {value blob info} : WhnfCoreNonLambda (.nat value blob info)
  | str {value blob info} : WhnfCoreNonLambda (.str value blob info)
  | const {id us info} : WhnfCoreNonLambda (.const id us info)

/-! ### Application-spine rebuilding -/

/-- A structurally recursive list view of an application spine.  The proof
below connects it to production's accumulator/reverse implementation, while
this view makes translation induction direct. -/
def appSpineView (e : KExpr m) : KExpr m × List (KExpr m) :=
  match e with
  | .app f a _ =>
      let (head, args) := appSpineView f
      (head, args ++ [a])
  | e => (e, [])
termination_by structural e

/-- Production's accumulator contains the reversed pending suffix; the
structural view contributes the already ordered prefix. -/
theorem appSpineView_go (e : KExpr m) (acc : Array (KExpr m)) :
    let (head, args) := appSpineView e
    (KExpr.collectSpine.go e acc).1 = head ∧
      (KExpr.collectSpine.go e acc).2.toList =
        args ++ acc.toList.reverse := by
  induction e generalizing acc <;>
    simp_all [appSpineView, KExpr.collectSpine.go,
      List.reverse_append, List.append_assoc]

/-- The structural view is extensionally the actual production spine. -/
theorem appSpineView_collectSpine (e : KExpr m) :
    let (head, args) := appSpineView e
    e.collectSpine.1 = head ∧ e.collectSpine.2.toList = args := by
  simpa [KExpr.collectSpine] using appSpineView_go e #[]

/-- Translation-indexed spine view.  Each extension retains the exact
function and argument typing derivations needed for semantic application
congruence. -/
inductive TrAppSpine (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Δ : KVLCtx) (head : KExpr .anon) :
    List (KExpr .anon) → VExpr → Prop
  | head {headV} :
      TrKExprS env uvars nameOf trProj Δ head headV →
      TrAppSpine env uvars nameOf trProj Δ head [] headV
  | app {args fV arg argV A B} :
      TrAppSpine env uvars nameOf trProj Δ head args fV →
      env.HasType uvars Δ.toCtx fV (.forallE A B) →
      env.HasType uvars Δ.toCtx argV A →
      TrKExprS env uvars nameOf trProj Δ arg argV →
      TrAppSpine env uvars nameOf trProj Δ head (args ++ [arg])
        (.app fV argV)

/-- Every structural translation induces the corresponding typed spine
translation; expression metadata is deliberately absent from the view. -/
theorem trAppSpine_of_tr
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Δ : KVLCtx} {e : KExpr .anon} {eV : VExpr}
    (h : TrKExprS env uvars nameOf trProj Δ e eV) :
    let (head, args) := appSpineView e
    TrAppSpine env uvars nameOf trProj Δ head args eV := by
  induction h with
  | var h => exact .head (.var h)
  | fvar h => exact .head (.fvar h)
  | sort h => exact .head (.sort h)
  | const h₁ h₂ h₃ h₄ => exact .head (.const h₁ h₂ h₃ h₄)
  | @app Δ f arg md fV argV A B h₁ h₂ htf hta ihf iha =>
      simp only [appSpineView]
      generalize hview : appSpineView f = view at ihf
      cases view with
      | mk head args =>
          exact .app ihf h₁ h₂ hta
  | lam h₁ h₂ h₃ ih₂ ih₃ => exact .head (.lam h₁ h₂ h₃)
  | all h₁ h₂ h₃ h₄ ih₃ ih₄ => exact .head (.all h₁ h₂ h₃ h₄)
  | letE h₁ h₂ h₃ h₄ ih₂ ih₃ ih₄ => exact .head (.letE h₁ h₂ h₃ h₄)
  | prj h₁ h₂ h₃ ih₁ => exact .head (.prj h₁ h₂ h₃)
  | nat h => exact .head (.nat h)
  | str h => exact .head (.str h)

namespace TrAppSpine

/-- Every concrete argument named by a typed spine retains its own
translation and typing derivation.  This is the membership form needed by
descriptor-driven reducers whose argument positions are discovered only at
runtime. -/
theorem argument
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {head arg : KExpr .anon}
    {args : List (KExpr .anon)} {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head args resultV)
    (hmem : arg ∈ args) :
    ∃ argV A,
      env.HasType uvars Delta.toCtx argV A ∧
        TrKExprS env uvars nameOf trProj Delta arg argV := by
  induction h with
  | head hhead => simp at hmem
  | app hprefix hfun hlast hlastTr ih =>
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hprefixMem | rfl
      · exact ih hprefixMem
      · exact ⟨_, _, hlast, hlastTr⟩

/-- Rebuild the canonical metadata-free raw spine without changing its
Theory translation. -/
theorem tr
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Δ : KVLCtx} {head : KExpr .anon} {args : List (KExpr .anon)}
    {eV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Δ head args eV) :
    TrKExprS env uvars nameOf trProj Δ
      (args.foldl KExpr.mkApp head) eV := by
  cases h with
  | head h => exact h
  | app hprefix hfun harg htr =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [KExpr.mkApp_shape]
      exact .app hfun harg hprefix.tr htr

end TrAppSpine

/-- Re-index a source translation by the head and array returned by the
actual production `collectSpine`. -/
theorem trAppSpine_of_collectSpine
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Δ : KVLCtx} {source head : KExpr .anon}
    {args : Array (KExpr .anon)} {sourceV : VExpr}
    (hsource : TrKExprS env uvars nameOf trProj Δ source sourceV)
    (hspine : source.collectSpine = (head, args)) :
    TrAppSpine env uvars nameOf trProj Δ head args.toList sourceV := by
  generalize hview : appSpineView source = view
  cases view with
  | mk viewHead viewArgs =>
      have htr := trAppSpine_of_tr hsource
      rw [hview] at htr
      have hv := appSpineView_collectSpine source
      rw [hview] at hv
      have hsHead := congrArg Prod.fst hspine
      have hsArgs := congrArg (fun p => p.2.toList) hspine
      have hhead : head = viewHead := hsHead.symm.trans hv.1
      have hargs : args.toList = viewArgs := hsArgs.symm.trans hv.2
      simpa only [hhead, hargs] using htr

/-- Pure left-to-right result of production's application-spine helper.
Only the suffix beginning at `consumed` is rebuilt. -/
def finishAppResultSpec (result : KExpr .anon)
    (args : Array (KExpr .anon)) (consumed : Nat) : KExpr .anon :=
  KExpr.mkAppN result (args.extract consumed args.size)

/-- The imperative `for` loop in `finishAppResult` is exactly a monadic
left fold over the requested suffix.  This equation fixes both argument order
and the consumed-prefix boundary without changing the production helper. -/
theorem finishAppResult_eq_foldlM (result : KExpr m)
    (args : Array (KExpr m)) (consumed : Nat) :
    finishAppResult result args consumed =
      (args.extract consumed args.size).foldlM (m := RecM m)
        (fun result arg => liftM (TcM.intern (KExpr.mkApp result arg)))
        result := by
  unfold finishAppResult
  simp [Array.forIn_yield_eq_foldlM]

/-- Production's application-suffix rebuild is operationally total.  This
fact is deliberately weaker than semantic correctness: without a finite
request certificate, an intern collision may change the returned syntax and
the post-state need not satisfy the checker invariant.  The finite-request
closure uses totality only to rule out a late miss/error after a primitive
result was selected. -/
theorem finishAppResult_total
    {methods : Methods .anon} {s : TcState .anon}
    (result : KExpr .anon) (args : Array (KExpr .anon)) (consumed : Nat) :
    ∃ final s',
      (finishAppResult result args consumed).run methods s = .ok final s' := by
  rw [finishAppResult_eq_foldlM]
  rw [← Array.foldlM_toList]
  generalize hrest : (args.extract consumed args.size).toList = rest
  clear hrest
  induction rest generalizing result s with
  | nil =>
      exact ⟨result, s, rfl⟩
  | cons arg rest ih =>
      rw [List.foldlM_cons, ReaderT.run_bind, ReaderT.run_monadLift]
      let pair := internExprM (KExpr.mkApp result arg) s.env.intern
      let next := {s with env := {s.env with intern := pair.2}}
      obtain ⟨final, s', htail⟩ := ih (result := pair.1) (s := next)
      refine ⟨final, s', ?_⟩
      change EStateM.bind (TcM.intern (KExpr.mkApp result arg)) _ s = _
      unfold EStateM.bind TcM.intern TcM.runIntern
      exact htail

/-- Exact one-argument specialization used by adversarial fixtures and by
single-node suffix certificates. -/
theorem finishAppResult_one
    {methods : Methods .anon} {s s' : TcState .anon}
    {result arg final : KExpr .anon}
    (hintern : TcM.intern (KExpr.mkApp result arg) s = .ok final s') :
    (finishAppResult result #[arg] 0).run methods s = .ok final s' := by
  rw [finishAppResult_eq_foldlM]
  change EStateM.bind (TcM.intern (KExpr.mkApp result arg)) EStateM.Result.ok s = _
  simp only [EStateM.bind]
  rw [hintern]

/-- Finite execution certificate for rebuilding an application suffix.
Each node records the exact dynamically generated application passed to
`TcM.intern`; the indices force a left-to-right spine and expose every support
and collision-freedom obligation through `WalkerRequest.internExpr`. -/
inductive FinishAppRequests (requests : List WalkerRequest) :
    List (KExpr .anon) → KExpr .anon → KExpr .anon → Prop
  | nil (result) : FinishAppRequests requests [] result result
  | cons {arg result rest final}
      (head : WalkerRequest.internExpr (KExpr.mkApp result arg) ∈ requests)
      (tail : FinishAppRequests requests rest
        (KExpr.mkApp result arg) final) :
      FinishAppRequests requests (arg :: rest) result final

namespace FinishAppRequests

/-- The certificate's final expression is the pure left fold described by
its indices; an argument permutation cannot inhabit this equality. -/
theorem result_eq_foldl {requests : List WalkerRequest}
    {rest : List (KExpr .anon)} {result final : KExpr .anon}
    (h : FinishAppRequests requests rest result final) :
    final = rest.foldl KExpr.mkApp result := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    simpa only [List.foldl_cons] using ih

/-- Every intermediate application requested by a certificate—and hence its
final result—is covered by the finite run support. -/
theorem support {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {runSupport : RunSupport}
    (hrun : RunAssumptions initial program requests runSupport)
    {rest : List (KExpr .anon)} {result final : KExpr .anon}
    (h : FinishAppRequests requests rest result final)
    (hresult : runSupport result) : runSupport final := by
  induction h with
  | nil => exact hresult
  | cons head tail ih =>
    exact ih (hrun.coverage.internExpr head)

/-- Execute the certified list fold.  Each direct intern request preserves
the full invariant; their intern-only frames compose transitively. -/
theorem foldlM_eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {rest : List (KExpr .anon)} {result final : KExpr .anon}
    (h : FinishAppRequests requests rest result final)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s',
      (rest.foldlM (m := RecM .anon)
          (fun result arg => liftM (TcM.intern (KExpr.mkApp result arg)))
          result).run methods s = .ok final s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  induction h generalizing s with
  | nil =>
    exact ⟨s, rfl, hI, InternUpdateFrame.refl s⟩
  | cons head tail ih =>
    obtain ⟨s₁, hstep, hI₁, hframe₁⟩ :=
      hrun.internExpr_whnf_eval head hI
    obtain ⟨s₂, htail, hI₂, hframe₂⟩ := ih hI₁
    refine ⟨s₂, ?_, hI₂, hframe₁.trans hframe₂⟩
    rw [List.foldlM_cons, ReaderT.run_bind, ReaderT.run_monadLift]
    change EStateM.bind (TcM.intern _) _ s = _
    unfold EStateM.bind
    rw [hstep]
    exact htail

/-- Execute the actual production helper from a certificate for precisely
the extracted suffix. -/
theorem eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {args : Array (KExpr .anon)} {consumed : Nat}
    {result final : KExpr .anon}
    (h : FinishAppRequests requests
      (args.extract consumed args.size).toList result final)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s',
      (finishAppResult result args consumed).run methods s = .ok final s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  obtain ⟨s', hrun', hI', hframe⟩ := h.foldlM_eval hrun hI
  refine ⟨s', ?_, hI', hframe⟩
  rw [finishAppResult_eq_foldlM]
  simpa only [← Array.foldlM_toList] using hrun'

/-- The certificate result agrees with the named pure helper specification. -/
theorem final_eq_spec {requests : List WalkerRequest}
    {args : Array (KExpr .anon)} {consumed : Nat}
    {result final : KExpr .anon}
    (h : FinishAppRequests requests
      (args.extract consumed args.size).toList result final) :
    final = finishAppResultSpec result args consumed := by
  rw [finishAppResultSpec, KExpr.mkAppN]
  simpa only [Array.foldl_toList] using h.result_eq_foldl

end FinishAppRequests

/-- Exact production step for successful legacy de-Bruijn zeta reduction.
The lookup may grow only the intern table because it lifts the stored value
to the current depth. -/
theorem whnfCoreWithFlagsStep_varZeta
    {methods : Methods .anon} {s s' : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {flags : WhnfFlags} {val : KExpr .anon}
    (hlookup : TcM.lookupLetVal idx s = .ok (some val) s') :
    (whnfCoreWithFlagsStep (.var idx name md) flags).run methods s =
      .ok (.next val) s' := by
  unfold whnfCoreWithFlagsStep
  change EStateM.bind (TcM.lookupLetVal idx) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- Exact production step for let-bound fvar zeta reduction.  This branch
is state-pure and does not consult the recursive method table. -/
theorem whnfCoreWithFlagsStep_fvarZeta
    {methods : Methods .anon} {s : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {declName : Mode.anon.F Name} {ty val : KExpr .anon}
    {flags : WhnfFlags}
    (hfind : s.lctx.find? id = some (.ldecl declName ty val)) :
    (whnfCoreWithFlagsStep (.fvar id name md) flags).run methods s =
      .ok (.next val) s := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  rw [hfind]
  rfl

/-- Exact production fallback for a legacy variable that is not let-bound.
    Any successful `none` lookup is state-pure by
    `TcM.lookupLetVal_none_state`. -/
theorem whnfCoreWithFlagsStep_varDone
    {methods : Methods .anon} {s s' : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {flags : WhnfFlags}
    (hlookup : TcM.lookupLetVal idx s = .ok none s') :
    (whnfCoreWithFlagsStep (.var idx name md) flags).run methods s =
      .ok (.done (.var idx name md)) s' := by
  unfold whnfCoreWithFlagsStep
  change EStateM.bind (TcM.lookupLetVal idx) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  rfl

/-- Exact production fallback for an fvar whose declaration is absent or a
    regular binder.  The quantified exclusion covers both lookup outcomes
    without assuming that a translated fvar must be present in arbitrary raw
    state. -/
theorem whnfCoreWithFlagsStep_fvarDone
    {methods : Methods .anon} {s : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {flags : WhnfFlags}
    (hnot : ∀ declName ty val,
      s.lctx.find? id ≠ some (.ldecl declName ty val)) :
    (whnfCoreWithFlagsStep (.fvar id name md) flags).run methods s =
      .ok (.done (.fvar id name md)) s := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  cases hfind : s.lctx.find? id with
  | none => rfl
  | some decl =>
    cases decl with
    | cdecl => rfl
    | ldecl declName ty val => exact False.elim (hnot declName ty val hfind)

/-- Exact production step for an explicit let expression.  The named
single-substitution walker is the only stateful action on this branch. -/
theorem whnfCoreWithFlagsStep_letE
    {methods : Methods .anon} {s s' : TcState .anon}
    {name : Mode.anon.F Name} {ty val body result : KExpr .anon}
    {nondep : Bool} {info : ExprInfo .anon} {flags : WhnfFlags}
    (hwalk : TcM.runIntern (subst body val 0) s = .ok result s') :
    (whnfCoreWithFlagsStep (.letE name ty val body nondep info) flags).run
      methods s = .ok (.next result) s' := by
  unfold whnfCoreWithFlagsStep
  change ReaderT.run
    (BoundedStep.next <$> liftM (TcM.runIntern (subst body val 0)) :
      RecM .anon (BoundedStep (KExpr .anon) (KExpr .anon))) methods s = _
  rw [ReaderT.run_map, ReaderT.run_monadLift]
  rw [← bind_pure_comp]
  change EStateM.bind (TcM.runIntern (subst body val 0))
    (fun r => pure (BoundedStep.next r)) s = _
  unfold EStateM.bind
  rw [hwalk]
  rfl

/-- Exact production step for a direct one-argument beta redex.  The head
callback equation is intentionally stronger than `Methods.WF`: semantic
closure alone cannot force a callback to return this syntactic lambda. -/
theorem whnfCoreWithFlagsStep_betaOne
    {methods : Methods .anon} {s s' : TcState .anon}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg result : KExpr .anon}
    {lamMd appMd : ExprInfo .anon} {flags : WhnfFlags}
    (hhead : methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags s =
      .ok (.lam nm bi ty body lamMd) s)
    (hwalk : TcM.runIntern (simulSubst body #[arg] 0) s = .ok result s') :
    (whnfCoreWithFlagsStep
      (.app (.lam nm bi ty body lamMd) arg appMd) flags).run methods s =
      .ok (.next result) s' := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  change EStateM.bind
    (methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp [consumeBetaLams, consumeBetaLamsFuel]
  change ReaderT.run
    (BoundedStep.next <$> liftM
      (TcM.runIntern (simulSubst body #[arg] 0)) :
        RecM .anon (BoundedStep (KExpr .anon) (KExpr .anon))) methods s = _
  rw [ReaderT.run_map, ReaderT.run_monadLift]
  rw [← bind_pure_comp]
  change EStateM.bind (TcM.runIntern (simulSubst body #[arg] 0))
    (fun r => pure (BoundedStep.next r)) s = _
  unfold EStateM.bind
  rw [hwalk]
  rfl

/-- Exact production step for general multi-argument beta.  Unlike the
single-argument convenience theorem, this exposes the lambda-peeling result,
the simultaneous-substitution execution, and rebuilding of only the
unconsumed argument suffix. -/
theorem whnfCoreWithFlagsStep_betaMany
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {f arg head : KExpr .anon} {appInfo : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body body₀ : KExpr .anon} {lamInfo : ExprInfo .anon}
    {consumed : Array (KExpr .anon)} {substituted result : KExpr .anon}
    {flags : WhnfFlags}
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine = (head, args))
    (hhead : methods.whnfCoreFlags head flags s =
      .ok (.lam nm bi ty body lamInfo) s₁)
    (hconsume : consumeBetaLams (.lam nm bi ty body lamInfo) args =
      (body₀, consumed))
    (hnonempty : (!consumed.isEmpty) = true)
    (hsubst : TcM.runIntern (simulSubst body₀ consumed.reverse 0) s₁ =
      .ok substituted s₂)
    (hfinish : (finishAppResult substituted args consumed.size).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsStep (.app f arg appInfo) flags).run methods s =
      .ok (.next result) s₃ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  rw [hconsume]
  simp only
  rw [hnonempty]
  simp only [↓reduceIte]
  change ReaderT.run
    ((liftM (TcM.runIntern (simulSubst body₀ consumed.reverse 0)) >>= fun r => do
      pure PUnit.unit
      let r ← finishAppResult r args consumed.size
      pure (BoundedStep.next r)) :
        RecM .anon (BoundedStep (KExpr .anon) (KExpr .anon))) methods s₁ = _
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.runIntern (simulSubst body₀ consumed.reverse 0)) _ s₁ = _
  unfold EStateM.bind
  rw [hsubst]
  change EStateM.bind
    (ReaderT.run (finishAppResult substituted args consumed.size) methods) _
      s₂ = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

/-- Exact production step for a successful projection reduction.  Both the
cheap and full value-WHNF policies are represented by the same explicit
callback equation, followed by the actual `tryProjReduce` execution. -/
theorem whnfCoreWithFlagsStep_projection
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {id : KId .anon} {field : UInt64} {value wvalue result : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok (some result) s₂) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
      .ok (.next result) s₂ := by
  unfold whnfCoreWithFlagsStep
  simp only
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]
    rfl

/-- Exact production fallback for a projection whose value callback succeeds
but whose syntax-directed reduction helper returns `none`.  The returned
expression is the original projection, not the normalized `wvalue`. -/
theorem whnfCoreWithFlagsStep_projectionDone
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {id : KId .anon} {field : UInt64} {value wvalue : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok none s₂) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
      .ok (.done (.prj id field value info)) s₂ := by
  unfold whnfCoreWithFlagsStep
  simp only
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]
    rfl

/-- Errors from the projection value callback are propagated with their
post-state before the reduction helper is entered. -/
theorem whnfCoreWithFlagsStep_projectionWhnfError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {id : KId .anon} {field : UInt64} {value : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags} {err : TcError .anon}
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .error err s₁) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
      .error err s₁ := by
  unfold whnfCoreWithFlagsStep
  simp only
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]

/-- Errors from `tryProjReduce` retain both the exact error and the helper's
partial post-state. -/
theorem whnfCoreWithFlagsStep_projectionReduceError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {id : KId .anon} {field : UInt64} {value wvalue : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags} {err : TcError .anon}
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .error err s₂) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
      .error err s₂ := by
  unfold whnfCoreWithFlagsStep
  simp only
  cases hcheap : flags.cheapProj <;>
      simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hwhnf]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind
      (ReaderT.run (tryProjReduce id field wvalue) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hreduce]

/-- Exact production step for a successful ordinary iota reduction after
the recursive head callback returns the same recursor constant.  State
changes made by that callback remain explicit as `s₁`; semantic closure does
not imply the syntactic self-return equation. -/
theorem whnfCoreWithFlagsStep_iota
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {recId : KId .anon} {us : Array (KUniv .anon)}
    {headInfo appInfo : ExprInfo .anon} {f arg result : KExpr .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine =
      (.const recId us headInfo, args))
    (hhead : methods.whnfCoreFlags (.const recId us headInfo) flags s =
      .ok (.const recId us headInfo) s₁)
    (hself : ((.const recId us headInfo : KExpr .anon) !=
      .const recId us headInfo) = false)
    (hiota :
      (tryIotaWithFlags (.app f arg appInfo) flags).run methods s₁ =
        .ok (some result) s₂) :
    (whnfCoreWithFlagsStep (.app f arg appInfo) flags).run methods s =
      .ok (.next result) s₂ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind
    (methods.whnfCoreFlags (.const recId us headInfo) flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  rw [hself]
  change EStateM.bind
    (ReaderT.run (tryIotaWithFlags (.app f arg appInfo) flags) methods) _
      s₁ = _
  unfold EStateM.bind
  rw [hiota]
  rfl

/-- Exact stuck-application fallback after the recursive head callback
returns the original non-lambda head and the iota helper returns `none`. -/
theorem whnfCoreWithFlagsStep_appUnchangedDone
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {f arg head : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda head)
    (hhead : methods.whnfCoreFlags head flags s = .ok head s₁)
    (hself : (head != head) = false)
    (hiota : (tryIotaWithFlags (.app f arg info) flags).run methods s₁ =
      .ok none s₂) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .ok (.done (.app f arg info)) s₂ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hself]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags (.app f arg info) flags) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hiota]
    rfl

/-- A failing recursive head callback is propagated before beta, rebuilding,
or iota dispatch. -/
theorem whnfCoreWithFlagsStep_appHeadError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {f arg head : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    {err : TcError .anon}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hhead : methods.whnfCoreFlags head flags s = .error err s₁) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .error err s₁ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]

/-- On an unchanged non-lambda head, an iota-helper error is propagated with
the helper's partial post-state. -/
theorem whnfCoreWithFlagsStep_appUnchangedIotaError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {f arg head : KExpr .anon} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    {err : TcError .anon}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda head)
    (hhead : methods.whnfCoreFlags head flags s = .ok head s₁)
    (hself : (head != head) = false)
    (hiota : (tryIotaWithFlags (.app f arg info) flags).run methods s₁ =
      .error err s₂) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .error err s₂ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hself]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags (.app f arg info) flags) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hiota]

/-- A changed non-lambda head is rebuilt with the complete original argument
spine before one successful iota reduction is attempted. -/
theorem whnfCoreWithFlagsStep_appChangedIota
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt result : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinish : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ =
      .ok (some result) s₃) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .ok (.next result) s₃ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hchanged]
    change EStateM.bind
      (ReaderT.run (finishAppResult _ args 0) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hfinish]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags rebuilt flags) methods) _ s₂ = _
    unfold EStateM.bind
    rw [hiota]
    rfl

/-- If iota misses after changed-head rebuilding, the rebuilt application—not
the original source—is the exact `.done` result. -/
theorem whnfCoreWithFlagsStep_appChangedDone
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinish : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ =
      .ok none s₃) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .ok (.done rebuilt) s₃ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hchanged]
    change EStateM.bind
      (ReaderT.run (finishAppResult _ args 0) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hfinish]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags rebuilt flags) methods) _ s₂ = _
    unfold EStateM.bind
    rw [hiota]
    rfl

/-- Iota errors after changed-head rebuilding retain the helper's exact
partial post-state.  The preceding intern-only rebuild has already completed. -/
theorem whnfCoreWithFlagsStep_appChangedIotaError
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags} {err : TcError .anon}
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinish : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ =
      .error err s₃) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
      .error err s₃ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  cases hnonlam <;> simp only
  all_goals
    rw [hchanged]
    change EStateM.bind
      (ReaderT.run (finishAppResult _ args 0) methods) _ s₁ = _
    unfold EStateM.bind
    rw [hfinish]
    change EStateM.bind
      (ReaderT.run (tryIotaWithFlags rebuilt flags) methods) _ s₂ = _
    unfold EStateM.bind
    rw [hiota]

/-- Every structural leaf terminates one named production loop iteration. -/
theorem whnfCoreWithFlagsStep_leaf {methods : Methods .anon}
    {s : TcState .anon} {e : KExpr .anon} (hleaf : WhnfCoreLeaf e)
    (flags : WhnfFlags) :
    (whnfCoreWithFlagsStep e flags).run methods s = .ok (.done e) s := by
  cases hleaf <;> rfl

/-- Structural-leaf base branch: every immediately WHNF form satisfies the
repaired one-step contract.  The proof consumes both finite-support membership
and an actual source translation; neither follows from the state invariant. -/
theorem whnfCoreWithFlagsStep_leaf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {e : KExpr .anon}
    {flags : WhnfFlags} {stepError : TcError .anon -> TcState .anon -> Prop}
    (theory : WhnfTheory trProj world uvars) (hleaf : WhnfCoreLeaf e) :
    forall s,
      WhnfStep.Source trProj world support uvars Delta id e ->
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep e flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          e action) stepError := by
  intro s hsource methods hmethods
  intro hI
  rw [whnfCoreWithFlagsStep_leaf hleaf]
  obtain ⟨hsupport, sourceV, htr⟩ := hsource
  exact ⟨hI, hsupport,
    WhnfMeaning.refl htr (theory.exprWF hI.2.1 htr)⟩

/-- A non-let legacy variable supplies a complete `.done` payload.  The
    lookup equation cannot hide an intern-table mutation: an `.ok none`
    outcome is proved to return the original state. -/
theorem whnfCoreWithFlagsStep_varDone_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s' : TcState .anon} {idx : UInt64}
    {name : Mode.anon.F Name} {md : ExprInfo .anon} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hsource : WhnfStep.Source trProj world support uvars Delta id
      (.var idx name md))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hlookup : TcM.lookupLetVal idx s = .ok none s') :
    (whnfCoreWithFlagsStep (.var idx name md) flags).run methods s =
        .ok (.done (.var idx name md)) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
      WhnfStep.Meaning trProj world support uvars Delta id
        (.var idx name md) (.done (.var idx name md)) := by
  have hsame := TcM.lookupLetVal_none_state hlookup
  subst s'
  obtain ⟨hsupport, sourceV, htr⟩ := hsource
  exact ⟨whnfCoreWithFlagsStep_varDone hlookup, hI, hsupport,
    WhnfMeaning.refl htr (theory.exprWF hI.2.1 htr)⟩

/-- An absent or regular-binder fvar supplies the analogous state-pure
    `.done` payload.  Excluding only `.ldecl` is deliberate: `.cdecl` is the
    ordinary open-binder case and must remain stuck. -/
theorem whnfCoreWithFlagsStep_fvarDone_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {fv : FVarId}
    {name : Mode.anon.F Name} {md : ExprInfo .anon} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hsource : WhnfStep.Source trProj world support uvars Delta id
      (.fvar fv name md))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnot : ∀ declName ty val,
      s.lctx.find? fv ≠ some (.ldecl declName ty val)) :
    (whnfCoreWithFlagsStep (.fvar fv name md) flags).run methods s =
        .ok (.done (.fvar fv name md)) s ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s ∧
      WhnfStep.Meaning trProj world support uvars Delta id
        (.fvar fv name md) (.done (.fvar fv name md)) := by
  obtain ⟨hsupport, sourceV, htr⟩ := hsource
  exact ⟨whnfCoreWithFlagsStep_fvarDone hnot, hI, hsupport,
    WhnfMeaning.refl htr (theory.exprWF hI.2.1 htr)⟩

/-- Successful explicit-let substitution supplies the complete local payload
consumed by `WhnfStep.WF`.  Exact execution, post-state invariant, and finite
result support come from one indexed substitution request; source
translatability plus that request's constructedness and exact UInt64 bounds
construct the Theory meaning through `WhnfMeaning.letE`. -/
theorem whnfCoreWithFlagsStep_letE_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {name : Mode.anon.F Name} {ty val body : KExpr .anon}
    {nondep : Bool} {info : ExprInfo .anon} {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hmem : WalkerRequest.subst body val 0 ∈ requests)
    (hsource : WhnfStep.Source trProj world support uvars Δ id
      (.letE name ty val body nondep info))
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s) :
    ∃ s',
      (whnfCoreWithFlagsStep (.letE name ty val body nondep info) flags).run
          methods s = .ok (.next (KExpr.substSpec body val 0)) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      WhnfStep.Meaning trProj world support uvars Δ id
        (.letE name ty val body nondep info)
        (.next (KExpr.substSpec body val 0)) := by
  obtain ⟨s', hwalk, hI', _⟩ := hrun.subst_whnf_eval hmem hI
  obtain ⟨_, hvalCon, _, _, hbound⟩ := hrun.requestBounds hmem
  obtain ⟨_, bodyV, htr⟩ := hsource
  have hsupport : support (KExpr.substSpec body val 0) :=
    hrun.coverage.subst hmem _ (KExpr.SubstReach.spec val body 0)
  have hmeaning := WhnfMeaning.letE theory hI.2.1 htr hvalCon (by
    simpa using hbound)
  exact ⟨s', whnfCoreWithFlagsStep_letE hwalk, hI', hsupport, hmeaning⟩

/-- Successful direct beta supplies the exact one-step payload consumed by
`WhnfStep.WF`: production execution and invariant preservation come from the
verified simultaneous-substitution walker, while Theory beta meaning remains
an explicit semantic premise.  The result-support fact is recovered from the
same finite request that justifies the walker. -/
theorem whnfCoreWithFlagsStep_betaOne_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {lamMd appMd : ExprInfo .anon}
    {flags : WhnfFlags}
    (hmem : WalkerRequest.simulSubst body #[arg] 0 ∈ requests)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hhead : methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags s =
      .ok (.lam nm bi ty body lamMd) s)
    (hmeaning : WhnfMeaning trProj world uvars Delta
      (.app (.lam nm bi ty body lamMd) arg appMd)
      (KExpr.simulSubstSpec body #[arg] 0)) :
    ∃ s',
      (whnfCoreWithFlagsStep
          (.app (.lam nm bi ty body lamMd) arg appMd) flags).run methods s =
        .ok (.next (KExpr.simulSubstSpec body #[arg] 0)) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s' ∧
      WhnfStep.Meaning trProj world support uvars Delta id
        (.app (.lam nm bi ty body lamMd) arg appMd)
        (.next (KExpr.simulSubstSpec body #[arg] 0)) := by
  obtain ⟨s', hwalk, hI', _⟩ :=
    hrun.simulSubst_whnf_eval hmem hI
  have hsupport : support (KExpr.simulSubstSpec body #[arg] 0) :=
    hrun.coverage.simulSubst hmem _
      (KExpr.SimulSubstReach.spec #[arg] body 0)
  exact ⟨s', whnfCoreWithFlagsStep_betaOne hhead hwalk, hI',
    hsupport, hmeaning⟩

/-- General multi-beta acceptance.  The recursive head callback's exact
syntax and post-invariant remain visible, while the substitution request and
application certificate discharge all subsequent execution, support,
collision-freedom, argument-order, and intern-frame obligations.  Semantic
meaning is explicit until the Theory-side multi-beta congruence lemma is
connected to `consumeBetaLams`. -/
theorem whnfCoreWithFlagsStep_betaMany_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s s₁ : TcState .anon}
    {f arg head : KExpr .anon} {appInfo : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body body₀ : KExpr .anon} {lamInfo : ExprInfo .anon}
    {consumed : Array (KExpr .anon)} {result : KExpr .anon}
    {flags : WhnfFlags}
    (hmem : WalkerRequest.simulSubst body₀ consumed.reverse 0 ∈ requests)
    (hfinish : FinishAppRequests requests
      (args.extract consumed.size args.size).toList
      (KExpr.simulSubstSpec body₀ consumed.reverse 0) result)
    (hI₁ : WhnfStateInv layer semantics trProj world support uvars Δ s₁)
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine = (head, args))
    (hhead : methods.whnfCoreFlags head flags s =
      .ok (.lam nm bi ty body lamInfo) s₁)
    (hconsume : consumeBetaLams (.lam nm bi ty body lamInfo) args =
      (body₀, consumed))
    (hnonempty : (!consumed.isEmpty) = true)
    (hmeaning : WhnfMeaning trProj world uvars Δ (.app f arg appInfo) result) :
    ∃ s₃,
      (whnfCoreWithFlagsStep (.app f arg appInfo) flags).run methods s =
          .ok (.next result) s₃ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₃ ∧
      WhnfStep.Meaning trProj world support uvars Δ id
        (.app f arg appInfo) (.next result) := by
  obtain ⟨s₂, hsubst, hI₂, _⟩ :=
    hrun.simulSubst_whnf_eval hmem hI₁
  obtain ⟨s₃, hfinishRun, hI₃, _⟩ := hfinish.eval hrun hI₂
  have hsubSupport :
      support (KExpr.simulSubstSpec body₀ consumed.reverse 0) :=
    hrun.coverage.simulSubst hmem _
      (KExpr.SimulSubstReach.spec consumed.reverse body₀ 0)
  have hresultSupport : support result :=
    hfinish.support hrun hsubSupport
  exact ⟨s₃,
    whnfCoreWithFlagsStep_betaMany hspine hhead hconsume hnonempty
      hsubst hfinishRun,
    hI₃, hresultSupport, hmeaning⟩

/-- Successful projection supplies one complete local step payload.  Source
translation is taken from `WhnfStep.Source`; the inductive-reduction oracle
justifies the syntax-directed helper result, and finite result support stays
an explicit construction obligation. -/
theorem whnfCoreWithFlagsStep_projection_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (oracle : InductiveReductionOracle layer semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s1 s2 : TcState .anon} {id : KId .anon} {field : UInt64}
    {value wvalue result : KExpr .anon} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hsource : WhnfStep.Source trProj world support uvars Delta (fun e => e)
      (.prj id field value info))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s1)
    (hreduce : (tryProjReduce id field wvalue).run methods s1 =
      .ok (some result) s2)
    (hresult : support result) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
        .ok (.next result) s2 ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s2 ∧
      WhnfStep.Meaning trProj world support uvars Delta (fun e => e)
        (.prj id field value info) (.next result) := by
  obtain ⟨_, sourceV, htr⟩ := hsource
  have hsemantic := oracle.projection hmethods htr hI hwhnf hreduce
  exact ⟨whnfCoreWithFlagsStep_projection hwhnf hreduce,
    hsemantic.1, hresult, hsemantic.2⟩

/-- Successful ordinary iota supplies the analogous local step payload.  As
with projection, helper success alone is insufficient: the translated source
and registered-rule oracle remain load-bearing premises. -/
theorem whnfCoreWithFlagsStep_iota_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (oracle : InductiveReductionOracle layer semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s1 s2 : TcState .anon} {recId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo appInfo : ExprInfo .anon}
    {f arg result : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hsource : WhnfStep.Source trProj world support uvars Delta id
      (.app f arg appInfo))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine =
      (.const recId us headInfo, args))
    (hhead : methods.whnfCoreFlags (.const recId us headInfo) flags s =
      .ok (.const recId us headInfo) s1)
    (hself : ((.const recId us headInfo : KExpr .anon) !=
      .const recId us headInfo) = false)
    (hiota : (tryIotaWithFlags (.app f arg appInfo) flags).run methods s1 =
      .ok (some result) s2)
    (hresult : support result) :
    (whnfCoreWithFlagsStep (.app f arg appInfo) flags).run methods s =
        .ok (.next result) s2 ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s2 ∧
      WhnfStep.Meaning trProj world support uvars Delta id
        (.app f arg appInfo) (.next result) := by
  obtain ⟨_, sourceV, htr⟩ := hsource
  have hsemantic :=
    oracle.iota hmethods htr hI hspine hhead hself hiota
  exact ⟨whnfCoreWithFlagsStep_iota hspine hhead hself hiota,
    hsemantic.1, hresult, hsemantic.2⟩

/-- A projection miss returns the original source.  The explicit post-state
invariant is the still-open helper-frame obligation; semantic meaning itself
is reflexive and needs no inductive reduction oracle. -/
theorem whnfCoreWithFlagsStep_projectionDone_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {id : KId .anon} {field : UInt64}
    {value wvalue : KExpr .anon} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hsource : WhnfStep.Source trProj world support uvars Delta (fun e => e)
      (.prj id field value info))
    (hpost : WhnfStateInv layer semantics trProj world support uvars Delta s₂)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok none s₂) :
    (whnfCoreWithFlagsStep (.prj id field value info) flags).run methods s =
        .ok (.done (.prj id field value info)) s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s₂ ∧
      WhnfStep.Meaning trProj world support uvars Delta (fun e => e)
        (.prj id field value info) (.done (.prj id field value info)) := by
  obtain ⟨hsupport, sourceV, htr⟩ := hsource
  exact ⟨whnfCoreWithFlagsStep_projectionDone hwhnf hreduce, hpost,
    hsupport, WhnfMeaning.refl htr (theory.exprWF hpost.2.1 htr)⟩

/-- The unchanged-head/iota-miss branch has the same reflexive semantic
shape.  Its post-state invariant remains explicit until the iota helper frame
is proved for every success and error path. -/
theorem whnfCoreWithFlagsStep_appUnchangedDone_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {f arg head : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (theory : WhnfTheory trProj world uvars)
    (hsource : WhnfStep.Source trProj world support uvars Delta id
      (.app f arg info))
    (hpost : WhnfStateInv layer semantics trProj world support uvars Delta s₂)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda head)
    (hhead : methods.whnfCoreFlags head flags s = .ok head s₁)
    (hself : (head != head) = false)
    (hiota : (tryIotaWithFlags (.app f arg info) flags).run methods s₁ =
      .ok none s₂) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
        .ok (.done (.app f arg info)) s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Delta s₂ ∧
      WhnfStep.Meaning trProj world support uvars Delta id
        (.app f arg info) (.done (.app f arg info)) := by
  obtain ⟨hsupport, sourceV, htr⟩ := hsource
  exact ⟨whnfCoreWithFlagsStep_appUnchangedDone hspine hnonlam hhead hself hiota,
    hpost, hsupport, WhnfMeaning.refl htr (theory.exprWF hpost.2.1 htr)⟩

/-- Changed-head/iota-miss acceptance.  The finite rebuild certificate is
checked against the exact helper state, proving its intern-only execution and
result support.  Head-reduction meaning and the iota helper's final frame are
still explicit semantic/post-state premises at this local boundary. -/
theorem whnfCoreWithFlagsStep_appChangedDone_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hfinish : FinishAppRequests requests
      (args.extract 0 args.size).toList changed rebuilt)
    (hchangedSupport : support changed)
    (hI₁ : WhnfStateInv layer semantics trProj world support uvars Δ s₁)
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s₃)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinishRun : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ = .ok none s₃)
    (hmeaning : WhnfMeaning trProj world uvars Δ
      (.app f arg info) rebuilt) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
        .ok (.done rebuilt) s₃ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₃ ∧
      WhnfStep.Meaning trProj world support uvars Δ id
        (.app f arg info) (.done rebuilt) := by
  obtain ⟨s₂', hfinishRun', _, _⟩ := hfinish.eval hrun hI₁
  rw [hfinishRun] at hfinishRun'
  cases hfinishRun'
  have hrebuiltSupport : support rebuilt :=
    hfinish.support hrun hchangedSupport
  exact ⟨whnfCoreWithFlagsStep_appChangedDone hspine hnonlam hhead hchanged
      hfinishRun hiota,
    hpost, hrebuiltSupport, hmeaning⟩

/-- Changed-head/iota-hit acceptance.  Rebuilding is fully certified; support
and semantic meaning of the syntax-directed iota result stay explicit until
the inductive-reduction oracle is generalized from unchanged to rebuilt
sources. -/
theorem whnfCoreWithFlagsStep_appChangedIota_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt result : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hfinish : FinishAppRequests requests
      (args.extract 0 args.size).toList changed rebuilt)
    (hI₁ : WhnfStateInv layer semantics trProj world support uvars Δ s₁)
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s₃)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinishRun : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ =
      .ok (some result) s₃)
    (hresultSupport : support result)
    (hmeaning : WhnfMeaning trProj world uvars Δ
      (.app f arg info) result) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
        .ok (.next result) s₃ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₃ ∧
      WhnfStep.Meaning trProj world support uvars Δ id
        (.app f arg info) (.next result) := by
  obtain ⟨s₂', hfinishRun', _, _⟩ := hfinish.eval hrun hI₁
  rw [hfinishRun] at hfinishRun'
  cases hfinishRun'
  exact ⟨whnfCoreWithFlagsStep_appChangedIota hspine hnonlam hhead hchanged
      hfinishRun hiota,
    hpost, hresultSupport, hmeaning⟩

/-- The changed-head error path retains the exact iota partial state and its
invariant; certified rebuilding has completed successfully beforehand. -/
theorem whnfCoreWithFlagsStep_appChangedIotaError_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ s₃ : TcState .anon}
    {f arg head changed rebuilt : KExpr .anon}
    {info : ExprInfo .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags} {err : TcError .anon}
    (hfinish : FinishAppRequests requests
      (args.extract 0 args.size).toList changed rebuilt)
    (hI₁ : WhnfStateInv layer semantics trProj world support uvars Δ s₁)
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s₃)
    (hspine : (.app f arg info : KExpr .anon).collectSpine = (head, args))
    (hnonlam : WhnfCoreNonLambda changed)
    (hhead : methods.whnfCoreFlags head flags s = .ok changed s₁)
    (hchanged : (changed != head) = true)
    (hfinishRun : (finishAppResult changed args 0).run methods s₁ =
      .ok rebuilt s₂)
    (hiota : (tryIotaWithFlags rebuilt flags).run methods s₂ =
      .error err s₃) :
    (whnfCoreWithFlagsStep (.app f arg info) flags).run methods s =
        .error err s₃ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₃ := by
  obtain ⟨s₂', hfinishRun', _, _⟩ := hfinish.eval hrun hI₁
  rw [hfinishRun] at hfinishRun'
  cases hfinishRun'
  exact ⟨whnfCoreWithFlagsStep_appChangedIotaError hspine hnonlam hhead
    hchanged hfinishRun hiota, hpost⟩

/-- Generic two-iteration equation for the production bounded driver: one
successful `.next` step followed by a structural leaf.  Keeping this seam
branch-agnostic lets beta, both zeta paths, and later projection/iota proofs
share the exact 10,000-fuel argument. -/
theorem whnfCoreWithFlagsUncached_nextLeaf
    {methods : Methods .anon} {s s' : TcState .anon}
    {source result : KExpr .anon} {flags : WhnfFlags}
    (hstep : (whnfCoreWithFlagsStep source flags).run methods s =
      .ok (.next result) s')
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached source flags).run methods s =
      .ok result s' := by
  unfold whnfCoreWithFlagsUncached
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  rw [RecM.runBounded]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlagsStep source flags) methods) _ s = _
  unfold EStateM.bind
  rw [hstep]
  simp only
  rw [RecM.runBounded.eq_def]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlagsStep result flags) methods) _ s' = _
  unfold EStateM.bind
  rw [whnfCoreWithFlagsStep_leaf hleaf]
  rfl

/-- The actual bounded structural-WHNF driver performs one successful
projection step and terminates on the resulting structural leaf. -/
theorem whnfCoreWithFlagsUncached_projection
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {id : KId .anon} {field : UInt64} {value wvalue result : KExpr .anon}
    {info : ExprInfo .anon} {flags : WhnfFlags}
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok (some result) s₂)
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached (.prj id field value info) flags).run
      methods s = .ok result s₂ :=
  whnfCoreWithFlagsUncached_nextLeaf
    (whnfCoreWithFlagsStep_projection hwhnf hreduce) hleaf

/-- The actual bounded structural-WHNF driver performs one successful iota
step and terminates on the resulting structural leaf. -/
theorem whnfCoreWithFlagsUncached_iota
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {recId : KId .anon} {us : Array (KUniv .anon)}
    {headInfo appInfo : ExprInfo .anon} {f arg result : KExpr .anon}
    {args : Array (KExpr .anon)} {flags : WhnfFlags}
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine =
      (.const recId us headInfo, args))
    (hhead : methods.whnfCoreFlags (.const recId us headInfo) flags s =
      .ok (.const recId us headInfo) s₁)
    (hself : ((.const recId us headInfo : KExpr .anon) !=
      .const recId us headInfo) = false)
    (hiota :
      (tryIotaWithFlags (.app f arg appInfo) flags).run methods s₁ =
        .ok (some result) s₂)
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached (.app f arg appInfo) flags).run methods s =
      .ok result s₂ :=
  whnfCoreWithFlagsUncached_nextLeaf
    (whnfCoreWithFlagsStep_iota hspine hhead hself hiota) hleaf

/-- Conditional projection package.  The production execution is proved
definitionally above; semantic validity and full invariant preservation are
obtained only through the explicit inductive-reduction boundary, which also
requires a translation of the original projection. -/
theorem whnfCoreWithFlagsUncached_projection_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (oracle : InductiveReductionOracle layer semantics trProj world support)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {id : KId .anon} {field : UInt64}
    {value wvalue result : KExpr .anon} {info : ExprInfo .anon}
    {flags : WhnfFlags} {sourceV : VExpr}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.prj id field value info) sourceV)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hwhnf :
      (if flags.cheapProj then
          (whnfCoreFlagsRec value flags).run methods s
        else (whnfRec value).run methods s) = .ok wvalue s₁)
    (hreduce : (tryProjReduce id field wvalue).run methods s₁ =
      .ok (some result) s₂)
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached (.prj id field value info) flags).run
        methods s = .ok result s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfMeaning trProj world uvars Δ
        (.prj id field value info) result := by
  have hsemantic :=
    oracle.projection hmethods hsource hI hwhnf hreduce
  exact ⟨whnfCoreWithFlagsUncached_projection hwhnf hreduce hleaf,
    hsemantic.1, hsemantic.2⟩

/-- Conditional iota package.  The source translation premise is
load-bearing: an untrusted catalog recursor can drive the production helper
without denoting a Theory term, as the adversarial fixture demonstrates. -/
theorem whnfCoreWithFlagsUncached_iota_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (oracle : InductiveReductionOracle layer semantics trProj world support)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {recId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo appInfo : ExprInfo .anon}
    {f arg result : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags} {sourceV : VExpr}
    (hmethods : Methods.WFAt layer semantics trProj world support uvars methods)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app f arg appInfo) sourceV)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine =
      (.const recId us headInfo, args))
    (hhead : methods.whnfCoreFlags (.const recId us headInfo) flags s =
      .ok (.const recId us headInfo) s₁)
    (hself : ((.const recId us headInfo : KExpr .anon) !=
      .const recId us headInfo) = false)
    (hiota :
      (tryIotaWithFlags (.app f arg appInfo) flags).run methods s₁ =
        .ok (some result) s₂)
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached (.app f arg appInfo) flags).run methods s =
        .ok result s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfMeaning trProj world uvars Δ (.app f arg appInfo) result := by
  have hsemantic :=
    oracle.iota hmethods hsource hI hspine hhead hself hiota
  exact ⟨whnfCoreWithFlagsUncached_iota hspine hhead hself hiota hleaf,
    hsemantic.1, hsemantic.2⟩

/-- The actual bounded structural-WHNF driver performs successful legacy
zeta and terminates when the lifted value is a structural leaf. -/
theorem whnfCoreWithFlagsUncached_varZeta
    {methods : Methods .anon} {s s' : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {flags : WhnfFlags} {val : KExpr .anon}
    (hlookup : TcM.lookupLetVal idx s = .ok (some val) s')
    (hleaf : WhnfCoreLeaf val) :
    (whnfCoreWithFlagsUncached (.var idx name md) flags).run methods s =
      .ok val s' :=
  whnfCoreWithFlagsUncached_nextLeaf
    (whnfCoreWithFlagsStep_varZeta hlookup) hleaf

/-- The actual bounded structural-WHNF driver performs let-bound fvar zeta
and terminates when the stored value is a structural leaf. -/
theorem whnfCoreWithFlagsUncached_fvarZeta
    {methods : Methods .anon} {s : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {declName : Mode.anon.F Name} {ty val : KExpr .anon}
    {flags : WhnfFlags}
    (hfind : s.lctx.find? id = some (.ldecl declName ty val))
    (hleaf : WhnfCoreLeaf val) :
    (whnfCoreWithFlagsUncached (.fvar id name md) flags).run methods s =
      .ok val s :=
  whnfCoreWithFlagsUncached_nextLeaf
    (whnfCoreWithFlagsStep_fvarZeta hfind) hleaf

/-- Legacy-zeta package.  The execution-indexed lift walker supplies the
exact production result and intern-only frame; the reconciled context
supplies the same inlined Theory value, so operational execution, invariant
preservation, and semantic meaning are established together. -/
theorem whnfCoreWithFlagsUncached_varZeta_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {idx : UInt64} {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {ty val : KExpr .anon} {flags : WhnfFlags}
    (htp : TrProjOK world.venv uvars trProj)
    (hmem : WalkerRequest.lift val (idx + 1) 0 ∈ requests)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hidx : idx.toNat < s.ctx.size)
    (hty : s.ctx[s.ctx.size - 1 - idx.toNat]? = some ty)
    (hov : s.letVals[s.ctx.size - 1 - idx.toNat]? = some (some val))
    (hbig : Δ.bvars + val.size < UInt64.size)
    (hleaf : WhnfCoreLeaf (KExpr.liftSpec val (idx + 1) 0)) :
    ∃ s',
      (whnfCoreWithFlagsUncached (.var idx name md) flags).run methods s =
          .ok (KExpr.liftSpec val (idx + 1) 0) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' ∧
      WhnfMeaning trProj world uvars Δ (.var idx name md)
        (KExpr.liftSpec val (idx + 1) 0) := by
  obtain ⟨s', hlift, hI', hframe⟩ := hrun.lift_whnf_eval hmem hI
  have hbang : s.letVals[s.ctx.size - 1 - idx.toNat]! = some val := by
    obtain ⟨hbound, hvalue⟩ := getElem?_eq_some_iff.mp hov
    rw [getElem!_pos s.letVals (s.ctx.size - 1 - idx.toNat) hbound,
      hvalue]
  have hlookup := TcM.lookupLetVal_eval hidx hbang hlift
  have hsz : s.ctx.size < UInt64.size := by
    rw [← hI.2.1.bvars_eq]
    omega
  exact ⟨s', whnfCoreWithFlagsUncached_varZeta hlookup hleaf,
    hI', hframe,
    WhnfMeaning.zetaVar hI.2.1 htp hidx hsz hty hov hbig⟩

/-- Free-variable zeta package.  Unlike the legacy branch this execution is
state-pure.  `hclosed` is intentionally visible: without it, a mixed context
may have newer de Bruijn frames and production's unchanged stored value is
not justified by `CtxRecon`. -/
theorem whnfCoreWithFlagsUncached_fvarZeta_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {fv : FVarId}
    {name : Mode.anon.F Name} {md : ExprInfo .anon}
    {declName : Mode.anon.F Name} {ty val : KExpr .anon}
    {flags : WhnfFlags}
    (htp : TrProjOK world.venv uvars trProj)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hfind : s.lctx.find? fv = some (.ldecl declName ty val))
    (hcon : KExpr.Constructed val) (hclosed : val.lbr = 0)
    (hbig : Δ.bvars + val.size < UInt64.size)
    (hleaf : WhnfCoreLeaf val) :
    (whnfCoreWithFlagsUncached (.fvar fv name md) flags).run methods s =
        .ok val s ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s ∧
      WhnfMeaning trProj world uvars Δ (.fvar fv name md) val :=
  ⟨whnfCoreWithFlagsUncached_fvarZeta hfind hleaf, hI,
    WhnfMeaning.zetaFVar hI.2.1 htp hfind hcon hclosed hbig⟩

/-- The actual 10,000-iteration production driver performs the direct beta
step and then terminates when the walker result is a structural leaf. -/
theorem whnfCoreWithFlagsUncached_betaOne
    {methods : Methods .anon} {s s' : TcState .anon}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg result : KExpr .anon}
    {lamMd appMd : ExprInfo .anon} {flags : WhnfFlags}
    (hhead : methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags s =
      .ok (.lam nm bi ty body lamMd) s)
    (hwalk : TcM.runIntern (simulSubst body #[arg] 0) s = .ok result s')
    (hleaf : WhnfCoreLeaf result) :
    (whnfCoreWithFlagsUncached
      (.app (.lam nm bi ty body lamMd) arg appMd) flags).run methods s =
      .ok result s' := by
  unfold whnfCoreWithFlagsUncached
  rw [show maxWhnfFuel.toNat = 10000 by rfl]
  rw [RecM.runBounded]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlagsStep
      (.app (.lam nm bi ty body lamMd) arg appMd) flags) methods) _ s = _
  unfold EStateM.bind
  rw [whnfCoreWithFlagsStep_betaOne hhead hwalk]
  simp only
  rw [RecM.runBounded.eq_def]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlagsStep result flags) methods) _ s' = _
  unfold EStateM.bind
  rw [whnfCoreWithFlagsStep_leaf hleaf]
  rfl

/-- Compose the production beta branch with the execution-indexed verified
walker.  This proves both the concrete result and full post-state invariant;
the only algorithm-specific premise left is the exact recursive-head callback
equation described above. -/
theorem whnfCoreWithFlagsUncached_betaOne_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Δ : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {lamMd appMd : ExprInfo .anon}
    {flags : WhnfFlags}
    (hmem : WalkerRequest.simulSubst body #[arg] 0 ∈ requests)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hhead : methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags s =
      .ok (.lam nm bi ty body lamMd) s)
    (hleaf : WhnfCoreLeaf (KExpr.simulSubstSpec body #[arg] 0)) :
    ∃ s',
      (whnfCoreWithFlagsUncached
        (.app (.lam nm bi ty body lamMd) arg appMd) flags).run methods s =
          .ok (KExpr.simulSubstSpec body #[arg] 0) s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' ∧
      InternUpdateFrame s s' := by
  obtain ⟨s', hwalk, hI', hframe⟩ :=
    hrun.simulSubst_whnf_eval hmem hI
  exact ⟨s', whnfCoreWithFlagsUncached_betaOne hhead hwalk hleaf,
    hI', hframe⟩

/-- First algorithmic K1 slice: all immediate-return WHNF forms preserve the
complete fixed-world/context/cache invariant and their exact Theory meaning.
The theorem is layer-polymorphic because these branches never inspect
`noAccel` and never consume a `NativeOracle`. -/
theorem whnf_leaf_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {e : KExpr .anon} {sourceV : VExpr}
    (hleaf : WhnfLeaf e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV)
    (hwf : VExpr.WF world.venv uvars Δ.toCtx sourceV) :
    RecM.WF layer semantics trProj world support uvars Δ s (RecM.whnf e)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result) := by
  intro methods hmethods
  rw [hleaf.eval]
  exact TcM.WF.pure fun hI => WhnfPost.refl htr hwf

/-- Convenient derived leaf theorem when the caller carries the uniform
literal/projection Theory bundle instead of an expression-specific WF fact. -/
theorem whnf_leaf_wf_of_theory {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {s : TcState .anon} {e : KExpr .anon}
    {sourceV : VExpr} (theory : WhnfTheory trProj world uvars)
    (hleaf : WhnfLeaf e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV) :
    RecM.WF layer semantics trProj world support uvars Δ s (RecM.whnf e)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result) := by
  intro methods hmethods
  rw [hleaf.eval]
  exact TcM.WF.pure fun hI =>
    WhnfPost.refl htr (theory.exprWF hI.2.1 htr)

/-- Immediate structural-WHNF forms preserve the complete K1 invariant and
have reflexive Theory meaning.  This covers the actual flag-parametric core
entry point, including constants and the cheap projection policy. -/
theorem whnfCoreWithFlags_leaf_wf {layer : WhnfLayer}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Δ : KVLCtx} {s : TcState .anon} {e : KExpr .anon}
    {sourceV : VExpr} {flags : WhnfFlags}
    (hleaf : WhnfCoreLeaf e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV)
    (hwf : VExpr.WF world.venv uvars Δ.toCtx sourceV) :
    RecM.WF layer semantics trProj world support uvars Δ s
      (RecM.whnfCoreWithFlags e flags)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result) := by
  intro methods hmethods
  rw [hleaf.eval]
  exact TcM.WF.pure fun _ => WhnfPost.refl htr hwf

end RecM

/-! ## Acceleration boundary -/

/-- Named semantic boundary for the four production acceleration gates.
Each field is indexed by the actual helper execution, the concrete state,
and a semantically closed recursive method table.  It asserts only the
successful accelerated step; state preservation remains part of the WHNF
Hoare proof.  Primitive-specific refinements can split these fields without
changing `WhnfMeaning` or the no-acceleration theorem layer. -/
structure NativeOracle (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  native : ∀ {uvars Δ methods s e result s'},
    methods.WF .accelerated semantics trProj world support →
    WhnfStateInv .accelerated semantics trProj world support uvars Δ s →
    (RecM.tryReduceNative e).run methods s = .ok (some result) s' →
    WhnfMeaning trProj world uvars Δ e result
  bitvec : ∀ {uvars Δ methods s e result s'},
    methods.WF .accelerated semantics trProj world support →
    WhnfStateInv .accelerated semantics trProj world support uvars Δ s →
    (RecM.tryReduceBitvec e).run methods s = .ok (some result) s' →
    WhnfMeaning trProj world uvars Δ e result
  decidable : ∀ {uvars Δ methods s e result s'},
    methods.WF .accelerated semantics trProj world support →
    WhnfStateInv .accelerated semantics trProj world support uvars Δ s →
    (RecM.tryReduceDecidable e).run methods s = .ok (some result) s' →
    WhnfMeaning trProj world uvars Δ e result
  finVal : ∀ {uvars Δ methods s id field value head args info result s'},
    methods.WF .accelerated semantics trProj world support →
    WhnfStateInv .accelerated semantics trProj world support uvars Δ s →
    value.collectSpine = (head, args) →
    (RecM.tryReduceFinValDecidableRec id field head args).run methods s =
      .ok (some result) s' →
    WhnfMeaning trProj world uvars Δ (.prj id field value info) result

/-! ## No-delta optional-reducer contract -/

namespace OptionalReduction

/-- Fixed-universe Hoare boundary for one optional reducer.  This is the
honest contract for reducers whose cache semantics is indexed by the active
run's universe count, notably delta unfolding. -/
def WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat)
    (reduce : KExpr .anon → RecM .anon (Option (KExpr .anon))) : Prop :=
  ∀ {Δ source sourceV s},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV →
    RecM.WF layer semantics trProj world support uvars Δ s (reduce source)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Δ source reduced)

/-- Uniform Hoare boundary for one optional no-delta reducer.  A miss carries
no semantic claim but still preserves the complete state invariant; a hit
must additionally preserve finite support and justify the concrete reduction
in the fixed Theory context.  Errors preserve the invariant through
`RecM.WF`'s ordinary error arm. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (reduce : KExpr .anon → RecM .anon (Option (KExpr .anon))) : Prop :=
  ∀ {uvars Δ source sourceV s},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV →
    RecM.WF layer semantics trProj world support uvars Δ s (reduce source)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Δ source reduced)

/-- Specialize a universe-uniform optional-reducer proof to one active
universe count. -/
theorem WF.atUvars
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {reduce : KExpr .anon → RecM .anon (Option (KExpr .anon))}
    (h : WF layer semantics trProj world support reduce) (uvars : Nat) :
    WFAt layer semantics trProj world support uvars reduce := by
  intro Δ source sourceV s hsource htr
  exact h hsource htr

end OptionalReduction

/-- The five reducers that remain active when acceleration is disabled.
Keeping this boundary separate is adversarially important: `.noAccel` proves
that native and BitVec helpers miss, but it says nothing about the trusted
primitive-address interpretation, finite support for generated terms, or the
semantic correctness of projection/Nat/String/quotient hits. -/
structure NoDeltaBaseOracle (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (flags : WhnfFlags) (natSuccMode : NatSuccMode) : Prop where
  projApp : OptionalReduction.WF .noAccel semantics trProj world support
    (fun source => RecM.tryProjAppReduceFinished source flags)
  nat : OptionalReduction.WF .noAccel semantics trProj world support
    (fun source => RecM.tryReduceNatWithSuccMode source natSuccMode)
  string : OptionalReduction.WF .noAccel semantics trProj world support
    RecM.tryReduceString
  projectionDef : OptionalReduction.WF .noAccel semantics trProj world support
    RecM.tryReduceProjectionDefinition
  quot : OptionalReduction.WF .noAccel semantics trProj world support
    RecM.tryQuotReduce

/-! ## Production primitive/world/support binding -/

/-- One primitive-table entry denotes an already trusted Theory constant at
the expected Lean name. The trusted bit is essential: a matching `nameOf`
entry by itself is representation data, not semantic authority. -/
def PrimitiveIdAgrees (world : VerifyWorld) (id : KId .anon)
    (name : Lean.Name) : Prop :=
  world.trusted id ∧ world.nameOf id.addr = some name

namespace PrimitiveIdAgrees

/-- A bound primitive id is present in the Theory environment once the
world's trusted-catalog log is available. -/
theorem contains {trProj : RawProjRel} {world : VerifyWorld}
    {id : KId .anon} {name : Lean.Name}
    (hcatalog : TrustedCatalogRel trProj world)
    (h : PrimitiveIdAgrees world id name) :
    world.venv.contains name := by
  obtain ⟨_, actualName, ci, _, hname, hlookup⟩ :=
    hcatalog.lookup h.1
  rw [h.2] at hname
  cases hname
  exact ⟨ci, hlookup⟩

/-- Two primitive identifiers assigned distinct trusted names cannot share an
address.  This uses only functionality of the fixed `nameOf` map; it does not
appeal to native evaluation of the concrete Blake3 hashes. -/
theorem addr_ne {world : VerifyWorld}
    {id₁ id₂ : KId .anon} {name₁ name₂ : Lean.Name}
    (h₁ : PrimitiveIdAgrees world id₁ name₁)
    (h₂ : PrimitiveIdAgrees world id₂ name₂)
    (hne : name₁ ≠ name₂) :
    id₁.addr ≠ id₂.addr := by
  intro haddr
  apply hne
  apply Option.some.inj
  calc
    some name₁ = world.nameOf id₁.addr := h₁.2.symm
    _ = world.nameOf id₂.addr := congrArg world.nameOf haddr
    _ = some name₂ := h₂.2

/-- Primitive-name agreement is stable under trusted-world extension because
`VerifyWorld.LE` fixes `nameOf` and only grows the trusted set. -/
theorem mono {before after : VerifyWorld} {id : KId .anon}
    {name : Lean.Name} (hle : before ≤ after)
    (h : PrimitiveIdAgrees before id name) :
    PrimitiveIdAgrees after id name := by
  exact ⟨hle.trusted h.1, by simpa only [← hle.nameOf] using h.2⟩

end PrimitiveIdAgrees

/-- Exact address-to-name agreement needed by the active no-delta primitive
reducers. Projection-app and projection-wrapper rewriting are absent here:
they obtain their authority from translated projection/declaration facts,
not from `Primitives`. The list mirrors every direct table read in the Nat,
String, and quotient helpers, including Nat's linear-recognizer read. -/
structure NoDeltaPrimitiveTableAgrees (world : VerifyWorld)
    (prims : Primitives .anon) : Prop where
  nat : PrimitiveIdAgrees world prims.nat ``Nat
  natZero : PrimitiveIdAgrees world prims.natZero ``Nat.zero
  natSucc : PrimitiveIdAgrees world prims.natSucc ``Nat.succ
  natAdd : PrimitiveIdAgrees world prims.natAdd ``Nat.add
  natSub : PrimitiveIdAgrees world prims.natSub ``Nat.sub
  natMul : PrimitiveIdAgrees world prims.natMul ``Nat.mul
  natPow : PrimitiveIdAgrees world prims.natPow ``Nat.pow
  natGcd : PrimitiveIdAgrees world prims.natGcd ``Nat.gcd
  natMod : PrimitiveIdAgrees world prims.natMod ``Nat.mod
  natDiv : PrimitiveIdAgrees world prims.natDiv ``Nat.div
  natBeq : PrimitiveIdAgrees world prims.natBeq ``Nat.beq
  natBle : PrimitiveIdAgrees world prims.natBle ``Nat.ble
  natLand : PrimitiveIdAgrees world prims.natLand ``Nat.land
  natLor : PrimitiveIdAgrees world prims.natLor ``Nat.lor
  natXor : PrimitiveIdAgrees world prims.natXor ``Nat.xor
  natShiftLeft :
    PrimitiveIdAgrees world prims.natShiftLeft ``Nat.shiftLeft
  natShiftRight :
    PrimitiveIdAgrees world prims.natShiftRight ``Nat.shiftRight
  natRec : PrimitiveIdAgrees world prims.natRec ``Nat.rec
  boolType : PrimitiveIdAgrees world prims.boolType ``Bool
  boolTrue : PrimitiveIdAgrees world prims.boolTrue ``Bool.true
  boolFalse : PrimitiveIdAgrees world prims.boolFalse ``Bool.false
  stringBack : PrimitiveIdAgrees world prims.stringBack ``String.back
  stringLegacyBack :
    PrimitiveIdAgrees world prims.stringLegacyBack ``String.Legacy.back
  stringUtf8ByteSize :
    PrimitiveIdAgrees world prims.stringUtf8ByteSize ``String.utf8ByteSize
  stringToByteArray :
    PrimitiveIdAgrees world prims.stringToByteArray ``String.toByteArray
  byteArrayEmpty :
    PrimitiveIdAgrees world prims.byteArrayEmpty ``ByteArray.empty
  charOfNat : PrimitiveIdAgrees world prims.charOfNat ``Char.ofNat
  quotCtor : PrimitiveIdAgrees world prims.quotCtor ``Quot.mk
  quotLift : PrimitiveIdAgrees world prims.quotLift ``Quot.lift
  quotInd : PrimitiveIdAgrees world prims.quotInd ``Quot.ind

namespace NoDeltaPrimitiveTableAgrees

theorem mono {before after : VerifyWorld} {prims : Primitives .anon}
    (hle : before ≤ after)
    (h : NoDeltaPrimitiveTableAgrees before prims) :
    NoDeltaPrimitiveTableAgrees after prims where
  nat := h.nat.mono hle
  natZero := h.natZero.mono hle
  natSucc := h.natSucc.mono hle
  natAdd := h.natAdd.mono hle
  natSub := h.natSub.mono hle
  natMul := h.natMul.mono hle
  natPow := h.natPow.mono hle
  natGcd := h.natGcd.mono hle
  natMod := h.natMod.mono hle
  natDiv := h.natDiv.mono hle
  natBeq := h.natBeq.mono hle
  natBle := h.natBle.mono hle
  natLand := h.natLand.mono hle
  natLor := h.natLor.mono hle
  natXor := h.natXor.mono hle
  natShiftLeft := h.natShiftLeft.mono hle
  natShiftRight := h.natShiftRight.mono hle
  natRec := h.natRec.mono hle
  boolType := h.boolType.mono hle
  boolTrue := h.boolTrue.mono hle
  boolFalse := h.boolFalse.mono hle
  stringBack := h.stringBack.mono hle
  stringLegacyBack := h.stringLegacyBack.mono hle
  stringUtf8ByteSize := h.stringUtf8ByteSize.mono hle
  stringToByteArray := h.stringToByteArray.mono hle
  byteArrayEmpty := h.byteArrayEmpty.mono hle
  charOfNat := h.charOfNat.mono hle
  quotCtor := h.quotCtor.mono hle
  quotLift := h.quotLift.mono hle
  quotInd := h.quotInd.mono hle

end NoDeltaPrimitiveTableAgrees

/-- Finite generated-term coverage stated against actual successful helper
executions. Requiring every numeral or application globally would make a
finite run support artificially infinite; these five fields cover exactly
the results reachable from supported inputs in this run. -/
structure NoDeltaGeneratedSupport (support : RunSupport)
    (flags : WhnfFlags) (natSuccMode : NatSuccMode) : Prop where
  boolConst : ∀ {prims : Primitives .anon}, prims.CanonicalAnon →
    ∀ decision : Bool,
      support (KExpr.mkConst
        (if decision then prims.boolTrue else prims.boolFalse) #[])
  projApp : ∀ {methods s source result s'},
    support source →
    (RecM.tryProjAppReduceFinished source flags).run methods s =
      .ok (some result) s' →
    support result
  nat : ∀ {methods s source result s'},
    support source →
    (RecM.tryReduceNatWithSuccMode source natSuccMode).run methods s =
      .ok (some result) s' →
    support result
  string : ∀ {methods s source result s'},
    support source →
    (RecM.tryReduceString source).run methods s = .ok (some result) s' →
    support result
  projectionDef : ∀ {methods s source result s'},
    support source →
    (RecM.tryReduceProjectionDefinition source).run methods s =
      .ok (some result) s' →
    support result
  quot : ∀ {methods s source result s'},
    support source →
    (RecM.tryQuotReduce source).run methods s = .ok (some result) s' →
    support result

/-- Finite input closure needed by reducers that recursively normalize an
application argument.  This is intentionally spine closure rather than
global constructor closure: the arguments of a supported expression form a
finite subdomain, and applying the field again to a supported callback result
reaches successor/recursor subspines without making the run support infinite. -/
structure NoDeltaInputSupport (support : RunSupport) : Prop where
  spine : ∀ {source head args},
    support source →
    source.collectSpine = (head, args) →
    support head ∧ ∀ (i : Nat) (hi : i < args.size), support args[i]

/-- The concrete K1 input for active no-delta primitive proofs. It binds the
canonical anon table to trusted Theory names, carries Lean4Lean's primitive
reflection laws, records the quotient lift equation, and scopes generated
syntax to actual supported executions. This is necessary but intentionally
not sufficient for `NoDeltaBaseOracle`: helper state frames and branch-level
`WhnfMeaning` proofs remain real proof obligations. -/
structure NoDeltaPrimitiveContext (world : VerifyWorld) (support : RunSupport)
    (flags : WhnfFlags) (natSuccMode : NatSuccMode) : Prop where
  table : ∀ prims, prims.CanonicalAnon →
    NoDeltaPrimitiveTableAgrees world prims
  theoryPrimitives : world.venv.HasPrimitives
  quotientDefEq : world.venv.defeqs Lean4Lean.quotDefEq
  collisionFree : support.CollisionFree
  inputs : NoDeltaInputSupport support
  generated : NoDeltaGeneratedSupport support flags natSuccMode

namespace NoDeltaPrimitiveContext

/-- Connect the fixed production state invariant to the trusted primitive
table relation consumed by an active reducer proof. -/
theorem stateTable
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s) :
    NoDeltaPrimitiveTableAgrees world s.prims := by
  exact context.table s.prims hI.noAccel_primitives

/-- `computeNatBin` uses the fixed canonical address table.  Under the
production table binding, every successful arithmetic result is therefore
one of Lean4Lean's reflected primitive equations, lifted from the empty
universe/local context to the current checker context. -/
theorem computeNatBin_defeq
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    {addr : Address} {a b result : Nat}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    (hcatalog : TrustedCatalogRel trProj world)
    (hcanonical : prims.CanonicalAnon)
    (hcompute : computeNatBin addr PrimAddrs.canonical a b = some result) :
    ∃ name,
      world.nameOf addr = some name ∧
      world.venv.IsDefEqU uvars Δ.toCtx
        (.app (.app (.const name []) (.natLit a)) (.natLit b))
        (.natLit result) := by
  have htable := context.table prims hcanonical
  have liftReflection {name : Lean.Name} {f : Nat → Nat → Nat}
      {primitiveId : KId .anon}
      (hid : PrimitiveIdAgrees world primitiveId name)
      (hreflect : world.venv.ReflectsNatNatNat name f) :
      world.venv.IsDefEqU uvars Δ.toCtx
        (.app (.app (.const name []) (.natLit a)) (.natLit b))
        (.natLit (f a b)) := by
    have h := hreflect (hid.contains hcatalog) a b
    have h := h.instL (U' := uvars) (ls := []) (by simp)
    simpa [VExpr.instL] using h.weak0 world.venvWF (Γ := Δ.toCtx)
  have hnatAdd : prims.natAdd.addr = PrimAddrs.canonical.natAdd := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natAdd hcanonical
  have hnatSub : prims.natSub.addr = PrimAddrs.canonical.natSub := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natSub hcanonical
  have hnatMul : prims.natMul.addr = PrimAddrs.canonical.natMul := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natMul hcanonical
  have hnatDiv : prims.natDiv.addr = PrimAddrs.canonical.natDiv := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natDiv hcanonical
  have hnatMod : prims.natMod.addr = PrimAddrs.canonical.natMod := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natMod hcanonical
  have hnatPow : prims.natPow.addr = PrimAddrs.canonical.natPow := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natPow hcanonical
  have hnatGcd : prims.natGcd.addr = PrimAddrs.canonical.natGcd := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natGcd hcanonical
  have hnatLand : prims.natLand.addr = PrimAddrs.canonical.natLand := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natLand hcanonical
  have hnatLor : prims.natLor.addr = PrimAddrs.canonical.natLor := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natLor hcanonical
  have hnatXor : prims.natXor.addr = PrimAddrs.canonical.natXor := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natXor hcanonical
  have hnatShiftLeft :
      prims.natShiftLeft.addr = PrimAddrs.canonical.natShiftLeft := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natShiftLeft hcanonical
  have hnatShiftRight :
      prims.natShiftRight.addr = PrimAddrs.canonical.natShiftRight := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natShiftRight hcanonical
  generalize hfixed : PrimAddrs.canonical = fixed at hcompute
  unfold computeNatBin at hcompute
  by_cases hopAdd : addr == fixed.natAdd
  · rw [if_pos hopAdd] at hcompute
    have haddr := beq_iff_eq.mp hopAdd
    simp only [Option.some.injEq] at hcompute
    subst result
    refine ⟨``Nat.add, ?_,
      liftReflection htable.natAdd context.theoryPrimitives.natAdd⟩
    simpa only [haddr, ← hfixed, ← hnatAdd] using htable.natAdd.2
  · rw [if_neg hopAdd] at hcompute
    by_cases hopSub : addr == fixed.natSub
    · rw [if_pos hopSub] at hcompute
      have haddr := beq_iff_eq.mp hopSub
      simp only [Option.some.injEq] at hcompute
      subst result
      refine ⟨``Nat.sub, ?_,
        liftReflection htable.natSub context.theoryPrimitives.natSub⟩
      simpa only [haddr, ← hfixed, ← hnatSub] using htable.natSub.2
    · rw [if_neg hopSub] at hcompute
      by_cases hopMul : addr == fixed.natMul
      · rw [if_pos hopMul] at hcompute
        have haddr := beq_iff_eq.mp hopMul
        simp only [Option.some.injEq] at hcompute
        subst result
        refine ⟨``Nat.mul, ?_,
          liftReflection htable.natMul context.theoryPrimitives.natMul⟩
        simpa only [haddr, ← hfixed, ← hnatMul] using htable.natMul.2
      · rw [if_neg hopMul] at hcompute
        by_cases hopDiv : addr == fixed.natDiv
        · rw [if_pos hopDiv] at hcompute
          have haddr := beq_iff_eq.mp hopDiv
          simp only [Option.some.injEq] at hcompute
          have hresult : result = a / b := by
            calc
              result = (if b == 0 then 0 else a / b) := hcompute.symm
              _ = a / b := by
                by_cases hb : b = 0 <;> simp [hb]
          rw [hresult]
          refine ⟨``Nat.div, ?_,
            liftReflection htable.natDiv context.theoryPrimitives.natDiv⟩
          simpa only [haddr, ← hfixed, ← hnatDiv] using htable.natDiv.2
        · rw [if_neg hopDiv] at hcompute
          by_cases hopMod : addr == fixed.natMod
          · rw [if_pos hopMod] at hcompute
            have haddr := beq_iff_eq.mp hopMod
            simp only [Option.some.injEq] at hcompute
            have hresult : result = a % b := by
              calc
                result = (if b == 0 then a else a % b) := hcompute.symm
                _ = a % b := by
                  by_cases hb : b = 0 <;> simp [hb]
            rw [hresult]
            refine ⟨``Nat.mod, ?_,
              liftReflection htable.natMod context.theoryPrimitives.natMod⟩
            simpa only [haddr, ← hfixed, ← hnatMod] using htable.natMod.2
          · rw [if_neg hopMod] at hcompute
            by_cases hopPow : addr == fixed.natPow
            · rw [if_pos hopPow] at hcompute
              have haddr := beq_iff_eq.mp hopPow
              by_cases hbound : b ≤ 16777216
              · rw [if_pos hbound] at hcompute
                simp only [Option.some.injEq] at hcompute
                subst result
                refine ⟨``Nat.pow, ?_,
                  liftReflection htable.natPow
                    context.theoryPrimitives.natPow⟩
                simpa only [haddr, ← hfixed, ← hnatPow] using
                  htable.natPow.2
              · rw [if_neg hbound] at hcompute
                contradiction
            · rw [if_neg hopPow] at hcompute
              by_cases hopGcd : addr == fixed.natGcd
              · rw [if_pos hopGcd] at hcompute
                have haddr := beq_iff_eq.mp hopGcd
                simp only [Option.some.injEq] at hcompute
                subst result
                refine ⟨``Nat.gcd, ?_,
                  liftReflection htable.natGcd
                    context.theoryPrimitives.natGcd⟩
                simpa only [haddr, ← hfixed, ← hnatGcd] using
                  htable.natGcd.2
              · rw [if_neg hopGcd] at hcompute
                by_cases hopLand : addr == fixed.natLand
                · rw [if_pos hopLand] at hcompute
                  have haddr := beq_iff_eq.mp hopLand
                  simp only [Option.some.injEq] at hcompute
                  subst result
                  refine ⟨``Nat.land, ?_,
                    liftReflection htable.natLand
                      context.theoryPrimitives.natLAnd⟩
                  simpa only [haddr, ← hfixed, ← hnatLand] using
                    htable.natLand.2
                · rw [if_neg hopLand] at hcompute
                  by_cases hopLor : addr == fixed.natLor
                  · rw [if_pos hopLor] at hcompute
                    have haddr := beq_iff_eq.mp hopLor
                    simp only [Option.some.injEq] at hcompute
                    subst result
                    refine ⟨``Nat.lor, ?_,
                      liftReflection htable.natLor
                        context.theoryPrimitives.natLOr⟩
                    simpa only [haddr, ← hfixed, ← hnatLor] using
                      htable.natLor.2
                  · rw [if_neg hopLor] at hcompute
                    by_cases hopXor : addr == fixed.natXor
                    · rw [if_pos hopXor] at hcompute
                      have haddr := beq_iff_eq.mp hopXor
                      simp only [Option.some.injEq] at hcompute
                      subst result
                      refine ⟨``Nat.xor, ?_,
                        liftReflection htable.natXor
                          context.theoryPrimitives.natXor⟩
                      simpa only [haddr, ← hfixed, ← hnatXor] using
                        htable.natXor.2
                    · rw [if_neg hopXor] at hcompute
                      by_cases hopShiftLeft : addr == fixed.natShiftLeft
                      · rw [if_pos hopShiftLeft] at hcompute
                        have haddr := beq_iff_eq.mp hopShiftLeft
                        by_cases hbound : b < 2 ^ 64
                        · rw [if_pos hbound] at hcompute
                          simp only [Option.some.injEq] at hcompute
                          subst result
                          refine ⟨``Nat.shiftLeft, ?_,
                            liftReflection htable.natShiftLeft
                              context.theoryPrimitives.natShiftLeft⟩
                          simpa only [haddr, ← hfixed, ← hnatShiftLeft] using
                            htable.natShiftLeft.2
                        · rw [if_neg hbound] at hcompute
                          contradiction
                      · rw [if_neg hopShiftLeft] at hcompute
                        by_cases hopShiftRight : addr == fixed.natShiftRight
                        · rw [if_pos hopShiftRight] at hcompute
                          have haddr := beq_iff_eq.mp hopShiftRight
                          by_cases hbound : b < 2 ^ 64
                          · rw [if_pos hbound] at hcompute
                            simp only [Option.some.injEq] at hcompute
                            subst result
                            refine ⟨``Nat.shiftRight, ?_,
                              liftReflection htable.natShiftRight
                                context.theoryPrimitives.natShiftRight⟩
                            simpa only [haddr, ← hfixed,
                              ← hnatShiftRight] using
                              htable.natShiftRight.2
                          · rw [if_neg hbound] at hcompute
                            contradiction
                        · rw [if_neg hopShiftRight] at hcompute
                          contradiction

/-- A successful binary-Nat computation is classified as arithmetic and not
as a predicate by the actual production readers.  Arithmetic membership
comes from the same ordered address tests as `computeNatBin`; exclusion from
the predicate table is derived constructively from the distinct trusted
Theory names, rather than from native comparison of concrete hashes. -/
theorem computeNatBin_classifiers
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {addr : Address} {a b result : Nat}
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s)
    (hcompute : computeNatBin addr PrimAddrs.canonical a b = some result) :
    (RecM.isNatBinArithAddr addr).run methods s = .ok true s ∧
      (RecM.isNatBinPredAddr addr).run methods s = .ok false s := by
  have htable := context.stateTable hI
  have hcanonical := hI.noAccel_primitives
  have hnatAdd : s.prims.natAdd.addr = PrimAddrs.canonical.natAdd := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natAdd hcanonical
  have hnatSub : s.prims.natSub.addr = PrimAddrs.canonical.natSub := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natSub hcanonical
  have hnatMul : s.prims.natMul.addr = PrimAddrs.canonical.natMul := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natMul hcanonical
  have hnatDiv : s.prims.natDiv.addr = PrimAddrs.canonical.natDiv := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natDiv hcanonical
  have hnatMod : s.prims.natMod.addr = PrimAddrs.canonical.natMod := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natMod hcanonical
  have hnatPow : s.prims.natPow.addr = PrimAddrs.canonical.natPow := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natPow hcanonical
  have hnatGcd : s.prims.natGcd.addr = PrimAddrs.canonical.natGcd := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natGcd hcanonical
  have hnatLand : s.prims.natLand.addr = PrimAddrs.canonical.natLand := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natLand hcanonical
  have hnatLor : s.prims.natLor.addr = PrimAddrs.canonical.natLor := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natLor hcanonical
  have hnatXor : s.prims.natXor.addr = PrimAddrs.canonical.natXor := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natXor hcanonical
  have hnatShiftLeft :
      s.prims.natShiftLeft.addr = PrimAddrs.canonical.natShiftLeft := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natShiftLeft hcanonical
  have hnatShiftRight :
      s.prims.natShiftRight.addr = PrimAddrs.canonical.natShiftRight := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natShiftRight hcanonical
  have classify {id : KId .anon} {name : Lean.Name}
      (hid : PrimitiveIdAgrees world id name)
      (harith :
        (id.addr == s.prims.natAdd.addr ||
          id.addr == s.prims.natSub.addr ||
          id.addr == s.prims.natMul.addr ||
          id.addr == s.prims.natDiv.addr ||
          id.addr == s.prims.natMod.addr ||
          id.addr == s.prims.natPow.addr ||
          id.addr == s.prims.natGcd.addr ||
          id.addr == s.prims.natLand.addr ||
          id.addr == s.prims.natLor.addr ||
          id.addr == s.prims.natXor.addr ||
          id.addr == s.prims.natShiftLeft.addr ||
          id.addr == s.prims.natShiftRight.addr) = true)
      (hneBeq : name ≠ ``Nat.beq) (hneBle : name ≠ ``Nat.ble)
      (haddr : addr = id.addr) :
      (RecM.isNatBinArithAddr addr).run methods s = .ok true s ∧
        (RecM.isNatBinPredAddr addr).run methods s = .ok false s := by
    constructor
    · unfold RecM.isNatBinArithAddr RecM.prims
      change EStateM.Result.ok
        (addr == s.prims.natAdd.addr ||
          addr == s.prims.natSub.addr ||
          addr == s.prims.natMul.addr ||
          addr == s.prims.natDiv.addr ||
          addr == s.prims.natMod.addr ||
          addr == s.prims.natPow.addr ||
          addr == s.prims.natGcd.addr ||
          addr == s.prims.natLand.addr ||
          addr == s.prims.natLor.addr ||
          addr == s.prims.natXor.addr ||
          addr == s.prims.natShiftLeft.addr ||
          addr == s.prims.natShiftRight.addr) s = .ok true s
      rw [haddr, harith]
    · have hbeq := hid.addr_ne htable.natBeq hneBeq
      have hble := hid.addr_ne htable.natBle hneBle
      unfold RecM.isNatBinPredAddr RecM.prims
      change EStateM.Result.ok
        (addr == s.prims.natBeq.addr || addr == s.prims.natBle.addr) s =
          .ok false s
      simp [haddr, hbeq, hble]
  generalize hfixed : PrimAddrs.canonical = fixed at hcompute
  unfold computeNatBin at hcompute
  by_cases hopAdd : addr == fixed.natAdd
  · rw [if_pos hopAdd] at hcompute
    apply classify htable.natAdd (by simp) (by decide) (by decide)
    simpa only [← hfixed, ← hnatAdd] using beq_iff_eq.mp hopAdd
  · rw [if_neg hopAdd] at hcompute
    by_cases hopSub : addr == fixed.natSub
    · rw [if_pos hopSub] at hcompute
      apply classify htable.natSub (by simp) (by decide) (by decide)
      simpa only [← hfixed, ← hnatSub] using beq_iff_eq.mp hopSub
    · rw [if_neg hopSub] at hcompute
      by_cases hopMul : addr == fixed.natMul
      · rw [if_pos hopMul] at hcompute
        apply classify htable.natMul (by simp) (by decide) (by decide)
        simpa only [← hfixed, ← hnatMul] using beq_iff_eq.mp hopMul
      · rw [if_neg hopMul] at hcompute
        by_cases hopDiv : addr == fixed.natDiv
        · rw [if_pos hopDiv] at hcompute
          apply classify htable.natDiv (by simp) (by decide) (by decide)
          simpa only [← hfixed, ← hnatDiv] using beq_iff_eq.mp hopDiv
        · rw [if_neg hopDiv] at hcompute
          by_cases hopMod : addr == fixed.natMod
          · rw [if_pos hopMod] at hcompute
            apply classify htable.natMod (by simp) (by decide) (by decide)
            simpa only [← hfixed, ← hnatMod] using beq_iff_eq.mp hopMod
          · rw [if_neg hopMod] at hcompute
            by_cases hopPow : addr == fixed.natPow
            · rw [if_pos hopPow] at hcompute
              apply classify htable.natPow (by simp) (by decide) (by decide)
              simpa only [← hfixed, ← hnatPow] using beq_iff_eq.mp hopPow
            · rw [if_neg hopPow] at hcompute
              by_cases hopGcd : addr == fixed.natGcd
              · rw [if_pos hopGcd] at hcompute
                apply classify htable.natGcd (by simp) (by decide) (by decide)
                simpa only [← hfixed, ← hnatGcd] using beq_iff_eq.mp hopGcd
              · rw [if_neg hopGcd] at hcompute
                by_cases hopLand : addr == fixed.natLand
                · rw [if_pos hopLand] at hcompute
                  apply classify htable.natLand (by simp) (by decide) (by decide)
                  simpa only [← hfixed, ← hnatLand] using beq_iff_eq.mp hopLand
                · rw [if_neg hopLand] at hcompute
                  by_cases hopLor : addr == fixed.natLor
                  · rw [if_pos hopLor] at hcompute
                    apply classify htable.natLor (by simp) (by decide) (by decide)
                    simpa only [← hfixed, ← hnatLor] using beq_iff_eq.mp hopLor
                  · rw [if_neg hopLor] at hcompute
                    by_cases hopXor : addr == fixed.natXor
                    · rw [if_pos hopXor] at hcompute
                      apply classify htable.natXor (by simp) (by decide) (by decide)
                      simpa only [← hfixed, ← hnatXor] using beq_iff_eq.mp hopXor
                    · rw [if_neg hopXor] at hcompute
                      by_cases hopShiftLeft : addr == fixed.natShiftLeft
                      · rw [if_pos hopShiftLeft] at hcompute
                        apply classify htable.natShiftLeft (by simp)
                          (by decide) (by decide)
                        simpa only [← hfixed, ← hnatShiftLeft] using
                          beq_iff_eq.mp hopShiftLeft
                      · rw [if_neg hopShiftLeft] at hcompute
                        by_cases hopShiftRight : addr == fixed.natShiftRight
                        · rw [if_pos hopShiftRight] at hcompute
                          apply classify htable.natShiftRight (by simp)
                            (by decide) (by decide)
                          simpa only [← hfixed, ← hnatShiftRight] using
                            beq_iff_eq.mp hopShiftRight
                        · rw [if_neg hopShiftRight] at hcompute
                          contradiction

/-- Either trusted binary-Nat predicate address is classified by the two
production readers exactly as intended.  All twelve arithmetic exclusions
come from distinct Theory names through `PrimitiveIdAgrees.addr_ne`; no
concrete content-hash comparison enters the proof. -/
theorem natPredicate_classifiers
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {addr : Address}
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s)
    (haddr : addr = s.prims.natBeq.addr ∨
      addr = s.prims.natBle.addr) :
    (RecM.isNatBinArithAddr addr).run methods s = .ok false s ∧
      (RecM.isNatBinPredAddr addr).run methods s = .ok true s := by
  have htable := context.stateTable hI
  have classify {id : KId .anon}
      (haddr : addr = id.addr)
      (harith :
        (id.addr == s.prims.natAdd.addr ||
          id.addr == s.prims.natSub.addr ||
          id.addr == s.prims.natMul.addr ||
          id.addr == s.prims.natDiv.addr ||
          id.addr == s.prims.natMod.addr ||
          id.addr == s.prims.natPow.addr ||
          id.addr == s.prims.natGcd.addr ||
          id.addr == s.prims.natLand.addr ||
          id.addr == s.prims.natLor.addr ||
          id.addr == s.prims.natXor.addr ||
          id.addr == s.prims.natShiftLeft.addr ||
          id.addr == s.prims.natShiftRight.addr) = false)
      (hpred :
        (id.addr == s.prims.natBeq.addr ||
          id.addr == s.prims.natBle.addr) = true) :
      (RecM.isNatBinArithAddr addr).run methods s = .ok false s ∧
        (RecM.isNatBinPredAddr addr).run methods s = .ok true s := by
    constructor
    · unfold RecM.isNatBinArithAddr RecM.prims
      change EStateM.Result.ok
        (addr == s.prims.natAdd.addr ||
          addr == s.prims.natSub.addr ||
          addr == s.prims.natMul.addr ||
          addr == s.prims.natDiv.addr ||
          addr == s.prims.natMod.addr ||
          addr == s.prims.natPow.addr ||
          addr == s.prims.natGcd.addr ||
          addr == s.prims.natLand.addr ||
          addr == s.prims.natLor.addr ||
          addr == s.prims.natXor.addr ||
          addr == s.prims.natShiftLeft.addr ||
          addr == s.prims.natShiftRight.addr) s = .ok false s
      rw [haddr, harith]
    · unfold RecM.isNatBinPredAddr RecM.prims
      change EStateM.Result.ok
        (addr == s.prims.natBeq.addr || addr == s.prims.natBle.addr) s =
          .ok true s
      rw [haddr, hpred]
  rcases haddr with hbeq | hble
  · apply classify hbeq
    · simp [htable.natBeq.addr_ne htable.natAdd (by decide),
        htable.natBeq.addr_ne htable.natSub (by decide),
        htable.natBeq.addr_ne htable.natMul (by decide),
        htable.natBeq.addr_ne htable.natDiv (by decide),
        htable.natBeq.addr_ne htable.natMod (by decide),
        htable.natBeq.addr_ne htable.natPow (by decide),
        htable.natBeq.addr_ne htable.natGcd (by decide),
        htable.natBeq.addr_ne htable.natLand (by decide),
        htable.natBeq.addr_ne htable.natLor (by decide),
        htable.natBeq.addr_ne htable.natXor (by decide),
        htable.natBeq.addr_ne htable.natShiftLeft (by decide),
        htable.natBeq.addr_ne htable.natShiftRight (by decide)]
    · simp
  · apply classify hble
    · simp [htable.natBle.addr_ne htable.natAdd (by decide),
        htable.natBle.addr_ne htable.natSub (by decide),
        htable.natBle.addr_ne htable.natMul (by decide),
        htable.natBle.addr_ne htable.natDiv (by decide),
        htable.natBle.addr_ne htable.natMod (by decide),
        htable.natBle.addr_ne htable.natPow (by decide),
        htable.natBle.addr_ne htable.natGcd (by decide),
        htable.natBle.addr_ne htable.natLand (by decide),
        htable.natBle.addr_ne htable.natLor (by decide),
        htable.natBle.addr_ne htable.natXor (by decide),
        htable.natBle.addr_ne htable.natShiftLeft (by decide),
        htable.natBle.addr_ne htable.natShiftRight (by decide)]
    · simp

/-- Reflect the concrete predicate decision selected by production into the
corresponding Lean4Lean `Nat.beq` or `Nat.ble` equation. -/
theorem natPredicate_defeq
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    {addr : Address} {a b : Nat}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    (hcatalog : TrustedCatalogRel trProj world)
    (hcanonical : prims.CanonicalAnon)
    (haddr : addr = prims.natBeq.addr ∨ addr = prims.natBle.addr) :
    ∃ name decision,
      world.nameOf addr = some name ∧
      decision =
        (if addr == prims.natBeq.addr then a == b else a.ble b) ∧
      world.venv.IsDefEqU uvars Δ.toCtx
        (.app (.app (.const name []) (.natLit a)) (.natLit b))
        (.boolLit decision) := by
  have htable := context.table prims hcanonical
  have liftReflection {name : Lean.Name} {f : Nat → Nat → Bool}
      {primitiveId : KId .anon}
      (hid : PrimitiveIdAgrees world primitiveId name)
      (hreflect : world.venv.ReflectsNatNatBool name f) :
      world.venv.IsDefEqU uvars Δ.toCtx
        (.app (.app (.const name []) (.natLit a)) (.natLit b))
        (.boolLit (f a b)) := by
    have h := hreflect (hid.contains hcatalog) a b
    have h := h.instL (U' := uvars) (ls := []) (by simp)
    simpa [VExpr.instL] using h.weak0 world.venvWF (Γ := Δ.toCtx)
  rcases haddr with hbeq | hble
  · subst addr
    refine ⟨``Nat.beq, a == b, htable.natBeq.2, by simp, ?_⟩
    have hdecision : Nat.beq a b = (a == b) := by
      apply Bool.eq_iff_iff.mpr
      simp
    simpa only [hdecision] using
      (liftReflection htable.natBeq context.theoryPrimitives.natBEq)
  · subst addr
    have hne := htable.natBle.addr_ne htable.natBeq (by decide)
    refine ⟨``Nat.ble, a.ble b, htable.natBle.2, by simp [hne], ?_⟩
    exact liftReflection htable.natBle context.theoryPrimitives.natBLE

end NoDeltaPrimitiveContext

namespace TrKExprS

/-- A successful production Nat-literal extraction has the canonical Theory
translation.  The constructor case is not justified by address equality
alone: `NoDeltaPrimitiveTableAgrees` fixes the address's trusted name, while
`HasPrimitives.natZero` fixes its declaration to zero universe parameters.
Consequently a translated `Nat.zero` accepted by `extractNatLit` cannot carry
spurious universe arguments. -/
theorem of_extractNatLit
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    {e : KExpr .anon} {eV : VExpr} {n : Nat}
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Δ e eV)
    (hextract : extractNatLit e prims = some n) :
    eV = .natLit n := by
  cases e with
  | nat value blob info =>
      simp only [extractNatLit, Option.some.injEq] at hextract
      subst n
      let .nat _ := htr
      rfl
  | const id us info =>
      simp only [extractNatLit] at hextract
      split at hextract
      · rename_i hzero
        have haddr : id.addr = prims.natZero.addr :=
          beq_iff_eq.mp hzero
        simp only [Option.some.injEq] at hextract
        subst n
        let .const (c := c) (ci := ci) hname hlookup _ hsize := htr
        have hc : c = ``Nat.zero := by
          rw [haddr, htable.natZero.2] at hname
          exact Option.some.inj hname.symm
        subst c
        have hci := hprims.natZero hlookup
        subst ci
        have hus : us = #[] := Array.eq_empty_of_size_eq_zero hsize
        subst us
        rfl
      · contradiction
  | var idx name info => simp [extractNatLit] at hextract
  | fvar id name info => simp [extractNatLit] at hextract
  | sort u info => simp [extractNatLit] at hextract
  | app f a info => simp [extractNatLit] at hextract
  | lam name bi ty body info => simp [extractNatLit] at hextract
  | all name bi ty body info => simp [extractNatLit] at hextract
  | letE name ty val body nondep info => simp [extractNatLit] at hextract
  | prj id field val info => simp [extractNatLit] at hextract
  | str value blob info => simp [extractNatLit] at hextract

/-- The numeral materialized by the Nat reducer translates directly to the
canonical Theory numeral. -/
theorem natExprFromValue
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (n : Nat) :
    TrKExprS world.venv uvars world.nameOf trProj Δ
      (RecM.natExprFromValue (m := .anon) n) (.natLit n) := by
  rw [RecM.natExprFromValue, KExpr.mkNat_shape]
  exact .nat (htable.nat.contains hcatalog)

/-- The finite Bool constant selected by the Nat predicate reducer translates
to the matching Theory Bool literal.  `HasPrimitives` fixes both declarations
to zero universe parameters, so no universe payload can be hidden behind the
trusted address. -/
theorem boolExprFromDecision
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives)
    (decision : Bool) :
    TrKExprS world.venv uvars world.nameOf trProj Δ
      (KExpr.mkConst
        (if decision then prims.boolTrue else prims.boolFalse) #[])
      (.boolLit decision) := by
  cases decision with
  | false =>
      rw [KExpr.mkConst_shape]
      obtain ⟨ci, hlookup⟩ := htable.boolFalse.contains hcatalog
      have hci := hprims.boolFalse hlookup
      subst ci
      exact
        (TrKExprS.const (Δ := Δ) (uvars := uvars)
          htable.boolFalse.2 hlookup (by simp) (by simp))
  | true =>
      rw [KExpr.mkConst_shape]
      obtain ⟨ci, hlookup⟩ := htable.boolTrue.contains hcatalog
      have hci := hprims.boolTrue hlookup
      subst ci
      exact
        (TrKExprS.const (Δ := Δ) (uvars := uvars)
          htable.boolTrue.2 hlookup (by simp) (by simp))

/-- Invert a translated exact binary application after its concrete head has
been identified with a reflected primitive.  The reflected equation proves
that `name` is usable with no universe arguments; uniqueness of the constant
lookup then forces the concrete source's universe array to be empty. -/
theorem natBinExact_inv
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {sourceV resultV : VExpr} {name : Lean.Name} {a b : Nat}
    (hΔ : KVLCtx.WF world.venv uvars Δ)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hname : world.nameOf headId.addr = some name)
    (hreflect : world.venv.IsDefEqU uvars Δ.toCtx
      (.app (.app (.const name []) (.natLit a)) (.natLit b))
      resultV) :
    ∃ argAV argBV,
      sourceV = (.app (.app (.const name []) argAV) argBV) ∧
      TrKExprS world.venv uvars world.nameOf trProj Δ argA argAV ∧
      TrKExprS world.venv uvars world.nameOf trProj Δ argB argBV := by
  let .app _ _ hprefix hargB := hsource
  let .app _ _ hhead hargA := hprefix
  let .const (c := c) (ci := ci) hheadName hlookup _ hsize := hhead
  have hc : c = name := by
    rw [hname] at hheadName
    exact Option.some.inj hheadName.symm
  subst c
  obtain ⟨_, hreflectTyped⟩ := hreflect
  have happType := hreflectTyped.hasType.1
  obtain ⟨_, _, hprefixType, _⟩ :=
    happType.app_inv world.venvWF.ordered hΔ
  obtain ⟨_, _, hconstType, _⟩ :=
    hprefixType.app_inv world.venvWF.ordered hΔ
  obtain ⟨reflectedCi, hreflectedLookup, _, hreflectedArity⟩ :=
    hconstType.const_inv world.venvWF.ordered hΔ
  have hci : ci = reflectedCi := by
    rw [hlookup] at hreflectedLookup
    exact Option.some.inj hreflectedLookup
  subst reflectedCi
  have hzero : ci.uvars = 0 := by simpa using hreflectedArity.symm
  have husSize : us.size = 0 := hsize.trans hzero
  have hus : us = #[] := Array.eq_empty_of_size_eq_zero husSize
  subst us
  exact ⟨_, _, rfl, hargA, hargB⟩

/-- A translation of a left-associated application fold contains a
translation of its initial function.  This is the structural inversion used
to recover each prefix while suffix congruence proceeds left-to-right. -/
theorem foldlMkApp_initial
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {rest : List (KExpr .anon)}
    {initial : KExpr .anon} {finalV : VExpr}
    (h : TrKExprS world.venv uvars world.nameOf trProj Δ
      (rest.foldl KExpr.mkApp initial) finalV) :
    ∃ initialV,
      TrKExprS world.venv uvars world.nameOf trProj Δ initial initialV := by
  induction rest generalizing initial finalV with
  | nil =>
      exact ⟨finalV, h⟩
  | cons arg rest ih =>
      have hprefix := ih (initial := KExpr.mkApp initial arg) h
      obtain ⟨prefixV, hprefix⟩ := hprefix
      rw [KExpr.mkApp_shape] at hprefix
      let .app _ _ hinitial _ := hprefix
      exact ⟨_, hinitial⟩

end TrKExprS

namespace WhnfPost

/-- If the shared argument normalizer returns something recognized by the
production literal extractor, its retained callback postcondition specializes
to definitional equality with the corresponding Theory numeral. -/
theorem of_extractNatLit
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    {sourceV : VExpr} {result : KExpr .anon} {n : Nat}
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives)
    (hpost : WhnfPost trProj world uvars Δ sourceV result)
    (hextract : extractNatLit result prims = some n) :
    world.venv.IsDefEqU uvars Δ.toCtx sourceV (.natLit n) := by
  obtain ⟨resultV, hresult, hdefeq⟩ := hpost
  have heq := hresult.of_extractNatLit htable hprims hextract
  simpa only [heq] using hdefeq

end WhnfPost

namespace WhnfMeaning

/-- Definitional equality of a function is preserved when both sides are
applied to the same translated argument.  The source application supplies
the function/argument typing facts; translation uniqueness reconciles its
function translation with the one stored in the incoming meaning. -/
theorem appSameArg
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Δ : KVLCtx} (hΔ : KVLCtx.WF world.venv uvars Δ)
    {source result arg : KExpr .anon} {sourceInfo : ExprInfo .anon}
    {sourceAppV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app source arg sourceInfo) sourceAppV)
    (hmeaning : WhnfMeaning trProj world uvars Δ source result) :
    WhnfMeaning trProj world uvars Δ (.app source arg sourceInfo)
      (KExpr.mkApp result arg) := by
  cases hsource with
  | @app _ _ _ _ sourceV₀ argV A B hsourceType hargType
      hsourceTr hargTr =>
      obtain ⟨sourceV, resultV, hsourceTr', hresultTr, hdefeq⟩ := hmeaning
      have hctx := KVLCtx.IsDefEq.refl world.venvWF hΔ
      have hsourceEq := hsourceTr.uniq world.venvWF theory.literalWF
        theory.projections hctx hsourceTr'
      have hfunEq := hsourceEq.trans world.venvWF hΔ hdefeq
      have hfunEqTyped := hfunEq.of_l world.venvWF hΔ hsourceType
      have hargEq : world.venv.IsDefEqU uvars Δ.toCtx _ _ :=
        Lean4Lean.VEnv.IsDefEqU.refl ⟨_, hargType⟩
      have hargEqTyped := hargEq.of_l world.venvWF hΔ hargType
      have hresultTr' : TrKExprS world.venv uvars world.nameOf trProj Δ
          (KExpr.mkApp result arg) (.app resultV argV) := by
        rw [KExpr.mkApp_shape]
        exact .app hfunEqTyped.hasType.2 hargType hresultTr hargTr
      exact ⟨_, _, .app hsourceType hargType hsourceTr hargTr, hresultTr',
        (hfunEqTyped.appDF hargEqTyped).toU⟩

/-- Fold `appSameArg` over a concrete left-associated suffix.  The final
source translation alone suffices: `foldlMkApp_initial` recovers the prefix
translation required at each induction step. -/
theorem foldlMkApp
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Δ : KVLCtx} (hΔ : KVLCtx.WF world.venv uvars Δ)
    {rest : List (KExpr .anon)} {source result : KExpr .anon}
    {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (rest.foldl KExpr.mkApp source) sourceV)
    (hmeaning : WhnfMeaning trProj world uvars Δ source result) :
    WhnfMeaning trProj world uvars Δ
      (rest.foldl KExpr.mkApp source)
      (rest.foldl KExpr.mkApp result) := by
  induction rest generalizing source result sourceV with
  | nil =>
      exact hmeaning
  | cons arg rest ih =>
      have hprefix := TrKExprS.foldlMkApp_initial
        (rest := rest) hsource
      obtain ⟨prefixV, hprefix⟩ := hprefix
      have hstep := appSameArg theory hΔ hprefix hmeaning
      exact ih hsource hstep

/-- Array form matching `finishAppResultSpec` and production's spine arrays. -/
theorem mkAppN
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Δ : KVLCtx} (hΔ : KVLCtx.WF world.venv uvars Δ)
    {args : Array (KExpr .anon)} {source result : KExpr .anon}
    {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (KExpr.mkAppN source args) sourceV)
    (hmeaning : WhnfMeaning trProj world uvars Δ source result) :
    WhnfMeaning trProj world uvars Δ
      (KExpr.mkAppN source args) (KExpr.mkAppN result args) := by
  rw [KExpr.mkAppN] at hsource ⊢
  have hsource' : TrKExprS world.venv uvars world.nameOf trProj Δ
      (args.toList.foldl KExpr.mkApp source) sourceV := by
    simpa only [Array.foldl_toList] using hsource
  have hresult := foldlMkApp theory hΔ hsource' hmeaning
  simpa only [Array.foldl_toList, KExpr.mkAppN] using hresult

/-- Replace the concrete source of a meaning proof when both concrete
expressions translate to the same Theory expression.  This is the metadata
bridge needed after `collectSpine`: production retains the original
application metadata, while `mkAppN` rebuilds a canonical metadata-free
spine. -/
theorem ofSharedSourceTranslation
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source canonical result : KExpr .anon} {sourceV : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hcanonical : TrKExprS world.venv uvars world.nameOf trProj Delta
      canonical sourceV)
    (hmeaning : WhnfMeaning trProj world uvars Delta canonical result) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨canonicalV, resultV, hcanonical', hresult, hdefeq⟩ := hmeaning
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have hsourceEq := hcanonical.uniq world.venvWF theory.literalWF
    theory.projections hctx hcanonical'
  exact ⟨sourceV, resultV, hsource, hresult,
    hsourceEq.trans world.venvWF hDelta hdefeq⟩

/-- Compose the exact two argument callback posts with one reflected Nat
primitive equation.  The source translation is deliberately fixed to the
primitive application shape, so no translation-uniqueness or projection
oracle is needed: both callback posts are stated against the very argument
translations embedded in that source. -/
theorem natBinExact
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Δ : KVLCtx} {prims : Primitives .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult resultExpr : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {name : Lean.Name} {argAV argBV resultV : VExpr} {a b : Nat}
    (hΔ : KVLCtx.WF world.venv uvars Δ)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo)
      (.app (.app (.const name []) argAV) argBV))
    (hargA : WhnfPost trProj world uvars Δ argAV argAResult)
    (hargB : WhnfPost trProj world uvars Δ argBV argBResult)
    (hextractA : extractNatLit argAResult prims = some a)
    (hextractB : extractNatLit argBResult prims = some b)
    (hreflect : world.venv.IsDefEqU uvars Δ.toCtx
      (.app (.app (.const name []) (.natLit a)) (.natLit b))
      resultV)
    (hresult : TrKExprS world.venv uvars world.nameOf trProj Δ resultExpr
      resultV) :
    WhnfMeaning trProj world uvars Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo)
      resultExpr := by
  let .app hprefixType hargBType hprefixTr hargBTr := hsource
  let .app hconstType hargAType hconstTr hargATr := hprefixTr
  have hargADef := hargA.of_extractNatLit htable hprims hextractA
  have hargBDef := hargB.of_extractNatLit htable hprims hextractB
  have hargADefTyped :=
    hargADef.of_l world.venvWF hΔ hargAType
  have hprefixDef := hconstType.appDF hargADefTyped
  have hprefixDefTyped :=
    hprefixDef.toU.of_l world.venvWF hΔ hprefixType
  have hargBDefTyped :=
    hargBDef.of_l world.venvWF hΔ hargBType
  have hsourceDef := (hprefixDefTyped.appDF hargBDefTyped).toU
  exact ⟨_, _, hsource, hresult,
    hsourceDef.trans world.venvWF hΔ hreflect⟩

end WhnfMeaning

namespace RecM

/-- State-only Hoare closure for the exact two-argument predicate helper.
Every callback miss/error and both extraction misses preserve the invariant;
the successful Bool intern is justified by the finite generated support and
collision boundary.  Semantic meaning of a hit is supplied separately by
`tryReduceNatWithSuccMode_binPredExact_acceptance`. -/
theorem tryReduceNatPredicate_bin_inv_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {addr : Address} {argA argB : KExpr .anon} {argAV argBV : VExpr}
    (hargASupport : support argA)
    (hargATr : TrKExprS world.venv uvars world.nameOf trProj Δ argA argAV)
    (hargBSupport : support argB)
    (hargBTr : TrKExprS world.venv uvars world.nameOf trProj Δ argB argBV) :
    RecM.WF .noAccel semantics trProj world support uvars Δ s
      (tryReduceNatPredicate addr #[argA, argB]) (fun _ _ => True) := by
  unfold tryReduceNatPredicate
  have hzero : (#[argA, argB] : Array (KExpr .anon))[0]! = argA := by
    simp
  have hone : (#[argA, argB] : Array (KExpr .anon))[1]! = argB := by
    simp
  rw [hzero, hone]
  apply RecM.WF.bind <|
    RecM.WF.withInv <| whnfNatReducerArg_post_wf hargASupport hargATr
  intro first afterFirst hfirst
  cases first with
  | none =>
      exact RecM.WF.pure fun _ => trivial
  | some firstResult =>
      have hI₁ := hfirst.1
      apply RecM.WF.bind (prims_wf (s := afterFirst))
      intro prims afterRead hread
      rcases hread with ⟨rfl, rfl⟩
      match hextractA : extractNatLit firstResult afterRead.prims with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some a =>
          apply RecM.WF.bind <|
            RecM.WF.withInv <|
              whnfNatReducerArg_post_wf hargBSupport hargBTr
          intro second afterSecond hsecond
          cases second with
          | none =>
              exact RecM.WF.pure fun _ => trivial
          | some secondResult =>
              match hextractB :
                  extractNatLit secondResult afterRead.prims with
              | none =>
                  simp only [hextractB]
                  exact RecM.WF.pure fun _ => trivial
              | some b =>
                  simp only [hextractB]
                  let decision :=
                    if addr == afterRead.prims.natBeq.addr then
                      a == b
                    else a.ble b
                  let resultExpr := KExpr.mkConst
                    (if decision then afterRead.prims.boolTrue
                      else afterRead.prims.boolFalse) #[]
                  have hresultSupport : support resultExpr := by
                    exact context.generated.boolConst
                      hI₁.noAccel_primitives decision
                  apply RecM.WF.bind <| RecM.WF.liftTcM <|
                    TcM.intern_whnf_wf context.collisionFree hresultSupport
                  intro interned afterIntern hintern
                  have hinterned : interned = resultExpr := hintern.1
                  subst interned
                  simpa [decision, resultExpr, finishAppResult] using
                    (RecM.WF.pure
                      (layer := .noAccel) (semantics := semantics)
                      (trProj := trProj) (world := world)
                      (support := support) (uvars := uvars) (Δ := Δ)
                      (s := afterIntern) (a := some resultExpr)
                      (fun _ => trivial))

/-- State-only Hoare closure for an exact two-argument binary Nat
application through the production dispatcher.  The theorem covers both
classifier orders, every arithmetic/predicate miss, all callback errors, and
both successful result forms.  Hit semantics remains separated into the
arithmetic and predicate acceptance theorems below. -/
theorem tryReduceNatWithSuccMode_bin_inv_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon} {sourceV : VExpr}
    (hsourceSupport : support
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB])) :
    RecM.WF .noAccel semantics trProj world support uvars Δ s
      (tryReduceNatWithSuccMode
        (.app (.app (.const headId us headInfo) argA firstInfo)
          argB secondInfo) natSuccMode)
      (fun _ _ => True) := by
  let .app _ _ hprefix hargBTr := hsource
  let .app _ _ _ hargATr := hprefix
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa using hinputSupport.2 0 (by simp)
  have hargBSupport : support argB := by
    simpa using hinputSupport.2 1 (by simp)
  unfold tryReduceNatWithSuccMode
  rw [hspine]
  apply RecM.WF.bind (prims_wf (s := s))
  intro prims afterRead hread
  rcases hread with ⟨rfl, rfl⟩
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  apply RecM.WF.bind (isNatBinArithAddr_inv_wf headId.addr)
  intro isArith afterArith hafterArith
  subst afterArith
  apply RecM.WF.bind (isNatBinPredAddr_inv_wf headId.addr)
  intro isPred afterPred hafterPred
  subst afterPred
  match isArith, isPred with
  | false, false =>
      simp
      exact RecM.WF.pure fun _ => trivial
  | false, true =>
      simpa using tryReduceNatPredicate_bin_inv_wf context
        hargASupport hargATr hargBSupport hargBTr
  | true, true =>
      simpa using tryReduceNatPredicate_bin_inv_wf context
        hargASupport hargATr hargBSupport hargBTr
  | true, false =>
      simp only [Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.false_eq_true, if_false]
      apply RecM.WF.bind (Q₂ := fun _ _ => True) <|
        whnfNatReducerArg_post_wf hargASupport hargATr
      intro first afterFirst hfirst
      cases first with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some firstResult =>
          apply RecM.WF.bind (Q₂ := fun _ _ => True) <|
            whnfNatReducerArg_post_wf hargBSupport hargBTr
          intro second afterSecond hsecond
          cases second with
          | none =>
              exact RecM.WF.pure fun _ => trivial
          | some secondResult =>
              match hextractA : extractNatLit firstResult afterRead.prims with
              | none =>
                  exact RecM.WF.pure fun _ => trivial
              | some a =>
                  match hextractB :
                      extractNatLit secondResult afterRead.prims with
                  | none =>
                      simp only [hextractB]
                      exact RecM.WF.pure fun _ => trivial
                  | some b =>
                      simp only [hextractB]
                      match hcompute : computeNatBin headId.addr
                          PrimAddrs.canonical a b with
                      | none =>
                          exact RecM.WF.pure fun _ => trivial
                      | some result =>
                          simpa [finishAppResult] using
                            (RecM.WF.pure
                              (layer := .noAccel) (semantics := semantics)
                              (trProj := trProj) (world := world)
                              (support := support) (uvars := uvars) (Δ := Δ)
                              (s := afterSecond)
                              (a := some
                                (natExprFromValue (m := .anon) result))
                              (fun _ => trivial))

/-- Exact two-argument execution of the dedicated Nat predicate helper.  The
only mutation is the explicitly supplied Bool-constant intern; the empty
application suffix performs no further writes. -/
theorem tryReduceNatPredicate_exact
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {argA argB argAResult argBResult : KExpr .anon}
    {a b : Nat} {decision : Bool} {result : KExpr .anon}
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractB : extractNatLit argBResult prims = some b)
    (hdecision :
      (if addr == prims.natBeq.addr then a == b else a.ble b) = decision)
    (hintern : TcM.intern
      (KExpr.mkConst
        (if decision then prims.boolTrue else prims.boolFalse) #[]) s₂ =
      .ok result s₃) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok (some result) s₃ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractB]
  simp only
  rw [hdecision]
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern _) _ s₂ = _
  unfold EStateM.bind
  rw [hintern]
  simp [finishAppResult]
  rfl

/-- General-suffix execution of the predicate helper.  The first two spine
arguments are consumed by the predicate; `finishAppResult` rebuilds exactly
the supplied trailing array and may grow only the intern table. -/
theorem tryReduceNatPredicate_suffixExact
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {args suffix : Array (KExpr .anon)}
    {argA argB argAResult argBResult requested base final : KExpr .anon}
    {a b : Nat} {decision : Bool}
    (hargs : args = #[argA, argB] ++ suffix)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractB : extractNatLit argBResult prims = some b)
    (hdecision :
      (if addr == prims.natBeq.addr then a == b else a.ble b) = decision)
    (hrequested : requested = KExpr.mkConst
      (if decision then prims.boolTrue else prims.boolFalse) #[])
    (hintern : TcM.intern requested s₂ = .ok base s₃)
    (hfinish : (finishAppResult base args 2).run methods s₃ =
      .ok final s₄) :
    (tryReduceNatPredicate addr args).run methods s =
      .ok (some final) s₄ := by
  have hzero : args[0]! = argA := by
    rw [hargs]
    grind
  have hone : args[1]! = argB := by
    rw [hargs]
    grind
  unfold tryReduceNatPredicate
  rw [hzero, hone, ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractB]
  simp only
  rw [hdecision, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern _) _ s₂ = _
  unfold EStateM.bind
  rw [← hrequested, hintern]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((finishAppResult base args 2).run methods) _ s₃ = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

/-- A miss from the first predicate argument callback stops immediately and
retains that callback's exact partial state. -/
theorem tryReduceNatPredicate_argAMiss
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {addr : Address} {argA argB : KExpr .anon}
    (hargA : (whnfNatReducerArg argA).run methods s = .ok none s₁) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok none s₁ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  rfl

/-- An error from the first predicate argument callback is propagated without
running the primitive-table read or the second callback. -/
theorem tryReduceNatPredicate_argAError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {addr : Address} {argA argB : KExpr .anon} {err : TcError .anon}
    (hargA : (whnfNatReducerArg argA).run methods s = .error err s₁) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .error err s₁ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]

/-- Failure to recognize the first normalized predicate argument as a literal
is a state-preserving miss after exactly the first callback. -/
theorem tryReduceNatPredicate_extractAMiss
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {argA argB argAResult : KExpr .anon}
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = none) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok none s₁ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  rfl

/-- A miss from the second predicate argument callback retains all state
changes made by the first and second callbacks. -/
theorem tryReduceNatPredicate_argBMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {argA argB argAResult : KExpr .anon} {a : Nat}
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ = .ok none s₂) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok none s₂ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  rfl

/-- An error from the second predicate argument callback is propagated with
the state reached after the successful first callback. -/
theorem tryReduceNatPredicate_argBError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {argA argB argAResult : KExpr .anon} {a : Nat}
    {err : TcError .anon}
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ = .error err s₂) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .error err s₂ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]

/-- Failure to recognize the second normalized predicate argument as a
literal is a miss at the exact post-second-callback state. -/
theorem tryReduceNatPredicate_extractBMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {addr : Address}
    {argA argB argAResult argBResult : KExpr .anon} {a : Nat}
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hprims : s₁.prims = prims)
    (hextractA : extractNatLit argAResult prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractB : extractNatLit argBResult prims = none) :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok none s₂ := by
  unfold tryReduceNatPredicate
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s₁ = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s₁ = .ok prims s₁ := by
    unfold RecM.prims
    change EStateM.Result.ok s₁.prims s₁ = .ok prims s₁
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextractA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractB]
  rfl

/-- Route an exact two-argument predicate application through the outer Nat
dispatcher.  The theorem pins predicate precedence over the arithmetic body
and delegates the helper's callback/intern trace to
`tryReduceNatPredicate_exact`. -/
theorem tryReduceNatWithSuccMode_binPredExact
    {methods : Methods .anon} {s s' : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB result : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok false s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
    (hhelper : (tryReduceNatPredicate headId.addr #[argA, argB]).run
      methods s = .ok (some result) s') :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s =
      .ok (some result) s' := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_false, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, if_false, if_true]
  simpa using hhelper

/-- Predicate classification has precedence even if an unconstrained method
table reports that the same address is arithmetic too.  Canonical production
states later rule out that overlap; the operational success trace does not
need to assume it away while it is being inverted. -/
theorem tryReduceNatWithSuccMode_binPredAnyExact
    {methods : Methods .anon} {s s' : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB result : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon} {isArith : Bool}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s =
      .ok isArith s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
    (hhelper : (tryReduceNatPredicate headId.addr #[argA, argB]).run
      methods s = .ok (some result) s') :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s =
      .ok (some result) s' := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  cases isArith <;>
    simp only [Bool.not_false, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, if_false, if_true] <;>
    simpa using hhelper

/-- General-spine predicate routing.  Predicate precedence is independent of
the suffix length; the dedicated helper consumes two arguments and returns
the fully rebuilt result. -/
theorem tryReduceNatWithSuccMode_binPredSuffixExact
    {methods : Methods .anon} {s s' : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {isArith : Bool}
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s =
      .ok isArith s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
    (hhelper : (tryReduceNatPredicate headId.addr args).run methods s =
      .ok (some result) s') :
    (tryReduceNatWithSuccMode source natSuccMode).run methods s =
      .ok (some result) s' := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity : (args.size == 1) = false := by
    rw [hargs]
    grind
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort : ¬(args.size < 2) := by
    rw [hargs]
    grind
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  cases isArith <;>
    simp only [Bool.not_false, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, if_false, if_true] <;>
    simpa using hhelper

/-- A predicate-helper miss is returned unchanged by the exact binary outer
dispatcher, including the helper's partial state. -/
theorem tryReduceNatWithSuccMode_binPredMiss
    {methods : Methods .anon} {s s' : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok false s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
    (hhelper : (tryReduceNatPredicate headId.addr #[argA, argB]).run
      methods s = .ok none s') :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s' := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_false, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, if_false, if_true]
  simpa using hhelper

/-- A predicate-helper error is propagated unchanged by the exact binary
outer dispatcher, with no later arithmetic work. -/
theorem tryReduceNatWithSuccMode_binPredError
    {methods : Methods .anon} {s s' : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon} {err : TcError .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok false s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
    (hhelper : (tryReduceNatPredicate headId.addr #[argA, argB]).run
      methods s = .error err s') :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .error err s' := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_false, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, if_false, if_true]
  simpa using hhelper

/-- Exact production execution for the two-argument arithmetic hit.  Keeping
the two classifier equations explicit separates address classification from
the callback/state proof and makes the precedence over Nat predicates
auditable.  Since the spine has exactly two arguments, `finishAppResult`
rebuilds an empty suffix and performs no intern-table mutation. -/
theorem tryReduceNatWithSuccMode_binArithExact
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {a b result : Nat}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult prims = some a)
    (hextractB : extractNatLit argBResult prims = some b)
    (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b =
      some result) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s =
      .ok (some (natExprFromValue result)) s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s =
      EStateM.Result.ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = EStateM.Result.ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractA, hextractB]
  simp only
  rw [hcompute]
  simp [finishAppResult]
  rfl

/-- General-spine arithmetic routing.  The reducer consumes exactly its first
two arguments, then delegates every trailing argument and its possible intern
table growth to the explicit `finishAppResult` execution premise. -/
theorem tryReduceNatWithSuccMode_binArithSuffixExact
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)}
    {argA argB argAResult argBResult final : KExpr .anon}
    {a b result : Nat}
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult prims = some a)
    (hextractB : extractNatLit argBResult prims = some b)
    (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b =
      some result)
    (hfinish :
      (finishAppResult (natExprFromValue result) args 2).run methods s₂ =
        .ok final s₃) :
    (tryReduceNatWithSuccMode source natSuccMode).run methods s =
      .ok (some final) s₃ := by
  have hzero : args[0]! = argA := by
    rw [hargs]
    grind
  have hone : args[1]! = argB := by
    rw [hargs]
    grind
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity : (args.size == 1) = false := by
    rw [hargs]
    grind
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort : ¬(args.size < 2) := by
    rw [hargs]
    grind
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [hzero]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [hone]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractA, hextractB]
  simp only
  rw [hcompute]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    ((finishAppResult (natExprFromValue result) args 2).run methods) _ s₂ = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

/-- A miss from the first arithmetic argument callback stops the inline
binary reducer at that callback's exact post-state. -/
theorem tryReduceNatWithSuccMode_binArithArgAMiss
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s = .ok none s₁) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s₁ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  rfl

/-- An error from the first arithmetic argument callback is propagated before
the second callback and retains the first callback's partial state. -/
theorem tryReduceNatWithSuccMode_binArithArgAError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon} {err : TcError .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s = .error err s₁) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .error err s₁ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]

/-- A miss from the second arithmetic argument callback retains both
callbacks' state and prevents literal extraction. -/
theorem tryReduceNatWithSuccMode_binArithArgBMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ = .ok none s₂) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  rfl

/-- An error from the second arithmetic argument callback is propagated at
its exact partial state before either literal extraction. -/
theorem tryReduceNatWithSuccMode_binArithArgBError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult : KExpr .anon} {err : TcError .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ = .error err s₂) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .error err s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]

/-- Arithmetic literal extraction happens only after both callbacks.  A miss
on the first result therefore returns at the second callback's post-state. -/
theorem tryReduceNatWithSuccMode_binArithExtractAMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult prims = none) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractA]
  rfl

/-- A miss on the second normalized arithmetic literal likewise returns at
the second callback's post-state and performs no result construction. -/
theorem tryReduceNatWithSuccMode_binArithExtractBMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon} {a : Nat}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult prims = some a)
    (hextractB : extractNatLit argBResult prims = none) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractA, hextractB]
  rfl

/-- Bounded power/shift computations may deliberately decline a literal
pair.  That computation miss is pure and returns at the second callback's
post-state. -/
theorem tryReduceNatWithSuccMode_binArithComputeMiss
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {prims : Primitives .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon} {a b : Nat}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hprims : s.prims = prims)
    (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
    (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult prims = some a)
    (hextractB : extractNatLit argBResult prims = some b)
    (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b = none) :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s = .ok none s₂ := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok prims s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok prims s
    rw [hprims]
  rw [hprimsRun]
  simp only
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [harith]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
  unfold EStateM.bind
  rw [hpred]
  simp only [Bool.not_true, Bool.not_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
  unfold EStateM.bind
  rw [hargA]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hargB]
  simp only
  rw [hextractA, hextractB]
  simp only
  rw [hcompute]
  simp
  rfl

/-- An execution-indexed account of every effect needed for a successful
exact two-argument Nat predicate reduction.  In particular, literal B is
interpreted against the primitive table read after callback A, matching the
production helper rather than silently assuming a frozen state. -/
inductive NatPredicateSuccessTrace
    (methods : Methods .anon) (addr : Address)
    (argA argB result : KExpr .anon)
    (s s' : TcState .anon) : Prop
  | intro {s₁ s₂ : TcState .anon}
      {argAResult argBResult : KExpr .anon} {a b : Nat}
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hextractA : extractNatLit argAResult s₁.prims = some a)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractB : extractNatLit argBResult s₁.prims = some b)
      (hintern : TcM.intern
        (KExpr.mkConst
          (if (if addr == s₁.prims.natBeq.addr then a == b else a.ble b)
            then s₁.prims.boolTrue else s₁.prims.boolFalse) #[]) s₂ =
        .ok result s') :
      NatPredicateSuccessTrace methods addr argA argB result s s'

namespace NatPredicateSuccessTrace

/-- Erase a predicate success trace to the exact production-helper run. -/
theorem eval
    {methods : Methods .anon} {addr : Address}
    {argA argB result : KExpr .anon} {s s' : TcState .anon}
    (trace : NatPredicateSuccessTrace methods addr argA argB result s s') :
    (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok (some result) s' := by
  cases trace with
  | intro hargA hextractA hargB hextractB hintern =>
      exact tryReduceNatPredicate_exact hargA rfl hextractA
        hargB hextractB rfl hintern

/-- Every successful exact predicate-helper execution exposes a complete
callback/extraction/intern trace; there is no unclassified success path. -/
theorem complete
    {methods : Methods .anon} {addr : Address}
    {argA argB result : KExpr .anon} {s s' : TcState .anon}
    (hrun : (tryReduceNatPredicate addr #[argA, argB]).run methods s =
      .ok (some result) s') :
    NatPredicateSuccessTrace methods addr argA argB result s s' := by
  unfold tryReduceNatPredicate at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _ at hrun
  unfold EStateM.bind at hrun
  match hargA : (whnfNatReducerArg argA).run methods s with
  | .error err s₁ =>
      rw [hargA] at hrun
      contradiction
  | .ok first s₁ =>
      rw [hargA] at hrun
      cases first with
      | none =>
          simp only at hrun
          change EStateM.Result.ok none s₁ = .ok (some result) s' at hrun
          cases hrun
      | some argAResult =>
          simp only at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind (RecM.prims.run methods) _ s₁ = _ at hrun
          unfold EStateM.bind at hrun
          have hprims : RecM.prims.run methods s₁ = .ok s₁.prims s₁ := rfl
          rw [hprims] at hrun
          simp only at hrun
          match hextractA : extractNatLit argAResult s₁.prims with
          | none =>
              rw [hextractA] at hrun
              change EStateM.Result.ok none s₁ = .ok (some result) s' at hrun
              cases hrun
          | some a =>
              rw [hextractA] at hrun
              simp only at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ = _
                at hrun
              unfold EStateM.bind at hrun
              match hargB : (whnfNatReducerArg argB).run methods s₁ with
              | .error err s₂ =>
                  rw [hargB] at hrun
                  contradiction
              | .ok second s₂ =>
                  rw [hargB] at hrun
                  cases second with
                  | none =>
                      simp only at hrun
                      change EStateM.Result.ok none s₂ = .ok (some result) s'
                        at hrun
                      cases hrun
                  | some argBResult =>
                      simp only at hrun
                      match hextractB :
                          extractNatLit argBResult s₁.prims with
                      | none =>
                          rw [hextractB] at hrun
                          change EStateM.Result.ok none s₂ =
                            .ok (some result) s' at hrun
                          cases hrun
                      | some b =>
                          rw [hextractB] at hrun
                          simp only at hrun
                          rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
                          change EStateM.bind (TcM.intern _) _ s₂ = _ at hrun
                          unfold EStateM.bind at hrun
                          match hintern : TcM.intern
                              (KExpr.mkConst
                                (if (if addr == s₁.prims.natBeq.addr then
                                    a == b else a.ble b)
                                  then s₁.prims.boolTrue
                                  else s₁.prims.boolFalse) #[]) s₂ with
                          | .error err s₃ =>
                              rw [hintern] at hrun
                              contradiction
                          | .ok interned s₃ =>
                              rw [hintern] at hrun
                              simp [finishAppResult] at hrun
                              rcases hrun with ⟨rfl, rfl⟩
                              exact .intro hargA hextractA hargB hextractB
                                hintern

end NatPredicateSuccessTrace

/-- The callback, extraction, and pure-computation witnesses for a successful
exact binary arithmetic reduction.  The indices expose the only possible
result expression and final state. -/
inductive NatArithmeticSuccessTrace
    (methods : Methods .anon) (addr : Address)
    (argA argB : KExpr .anon) (s : TcState .anon) :
    KExpr .anon → TcState .anon → Prop
  | intro {s₁ s₂ : TcState .anon}
      {argAResult argBResult : KExpr .anon} {a b value : Nat}
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractA : extractNatLit argAResult s.prims = some a)
      (hextractB : extractNatLit argBResult s.prims = some b)
      (hcompute : computeNatBin addr PrimAddrs.canonical a b = some value) :
      NatArithmeticSuccessTrace methods addr argA argB s
        (natExprFromValue (m := .anon) value) s₂

/-- Successful production execution of an exact binary Nat application is
partitioned by the actual classifier results.  Predicate precedence is
recorded explicitly; canonical-state semantics later proves its address is
one of `Nat.beq` or `Nat.ble`. -/
inductive NatBinSuccessTrace
    (methods : Methods .anon) (natSuccMode : NatSuccMode)
    (headId : KId .anon) (us : Array (KUniv .anon))
    (argA argB : KExpr .anon)
    (headInfo firstInfo secondInfo : ExprInfo .anon)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop
  | arithmetic {result : KExpr .anon} {s' : TcState .anon}
      (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
      (body : NatArithmeticSuccessTrace methods headId.addr argA argB s
        result s') :
      NatBinSuccessTrace methods natSuccMode headId us argA argB
        headInfo firstInfo secondInfo s result s'
  | predicate {result : KExpr .anon} {s' : TcState .anon} {isArith : Bool}
      (harith : (isNatBinArithAddr headId.addr).run methods s =
        .ok isArith s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
      (body : NatPredicateSuccessTrace methods headId.addr argA argB
        result s s') :
      NatBinSuccessTrace methods natSuccMode headId us argA argB
        headInfo firstInfo secondInfo s result s'

namespace NatBinSuccessTrace

/-- Erase either success branch to the exact production dispatcher run. -/
theorem eval
    {methods : Methods .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB result : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {s s' : TcState .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (trace : NatBinSuccessTrace methods natSuccMode headId us argA argB
      headInfo firstInfo secondInfo s result s') :
    (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s =
      .ok (some result) s' := by
  cases trace with
  | arithmetic harith hpred body =>
      cases body with
      | intro hargA hargB hextractA hextractB hcompute =>
          exact tryReduceNatWithSuccMode_binArithExact hspine rfl
            harith hpred hargA hargB hextractA hextractB hcompute
  | predicate harith hpred body =>
      exact tryReduceNatWithSuccMode_binPredAnyExact hspine rfl harith hpred
        body.eval

/-- Invert an arbitrary successful exact-binary production run into one of
the two exhaustive success traces.  Every callback, extraction, computation,
and intern witness comes from evaluating the actual dispatcher. -/
theorem complete
    {methods : Methods .anon} {natSuccMode : NatSuccMode}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB result : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {s s' : TcState .anon}
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hrun : (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s =
      .ok (some result) s') :
    NatBinSuccessTrace methods natSuccMode headId us argA argB
      headInfo firstInfo secondInfo s result s' := by
  let isArith :=
    headId.addr == s.prims.natAdd.addr ||
      headId.addr == s.prims.natSub.addr ||
      headId.addr == s.prims.natMul.addr ||
      headId.addr == s.prims.natDiv.addr ||
      headId.addr == s.prims.natMod.addr ||
      headId.addr == s.prims.natPow.addr ||
      headId.addr == s.prims.natGcd.addr ||
      headId.addr == s.prims.natLand.addr ||
      headId.addr == s.prims.natLor.addr ||
      headId.addr == s.prims.natXor.addr ||
      headId.addr == s.prims.natShiftLeft.addr ||
      headId.addr == s.prims.natShiftRight.addr
  let isPred := headId.addr == s.prims.natBeq.addr ||
    headId.addr == s.prims.natBle.addr
  have harith : (isNatBinArithAddr headId.addr).run methods s =
      .ok isArith s := by
    exact isNatBinArithAddr_eval methods s headId.addr
  have hpred : (isNatBinPredAddr headId.addr).run methods s =
      .ok isPred s := by
    exact isNatBinPredAddr_eval methods s headId.addr
  unfold tryReduceNatWithSuccMode at hrun
  rw [hspine, ReaderT.run_bind] at hrun
  change EStateM.bind (RecM.prims.run methods) _ s = _ at hrun
  unfold EStateM.bind at hrun
  have hprims : RecM.prims.run methods s = .ok s.prims s := rfl
  rw [hprims] at hrun
  simp only at hrun
  have hnotSuccArity :
      ((#[argA, argB] : Array (KExpr .anon)).size == 1) = false := by
    simp
  rw [hnotSuccArity] at hrun
  simp only [Bool.and_false, Bool.false_eq_true, if_false] at hrun
  have hnotShort :
      ¬((#[argA, argB] : Array (KExpr .anon)).size < 2) := by
    simp
  rw [if_neg hnotShort] at hrun
  simp only [pure_bind] at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
    at hrun
  unfold EStateM.bind at hrun
  rw [harith] at hrun
  simp only at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
    at hrun
  unfold EStateM.bind at hrun
  rw [hpred] at hrun
  cases hisArith : isArith with
  | false =>
      cases hisPred : isPred with
      | false =>
          simp only [hisArith, hisPred, Bool.not_false,
            Bool.false_eq_true, if_false] at hrun
          change EStateM.Result.ok none s = .ok (some result) s' at hrun
          cases hrun
      | true =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok false s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok true s := by simpa [hisPred] using hpred
          have hhelper :
              (tryReduceNatPredicate headId.addr #[argA, argB]).run
                methods s = .ok (some result) s' := by
            simpa [hisArith, hisPred] using hrun
          exact .predicate harith' hpred'
            (NatPredicateSuccessTrace.complete hhelper)
  | true =>
      cases hisPred : isPred with
      | true =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok true s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok true s := by simpa [hisPred] using hpred
          have hhelper :
              (tryReduceNatPredicate headId.addr #[argA, argB]).run
                methods s = .ok (some result) s' := by
            simpa [hisArith, hisPred] using hrun
          exact .predicate harith' hpred'
            (NatPredicateSuccessTrace.complete hhelper)
      | false =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok true s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok false s := by simpa [hisPred] using hpred
          simp only [hisArith, hisPred, Bool.not_true, Bool.not_false,
            Bool.false_and, Bool.false_eq_true, if_false] at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
            at hrun
          unfold EStateM.bind at hrun
          match hargA : (whnfNatReducerArg argA).run methods s with
          | .error err s₁ =>
              rw [hargA] at hrun
              contradiction
          | .ok first s₁ =>
              rw [hargA] at hrun
              cases first with
              | none =>
                  change EStateM.Result.ok none s₁ = .ok (some result) s'
                    at hrun
                  cases hrun
              | some argAResult =>
                  simp only at hrun
                  rw [ReaderT.run_bind] at hrun
                  change EStateM.bind
                    ((whnfNatReducerArg argB).run methods) _ s₁ = _ at hrun
                  unfold EStateM.bind at hrun
                  match hargB : (whnfNatReducerArg argB).run methods s₁ with
                  | .error err s₂ =>
                      rw [hargB] at hrun
                      contradiction
                  | .ok second s₂ =>
                      rw [hargB] at hrun
                      cases second with
                      | none =>
                          change EStateM.Result.ok none s₂ =
                            .ok (some result) s' at hrun
                          cases hrun
                      | some argBResult =>
                          simp only at hrun
                          match hextractA :
                              extractNatLit argAResult s.prims with
                          | none =>
                              rw [hextractA] at hrun
                              change EStateM.Result.ok none s₂ =
                                .ok (some result) s' at hrun
                              cases hrun
                          | some a =>
                              rw [hextractA] at hrun
                              simp only at hrun
                              match hextractB :
                                  extractNatLit argBResult s.prims with
                              | none =>
                                  rw [hextractB] at hrun
                                  change EStateM.Result.ok none s₂ =
                                    .ok (some result) s' at hrun
                                  cases hrun
                              | some b =>
                                  rw [hextractB] at hrun
                                  simp only at hrun
                                  match hcompute : computeNatBin headId.addr
                                      PrimAddrs.canonical a b with
                                  | none =>
                                      rw [hcompute] at hrun
                                      change EStateM.Result.ok none s₂ =
                                        .ok (some result) s' at hrun
                                      cases hrun
                                  | some value =>
                                      rw [hcompute] at hrun
                                      simp [finishAppResult] at hrun
                                      rcases hrun with ⟨rfl, rfl⟩
                                      exact .arithmetic harith' hpred'
                                        (.intro hargA hargB hextractA
                                          hextractB hcompute)

end NatBinSuccessTrace

/-- Semantic/state acceptance for the exact binary arithmetic hit.  Both
recursive argument calls are checked through the strengthened callback
contract; the final generated-support fact comes from the execution-indexed
context field, and the Theory meaning is assembled from the canonical
primitive reflection proved above. -/
theorem tryReduceNatWithSuccMode_binArithExact_acceptance
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {sourceV : VExpr} {a b result : Nat}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s)
    (hsourceSupport : support
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult s.prims = some a)
    (hextractB : extractNatLit argBResult s.prims = some b)
    (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b =
      some result) :
    let source :=
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon)
    let reduced := natExprFromValue (m := .anon) result
    (tryReduceNatWithSuccMode source natSuccMode).run methods s =
        .ok (some reduced) s₂ ∧
      WhnfStateInv .noAccel semantics trProj world support uvars Δ s₂ ∧
      support reduced ∧
      WhnfMeaning trProj world uvars Δ source reduced := by
  dsimp only
  have hcatalog := hI.1.core.trustedCatalog
  have hΔ := hI.2.1.wf
  have hcanonical := hI.noAccel_primitives
  have htable := context.stateTable hI
  obtain ⟨harith, hpred⟩ := context.computeNatBin_classifiers hI hcompute
  obtain ⟨name, hname, hreflect⟩ :=
    context.computeNatBin_defeq hcatalog hcanonical hcompute
  obtain ⟨argAV, argBV, hsourceV, hargATr, hargBTr⟩ :=
    hsource.natBinExact_inv hΔ hname hreflect
  subst sourceV
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa using hinputSupport.2 0 (by simp)
  have hargBSupport : support argB := by
    simpa using hinputSupport.2 1 (by simp)
  have hargAPost :=
    whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
  rw [hargA] at hargAPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Δ s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Δ argAV argAResult at hargAPost
  have hargBPost :=
    whnfNatReducerArg_post_wf hargBSupport hargBTr methods hmethods
      hargAPost.1
  rw [hargB] at hargBPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Δ s₂ ∧
    support argBResult ∧
      WhnfPost trProj world uvars Δ argBV argBResult at hargBPost
  have hrun := tryReduceNatWithSuccMode_binArithExact
    (natSuccMode := natSuccMode) hspine rfl
    harith hpred hargA hargB hextractA hextractB hcompute
  have hresultSupport := context.generated.nat hsourceSupport hrun
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Δ
      (natExprFromValue (m := .anon) result) (.natLit result) :=
    TrKExprS.natExprFromValue hcatalog htable result
  have hmeaning := WhnfMeaning.natBinExact hΔ htable
    context.theoryPrimitives hsource hargAPost.2.2 hargBPost.2.2
    hextractA hextractB hreflect hresultTr
  exact ⟨hrun, hargBPost.1, hresultSupport, hmeaning⟩

/-- End-to-end arithmetic acceptance for a production spine with an arbitrary
trailing argument suffix.  The finite `FinishAppRequests` witness accounts
for every dynamically interned application node; `collectSpine` translation
inversion and application congruence transport the exact binary primitive
equation across that unchanged suffix. -/
theorem tryReduceNatWithSuccMode_binArithSuffix_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)}
    {argA argB argAResult argBResult final : KExpr .anon}
    {sourceV : VExpr} {a b result : Nat}
    (hrun : RunAssumptions initial program requests support)
    (theory : WhnfTheory trProj world uvars)
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractA : extractNatLit argAResult s.prims = some a)
    (hextractB : extractNatLit argBResult s.prims = some b)
    (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b =
      some result)
    (hfinish : FinishAppRequests requests
      (args.extract 2 args.size).toList
      (natExprFromValue (m := .anon) result) final) :
    ∃ s₃,
      (tryReduceNatWithSuccMode source natSuccMode).run methods s =
          .ok (some final) s₃ ∧
        WhnfStateInv .noAccel semantics trProj world support uvars Delta s₃ ∧
        support final ∧
        WhnfMeaning trProj world uvars Delta source final := by
  have hcatalog := hI.1.core.trustedCatalog
  have hDelta := hI.2.1.wf
  have hcanonical := hI.noAccel_primitives
  have htable := context.stateTable hI
  obtain ⟨harith, hpred⟩ := context.computeNatBin_classifiers hI hcompute
  obtain ⟨name, hname, hreflect⟩ :=
    context.computeNatBin_defeq hcatalog hcanonical hcompute
  have hspineTr := trAppSpine_of_collectSpine hsource hspine
  have hcanonicalSource :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN (.const headId us headInfo) args) sourceV := by
    rw [KExpr.mkAppN]
    simpa only [Array.foldl_toList] using hspineTr.tr
  have hcanonicalSuffix :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
          suffix) sourceV := by
    simpa [hargs, KExpr.mkAppN] using hcanonicalSource
  have hcanonicalSuffixList :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (suffix.toList.foldl KExpr.mkApp
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB))
        sourceV := by
    simpa only [KExpr.mkAppN, Array.foldl_toList] using hcanonicalSuffix
  obtain ⟨baseV, hbaseTr⟩ :=
    TrKExprS.foldlMkApp_initial (rest := suffix.toList)
      hcanonicalSuffixList
  have hbaseTrExact := hbaseTr
  rw [KExpr.mkApp_shape, KExpr.mkApp_shape] at hbaseTrExact
  obtain ⟨argAV, argBV, hbaseV, hargATr, hargBTr⟩ :=
    hbaseTrExact.natBinExact_inv hDelta hname hreflect
  subst baseV
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa [hargs] using hinputSupport.2 0 (by
      rw [hargs]
      grind)
  have hargBSupport : support argB := by
    simpa [hargs] using hinputSupport.2 1 (by
      rw [hargs]
      grind)
  have hargAPost :=
    whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
  rw [hargA] at hargAPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Delta argAV argAResult at hargAPost
  have hargBPost :=
    whnfNatReducerArg_post_wf hargBSupport hargBTr methods hmethods
      hargAPost.1
  rw [hargB] at hargBPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₂ ∧
    support argBResult ∧
      WhnfPost trProj world uvars Delta argBV argBResult at hargBPost
  obtain ⟨s₃, hfinishRun, hI₃, _⟩ := hfinish.eval hrun hargBPost.1
  have hactualRun := tryReduceNatWithSuccMode_binArithSuffixExact
    (natSuccMode := natSuccMode) hspine hargs rfl harith hpred hargA hargB
      hextractA hextractB hcompute hfinishRun
  have hresultSupport := context.generated.nat hsourceSupport hactualRun
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      (natExprFromValue (m := .anon) result) (.natLit result) :=
    TrKExprS.natExprFromValue hcatalog htable result
  have hbaseMeaningExact := WhnfMeaning.natBinExact hDelta htable
    context.theoryPrimitives hbaseTrExact hargAPost.2.2 hargBPost.2.2
    hextractA hextractB hreflect hresultTr
  have hbaseMeaning : WhnfMeaning trProj world uvars Delta
      (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
      (natExprFromValue (m := .anon) result) := by
    rw [KExpr.mkApp_shape, KExpr.mkApp_shape]
    exact hbaseMeaningExact
  have hcanonicalMeaning := WhnfMeaning.mkAppN theory hDelta
    hcanonicalSuffix hbaseMeaning
  have hsuffix : args.extract 2 args.size = suffix := by
    rw [hargs]
    grind
  have hfinal := hfinish.final_eq_spec
  rw [finishAppResultSpec, hsuffix] at hfinal
  subst final
  have hmeaning := WhnfMeaning.ofSharedSourceTranslation theory hDelta
    hsource hcanonicalSuffix hcanonicalMeaning
  exact ⟨s₃, hactualRun, hI₃, hresultSupport, hmeaning⟩

/-- End-to-end acceptance of an exact two-argument `Nat.beq` or `Nat.ble`
application.  The first callback precedes the primitive-table read exactly as
in production; the selected Bool node is then interned through the finite
collision/support boundary before the reflected predicate equation is
composed with both callback posts. -/
theorem tryReduceNatWithSuccMode_binPredExact_acceptance
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB argAResult argBResult : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {sourceV : VExpr} {a b : Nat}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s)
    (hsourceSupport : support
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (haddr : headId.addr = s.prims.natBeq.addr ∨
      headId.addr = s.prims.natBle.addr)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hextractA : extractNatLit argAResult s₁.prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractB : extractNatLit argBResult s₁.prims = some b) :
    let source :=
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon)
    let decision :=
      if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b
    let reduced := KExpr.mkConst
      (if decision then s₁.prims.boolTrue else s₁.prims.boolFalse) #[]
    ∃ s₃,
      (tryReduceNatWithSuccMode source natSuccMode).run methods s =
          .ok (some reduced) s₃ ∧
        WhnfStateInv .noAccel semantics trProj world support uvars Δ s₃ ∧
        support reduced ∧
        WhnfMeaning trProj world uvars Δ source reduced := by
  dsimp only
  have hcatalog := hI.1.core.trustedCatalog
  have hΔ := hI.2.1.wf
  let .app _ _ hprefixTr hargBTr := hsource
  let .app _ _ hheadTr hargATr := hprefixTr
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa using hinputSupport.2 0 (by simp)
  have hargBSupport : support argB := by
    simpa using hinputSupport.2 1 (by simp)
  have hargAPost :=
    whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
  rw [hargA] at hargAPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Δ s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Δ _ argAResult at hargAPost
  have hcanonical₀ := hI.noAccel_primitives
  have hcanonical₁ := hargAPost.1.noAccel_primitives
  have hbeq₀ : s.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBeq hcanonical₀
  have hble₀ : s.prims.natBle.addr = PrimAddrs.canonical.natBle := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBle hcanonical₀
  have hbeq₁ : s₁.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBeq hcanonical₁
  have hble₁ : s₁.prims.natBle.addr = PrimAddrs.canonical.natBle := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBle hcanonical₁
  have haddr₁ : headId.addr = s₁.prims.natBeq.addr ∨
      headId.addr = s₁.prims.natBle.addr := by
    rcases haddr with hbeq | hble
    · exact .inl (hbeq.trans (hbeq₀.trans hbeq₁.symm))
    · exact .inr (hble.trans (hble₀.trans hble₁.symm))
  obtain ⟨harith, hpred⟩ := context.natPredicate_classifiers hI haddr
  obtain ⟨name, decision, hname, hdecision, hreflect⟩ :=
    context.natPredicate_defeq hcatalog hcanonical₁ haddr₁
  subst decision
  obtain ⟨argAV, argBV, hsourceV, hargATrExact, hargBTrExact⟩ :=
    hsource.natBinExact_inv hΔ hname hreflect
  subst sourceV
  have hargAPostExact :=
    whnfNatReducerArg_post_wf hargASupport hargATrExact methods hmethods hI
  rw [hargA] at hargAPostExact
  change WhnfStateInv .noAccel semantics trProj world support uvars Δ s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Δ argAV argAResult at hargAPostExact
  have hargBPost :=
    whnfNatReducerArg_post_wf hargBSupport hargBTrExact methods hmethods
      hargAPostExact.1
  rw [hargB] at hargBPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Δ s₂ ∧
    support argBResult ∧
      WhnfPost trProj world uvars Δ _ argBResult at hargBPost
  let reduced := KExpr.mkConst
    (if (if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b)
      then s₁.prims.boolTrue else s₁.prims.boolFalse) #[]
  have hreducedSupport : support reduced := by
    exact context.generated.boolConst hcanonical₁ _
  obtain ⟨s₃, hintern, hI₃, _⟩ :=
    TcM.intern_whnf_eval context.collisionFree hreducedSupport hargBPost.1
  have hhelper := tryReduceNatPredicate_exact
    (prims := s₁.prims) (addr := headId.addr)
    hargA rfl hextractA hargB hextractB rfl hintern
  have hrun := tryReduceNatWithSuccMode_binPredExact
    (natSuccMode := natSuccMode) hspine rfl harith hpred hhelper
  have htable := context.stateTable hargAPostExact.1
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Δ reduced
      (.boolLit
        (if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b)) :=
    TrKExprS.boolExprFromDecision hcatalog htable
      context.theoryPrimitives _
  have hmeaning := WhnfMeaning.natBinExact hΔ htable
    context.theoryPrimitives hsource hargAPostExact.2.2 hargBPost.2.2
    hextractA hextractB hreflect hresultTr
  exact ⟨s₃, hrun, hI₃, hreducedSupport, hmeaning⟩

/-- End-to-end predicate acceptance for a binary Nat application with an
arbitrary trailing suffix.  The selected Bool constant is interned first;
the finite suffix certificate then accounts for every rebuilt application.
Both phases preserve the checker invariant, and unchanged-argument
congruence transports the reflected predicate equation to the final spine. -/
theorem tryReduceNatWithSuccMode_binPredSuffix_acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)}
    {argA argB argAResult argBResult final : KExpr .anon}
    {sourceV : VExpr} {a b : Nat}
    (hrun : RunAssumptions initial program requests support)
    (theory : WhnfTheory trProj world uvars)
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (haddr : headId.addr = s.prims.natBeq.addr ∨
      headId.addr = s.prims.natBle.addr)
    (hargA : (whnfNatReducerArg argA).run methods s =
      .ok (some argAResult) s₁)
    (hextractA : extractNatLit argAResult s₁.prims = some a)
    (hargB : (whnfNatReducerArg argB).run methods s₁ =
      .ok (some argBResult) s₂)
    (hextractB : extractNatLit argBResult s₁.prims = some b)
    (hfinish : FinishAppRequests requests
      (args.extract 2 args.size).toList
      (KExpr.mkConst
        (if (if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b)
          then s₁.prims.boolTrue else s₁.prims.boolFalse) #[])
      final) :
    ∃ s₄,
      (tryReduceNatWithSuccMode source natSuccMode).run methods s =
          .ok (some final) s₄ ∧
        WhnfStateInv .noAccel semantics trProj world support uvars Delta s₄ ∧
        support final ∧
        WhnfMeaning trProj world uvars Delta source final := by
  have hcatalog := hI.1.core.trustedCatalog
  have hDelta := hI.2.1.wf
  have hspineTr := trAppSpine_of_collectSpine hsource hspine
  have hcanonicalSource :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN (.const headId us headInfo) args) sourceV := by
    rw [KExpr.mkAppN]
    simpa only [Array.foldl_toList] using hspineTr.tr
  have hcanonicalSuffix :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
          suffix) sourceV := by
    simpa [hargs, KExpr.mkAppN] using hcanonicalSource
  have hcanonicalSuffixList :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (suffix.toList.foldl KExpr.mkApp
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB))
        sourceV := by
    simpa only [KExpr.mkAppN, Array.foldl_toList] using hcanonicalSuffix
  obtain ⟨baseV, hbaseTr⟩ :=
    TrKExprS.foldlMkApp_initial (rest := suffix.toList)
      hcanonicalSuffixList
  have hbaseTrExact := hbaseTr
  rw [KExpr.mkApp_shape, KExpr.mkApp_shape] at hbaseTrExact
  let .app _ _ hprefixTr hargBTr := hbaseTrExact
  let .app _ _ _ hargATr := hprefixTr
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa [hargs] using hinputSupport.2 0 (by
      rw [hargs]
      grind)
  have hargBSupport : support argB := by
    simpa [hargs] using hinputSupport.2 1 (by
      rw [hargs]
      grind)
  have hargAPost :=
    whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
  rw [hargA] at hargAPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Delta _ argAResult at hargAPost
  have hcanonical₀ := hI.noAccel_primitives
  have hcanonical₁ := hargAPost.1.noAccel_primitives
  have hbeq₀ : s.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBeq hcanonical₀
  have hble₀ : s.prims.natBle.addr = PrimAddrs.canonical.natBle := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBle hcanonical₀
  have hbeq₁ : s₁.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBeq hcanonical₁
  have hble₁ : s₁.prims.natBle.addr = PrimAddrs.canonical.natBle := by
    simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
      congrArg PrimAddrs.natBle hcanonical₁
  have haddr₁ : headId.addr = s₁.prims.natBeq.addr ∨
      headId.addr = s₁.prims.natBle.addr := by
    rcases haddr with hbeq | hble
    · exact .inl (hbeq.trans (hbeq₀.trans hbeq₁.symm))
    · exact .inr (hble.trans (hble₀.trans hble₁.symm))
  obtain ⟨harith, hpred⟩ := context.natPredicate_classifiers hI haddr
  obtain ⟨name, decision, hname, hdecision, hreflect⟩ :=
    context.natPredicate_defeq hcatalog hcanonical₁ haddr₁
  subst decision
  obtain ⟨argAV, argBV, hbaseV, hargATrExact, hargBTrExact⟩ :=
    hbaseTrExact.natBinExact_inv hDelta hname hreflect
  subst baseV
  have hargAPostExact :=
    whnfNatReducerArg_post_wf hargASupport hargATrExact methods hmethods hI
  rw [hargA] at hargAPostExact
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
    support argAResult ∧
      WhnfPost trProj world uvars Delta argAV argAResult at hargAPostExact
  have hargBPost :=
    whnfNatReducerArg_post_wf hargBSupport hargBTrExact methods hmethods
      hargAPostExact.1
  rw [hargB] at hargBPost
  change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₂ ∧
    support argBResult ∧
      WhnfPost trProj world uvars Delta argBV argBResult at hargBPost
  let decision :=
    if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b
  let reduced := KExpr.mkConst
    (if decision then s₁.prims.boolTrue else s₁.prims.boolFalse) #[]
  have hreducedSupport : support reduced := by
    exact context.generated.boolConst hcanonical₁ _
  obtain ⟨s₃, hintern, hI₃, _⟩ :=
    TcM.intern_whnf_eval context.collisionFree hreducedSupport hargBPost.1
  change FinishAppRequests requests
    (args.extract 2 args.size).toList reduced final at hfinish
  obtain ⟨s₄, hfinishRun, hI₄, _⟩ := hfinish.eval hrun hI₃
  have hhelper := tryReduceNatPredicate_suffixExact
    (prims := s₁.prims) (addr := headId.addr)
    (decision := decision) (base := reduced) hargs hargA rfl hextractA
      hargB hextractB rfl rfl hintern hfinishRun
  have hactualRun := tryReduceNatWithSuccMode_binPredSuffixExact
    (natSuccMode := natSuccMode) hspine hargs rfl harith hpred hhelper
  have hresultSupport := context.generated.nat hsourceSupport hactualRun
  have htable := context.stateTable hargAPostExact.1
  have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta reduced
      (.boolLit decision) :=
    TrKExprS.boolExprFromDecision hcatalog htable
      context.theoryPrimitives _
  have hbaseMeaningExact := WhnfMeaning.natBinExact hDelta htable
    context.theoryPrimitives hbaseTrExact hargAPostExact.2.2 hargBPost.2.2
    hextractA hextractB hreflect hresultTr
  have hbaseMeaning : WhnfMeaning trProj world uvars Delta
      (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
      reduced := by
    rw [KExpr.mkApp_shape, KExpr.mkApp_shape]
    exact hbaseMeaningExact
  have hcanonicalMeaning := WhnfMeaning.mkAppN theory hDelta
    hcanonicalSuffix hbaseMeaning
  have hsuffix : args.extract 2 args.size = suffix := by
    rw [hargs]
    grind
  have hfinal := hfinish.final_eq_spec
  rw [finishAppResultSpec, hsuffix] at hfinal
  subst final
  have hmeaning := WhnfMeaning.ofSharedSourceTranslation theory hDelta
    hsource hcanonicalSuffix hcanonicalMeaning
  exact ⟨s₄, hactualRun, hI₄, hresultSupport, hmeaning⟩

/-- Exhaustive operational witness for a successful predicate helper on a
general application spine.  Unlike the exact-binary trace, it records both
the expression returned by Bool interning and the subsequent suffix rebuild. -/
inductive NatPredicateSuffixSuccessTrace
    (methods : Methods .anon) (addr : Address)
    (args : Array (KExpr .anon)) (argA argB : KExpr .anon)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop
  | intro {s₁ s₂ s₃ s₄ : TcState .anon}
      {argAResult argBResult requested base final : KExpr .anon}
      {a b : Nat}
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hextractA : extractNatLit argAResult s₁.prims = some a)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractB : extractNatLit argBResult s₁.prims = some b)
      (hrequested : requested = KExpr.mkConst
        (if (if addr == s₁.prims.natBeq.addr then a == b else a.ble b)
          then s₁.prims.boolTrue else s₁.prims.boolFalse) #[])
      (hintern : TcM.intern requested s₂ = .ok base s₃)
      (hfinish : (finishAppResult base args 2).run methods s₃ =
        .ok final s₄) :
      NatPredicateSuffixSuccessTrace methods addr args argA argB s final s₄

namespace NatPredicateSuffixSuccessTrace

/-- Erase a general predicate trace to the exact production helper run. -/
theorem eval
    {methods : Methods .anon} {addr : Address}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {s s' : TcState .anon}
    (hargs : args = #[argA, argB] ++ suffix)
    (trace : NatPredicateSuffixSuccessTrace methods addr args argA argB
      s result s') :
    (tryReduceNatPredicate addr args).run methods s =
      .ok (some result) s' := by
  cases trace with
  | intro hargA hextractA hargB hextractB hrequested hintern hfinish =>
      exact tryReduceNatPredicate_suffixExact
        (prims := _) (decision := _) hargs hargA rfl hextractA hargB
          hextractB rfl hrequested hintern hfinish

/-- Every successful general predicate-helper execution exposes its complete
callback, extraction, Bool-intern, and suffix-rebuild trace. -/
theorem complete
    {methods : Methods .anon} {addr : Address}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {s s' : TcState .anon}
    (hargs : args = #[argA, argB] ++ suffix)
    (hrun : (tryReduceNatPredicate addr args).run methods s =
      .ok (some result) s') :
    NatPredicateSuffixSuccessTrace methods addr args argA argB
      s result s' := by
  have hzero : args[0]! = argA := by
    rw [hargs]
    grind
  have hone : args[1]! = argB := by
    rw [hargs]
    grind
  unfold tryReduceNatPredicate at hrun
  rw [hzero, hone, ReaderT.run_bind] at hrun
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _ at hrun
  unfold EStateM.bind at hrun
  match hargA : (whnfNatReducerArg argA).run methods s with
  | .error err s₁ =>
      rw [hargA] at hrun
      contradiction
  | .ok first s₁ =>
      rw [hargA] at hrun
      cases first with
      | none =>
          simp only at hrun
          change EStateM.Result.ok none s₁ = .ok (some result) s' at hrun
          cases hrun
      | some argAResult =>
          simp only at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind (RecM.prims.run methods) _ s₁ = _ at hrun
          unfold EStateM.bind at hrun
          have hprims : RecM.prims.run methods s₁ = .ok s₁.prims s₁ := rfl
          rw [hprims] at hrun
          simp only at hrun
          match hextractA : extractNatLit argAResult s₁.prims with
          | none =>
              rw [hextractA] at hrun
              change EStateM.Result.ok none s₁ = .ok (some result) s'
                at hrun
              cases hrun
          | some a =>
              rw [hextractA] at hrun
              simp only at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind
                ((whnfNatReducerArg argB).run methods) _ s₁ = _ at hrun
              unfold EStateM.bind at hrun
              match hargB : (whnfNatReducerArg argB).run methods s₁ with
              | .error err s₂ =>
                  rw [hargB] at hrun
                  contradiction
              | .ok second s₂ =>
                  rw [hargB] at hrun
                  cases second with
                  | none =>
                      simp only at hrun
                      change EStateM.Result.ok none s₂ =
                        .ok (some result) s' at hrun
                      cases hrun
                  | some argBResult =>
                      simp only at hrun
                      match hextractB :
                          extractNatLit argBResult s₁.prims with
                      | none =>
                          rw [hextractB] at hrun
                          change EStateM.Result.ok none s₂ =
                            .ok (some result) s' at hrun
                          cases hrun
                      | some b =>
                          rw [hextractB] at hrun
                          simp only at hrun
                          rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
                          change EStateM.bind (TcM.intern _) _ s₂ = _ at hrun
                          unfold EStateM.bind at hrun
                          let requested := KExpr.mkConst
                            (if (if addr == s₁.prims.natBeq.addr then
                                a == b else a.ble b)
                              then s₁.prims.boolTrue
                              else s₁.prims.boolFalse) #[]
                          match hintern : TcM.intern requested s₂ with
                          | .error err s₃ =>
                              rw [hintern] at hrun
                              contradiction
                          | .ok base s₃ =>
                              rw [hintern] at hrun
                              simp only at hrun
                              rw [ReaderT.run_bind] at hrun
                              change EStateM.bind
                                ((finishAppResult base args 2).run methods) _ s₃ = _
                                at hrun
                              unfold EStateM.bind at hrun
                              match hfinish :
                                  (finishAppResult base args 2).run methods s₃ with
                              | .error err s₄ =>
                                  rw [hfinish] at hrun
                                  contradiction
                              | .ok final s₄ =>
                                  rw [hfinish] at hrun
                                  simp only at hrun
                                  rcases hrun with ⟨rfl, rfl⟩
                                  exact .intro hargA hextractA hargB hextractB
                                    rfl hintern hfinish

end NatPredicateSuffixSuccessTrace

/-- Callback, extraction, computation, and suffix-rebuild witnesses for a
successful arithmetic branch on a general application spine. -/
inductive NatArithmeticSuffixSuccessTrace
    (methods : Methods .anon) (addr : Address)
    (args : Array (KExpr .anon)) (argA argB : KExpr .anon)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop
  | intro {s₁ s₂ s₃ : TcState .anon}
      {argAResult argBResult final : KExpr .anon} {a b value : Nat}
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractA : extractNatLit argAResult s.prims = some a)
      (hextractB : extractNatLit argBResult s.prims = some b)
      (hcompute : computeNatBin addr PrimAddrs.canonical a b = some value)
      (hfinish :
        (finishAppResult (natExprFromValue (m := .anon) value) args 2).run
          methods s₂ = .ok final s₃) :
      NatArithmeticSuffixSuccessTrace methods addr args argA argB s final s₃

/-- Every successful production run on a spine with at least two arguments
is partitioned by the actual classifier results.  The trace retains the
entire suffix-rebuild run instead of collapsing it to the exact-binary case. -/
inductive NatSpineSuccessTrace
    (methods : Methods .anon) (natSuccMode : NatSuccMode)
    (source : KExpr .anon) (headId : KId .anon)
    (us : Array (KUniv .anon)) (headInfo : ExprInfo .anon)
    (args : Array (KExpr .anon)) (argA argB : KExpr .anon)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop
  | arithmetic {result : KExpr .anon} {s' : TcState .anon}
      (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
      (body : NatArithmeticSuffixSuccessTrace methods headId.addr args
        argA argB s result s') :
      NatSpineSuccessTrace methods natSuccMode source headId us headInfo
        args argA argB s result s'
  | predicate {result : KExpr .anon} {s' : TcState .anon}
      {isArith : Bool}
      (harith : (isNatBinArithAddr headId.addr).run methods s =
        .ok isArith s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
      (body : NatPredicateSuffixSuccessTrace methods headId.addr args
        argA argB s result s') :
      NatSpineSuccessTrace methods natSuccMode source headId us headInfo
        args argA argB s result s'

namespace NatSpineSuccessTrace

/-- Erase either general-spine success trace to the production dispatcher. -/
theorem eval
    {methods : Methods .anon} {natSuccMode : NatSuccMode}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {s s' : TcState .anon}
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (trace : NatSpineSuccessTrace methods natSuccMode source headId us
      headInfo args argA argB s result s') :
    (tryReduceNatWithSuccMode source natSuccMode).run methods s =
      .ok (some result) s' := by
  cases trace with
  | arithmetic harith hpred body =>
      cases body with
      | intro hargA hargB hextractA hextractB hcompute hfinish =>
          exact tryReduceNatWithSuccMode_binArithSuffixExact hspine hargs rfl
            harith hpred hargA hargB hextractA hextractB hcompute hfinish
  | predicate harith hpred body =>
      exact tryReduceNatWithSuccMode_binPredSuffixExact hspine hargs rfl
        harith hpred (body.eval hargs)

/-- Invert an arbitrary successful general-spine production run.  All
callback, extraction, computation, Bool-intern, and suffix-rebuild equations
come from evaluating the actual dispatcher. -/
theorem complete
    {methods : Methods .anon} {natSuccMode : NatSuccMode}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {s s' : TcState .anon}
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hrun : (tryReduceNatWithSuccMode source natSuccMode).run methods s =
      .ok (some result) s') :
    NatSpineSuccessTrace methods natSuccMode source headId us headInfo
      args argA argB s result s' := by
  let isArith :=
    headId.addr == s.prims.natAdd.addr ||
      headId.addr == s.prims.natSub.addr ||
      headId.addr == s.prims.natMul.addr ||
      headId.addr == s.prims.natDiv.addr ||
      headId.addr == s.prims.natMod.addr ||
      headId.addr == s.prims.natPow.addr ||
      headId.addr == s.prims.natGcd.addr ||
      headId.addr == s.prims.natLand.addr ||
      headId.addr == s.prims.natLor.addr ||
      headId.addr == s.prims.natXor.addr ||
      headId.addr == s.prims.natShiftLeft.addr ||
      headId.addr == s.prims.natShiftRight.addr
  let isPred := headId.addr == s.prims.natBeq.addr ||
    headId.addr == s.prims.natBle.addr
  have harith : (isNatBinArithAddr headId.addr).run methods s =
      .ok isArith s := isNatBinArithAddr_eval methods s headId.addr
  have hpred : (isNatBinPredAddr headId.addr).run methods s =
      .ok isPred s := isNatBinPredAddr_eval methods s headId.addr
  have hzero : args[0]! = argA := by
    rw [hargs]
    grind
  have hone : args[1]! = argB := by
    rw [hargs]
    grind
  unfold tryReduceNatWithSuccMode at hrun
  rw [hspine, ReaderT.run_bind] at hrun
  change EStateM.bind (RecM.prims.run methods) _ s = _ at hrun
  unfold EStateM.bind at hrun
  have hprims : RecM.prims.run methods s = .ok s.prims s := rfl
  rw [hprims] at hrun
  simp only at hrun
  have hnotSuccArity : (args.size == 1) = false := by
    rw [hargs]
    grind
  rw [hnotSuccArity] at hrun
  simp only [Bool.and_false, Bool.false_eq_true, if_false] at hrun
  have hnotShort : ¬(args.size < 2) := by
    rw [hargs]
    grind
  rw [if_neg hnotShort] at hrun
  simp only [pure_bind] at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s = _
    at hrun
  unfold EStateM.bind at hrun
  rw [harith] at hrun
  simp only at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s = _
    at hrun
  unfold EStateM.bind at hrun
  rw [hpred] at hrun
  cases hisArith : isArith with
  | false =>
      cases hisPred : isPred with
      | false =>
          simp only [hisArith, hisPred, Bool.not_false,
            Bool.false_eq_true, if_false] at hrun
          change EStateM.Result.ok none s = .ok (some result) s' at hrun
          cases hrun
      | true =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok false s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok true s := by simpa [hisPred] using hpred
          have hhelper : (tryReduceNatPredicate headId.addr args).run
              methods s = .ok (some result) s' := by
            simpa [hisArith, hisPred] using hrun
          exact .predicate harith' hpred'
            (NatPredicateSuffixSuccessTrace.complete hargs hhelper)
  | true =>
      cases hisPred : isPred with
      | true =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok true s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok true s := by simpa [hisPred] using hpred
          have hhelper : (tryReduceNatPredicate headId.addr args).run
              methods s = .ok (some result) s' := by
            simpa [hisArith, hisPred] using hrun
          exact .predicate harith' hpred'
            (NatPredicateSuffixSuccessTrace.complete hargs hhelper)
      | false =>
          have harith' : (isNatBinArithAddr headId.addr).run methods s =
              .ok true s := by simpa [hisArith] using harith
          have hpred' : (isNatBinPredAddr headId.addr).run methods s =
              .ok false s := by simpa [hisPred] using hpred
          simp only [hisArith, hisPred, Bool.not_true, Bool.not_false,
            Bool.false_and, Bool.false_eq_true, if_false] at hrun
          rw [hzero] at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = _
            at hrun
          unfold EStateM.bind at hrun
          match hargA : (whnfNatReducerArg argA).run methods s with
          | .error err s₁ =>
              rw [hargA] at hrun
              contradiction
          | .ok first s₁ =>
              rw [hargA] at hrun
              cases first with
              | none =>
                  change EStateM.Result.ok none s₁ = .ok (some result) s'
                    at hrun
                  cases hrun
              | some argAResult =>
                  simp only at hrun
                  rw [hone] at hrun
                  rw [ReaderT.run_bind] at hrun
                  change EStateM.bind
                    ((whnfNatReducerArg argB).run methods) _ s₁ = _ at hrun
                  unfold EStateM.bind at hrun
                  match hargB : (whnfNatReducerArg argB).run methods s₁ with
                  | .error err s₂ =>
                      rw [hargB] at hrun
                      contradiction
                  | .ok second s₂ =>
                      rw [hargB] at hrun
                      cases second with
                      | none =>
                          change EStateM.Result.ok none s₂ =
                            .ok (some result) s' at hrun
                          cases hrun
                      | some argBResult =>
                          simp only at hrun
                          match hextractA :
                              extractNatLit argAResult s.prims with
                          | none =>
                              rw [hextractA] at hrun
                              change EStateM.Result.ok none s₂ =
                                .ok (some result) s' at hrun
                              cases hrun
                          | some a =>
                              rw [hextractA] at hrun
                              simp only at hrun
                              match hextractB :
                                  extractNatLit argBResult s.prims with
                              | none =>
                                  rw [hextractB] at hrun
                                  change EStateM.Result.ok none s₂ =
                                    .ok (some result) s' at hrun
                                  cases hrun
                              | some b =>
                                  rw [hextractB] at hrun
                                  simp only at hrun
                                  match hcompute : computeNatBin headId.addr
                                      PrimAddrs.canonical a b with
                                  | none =>
                                      rw [hcompute] at hrun
                                      change EStateM.Result.ok none s₂ =
                                        .ok (some result) s' at hrun
                                      cases hrun
                                  | some value =>
                                      rw [hcompute] at hrun
                                      simp only [if_true] at hrun
                                      rw [ReaderT.run_bind] at hrun
                                      change EStateM.bind
                                        ((finishAppResult
                                          (natExprFromValue value) args 2).run
                                            methods) _ s₂ = _ at hrun
                                      unfold EStateM.bind at hrun
                                      match hfinish :
                                          (finishAppResult
                                            (natExprFromValue value) args 2).run
                                              methods s₂ with
                                      | .error err s₃ =>
                                          rw [hfinish] at hrun
                                          contradiction
                                      | .ok final s₃ =>
                                          rw [hfinish] at hrun
                                          simp only at hrun
                                          rcases hrun with ⟨rfl, rfl⟩
                                          exact .arithmetic harith' hpred'
                                            (.intro hargA hargB hextractA
                                              hextractB hcompute hfinish)

end NatSpineSuccessTrace

namespace NatBinSuccessTrace

/-- Interpret either operational success trace in the fixed Theory world.
For predicates, determinism identifies the trace's concrete intern result
with the collision-safe canonical Bool result constructed by the semantic
acceptance theorem. -/
theorem acceptance
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB result : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon}
    {sourceV : VExpr} {s s' : TcState .anon}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Δ s)
    (hsourceSupport : support
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB]))
    (trace : NatBinSuccessTrace methods natSuccMode headId us argA argB
      headInfo firstInfo secondInfo s result s') :
    WhnfStateInv .noAccel semantics trProj world support uvars Δ s' ∧
      support result ∧
      WhnfMeaning trProj world uvars Δ
        (.app (.app (.const headId us headInfo) argA firstInfo)
          argB secondInfo) result := by
  cases trace with
  | arithmetic harith hpred body =>
      cases body with
      | intro hargA hargB hextractA hextractB hcompute =>
          have haccept := tryReduceNatWithSuccMode_binArithExact_acceptance
            context hmethods hI hsourceSupport hsource hspine hargA hargB
              hextractA hextractB hcompute
          exact ⟨haccept.2.1, haccept.2.2.1, haccept.2.2.2⟩
  | predicate harith hpred body =>
      cases body with
      | intro hargA hextractA hargB hextractB hintern =>
          have haddr := isNatBinPredAddr_true hpred
          obtain ⟨s₃, hcanonicalRun, hI₃, hresultSupport, hmeaning⟩ :=
            tryReduceNatWithSuccMode_binPredExact_acceptance context
              hmethods hI hsourceSupport hsource hspine haddr hargA
              hextractA hargB hextractB
          have hhelper := tryReduceNatPredicate_exact
            (prims := _ ) (addr := headId.addr) hargA rfl hextractA
              hargB hextractB rfl hintern
          have hactualRun := tryReduceNatWithSuccMode_binPredAnyExact
            (natSuccMode := natSuccMode) hspine rfl harith hpred hhelper
          have heq := hactualRun.symm.trans hcanonicalRun
          have hresultEq := Option.some.inj (EStateM.Result.ok.inj heq).1
          have hstateEq : s' = s₃ := (EStateM.Result.ok.inj heq).2
          subst result
          subst s'
          exact ⟨hI₃, hresultSupport, hmeaning⟩

end NatBinSuccessTrace

/-- Exact-binary `OptionalReduction.WF` slice for the production Nat
dispatcher.  Misses and errors use the exhaustive state-invariant theorem;
every hit is inverted into an exact binary success trace and interpreted
semantically. -/
theorem tryReduceNatWithSuccMode_bin_optional_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {argA argB : KExpr .anon}
    {headInfo firstInfo secondInfo : ExprInfo .anon} {sourceV : VExpr}
    (hsourceSupport : support
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo))
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Δ
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) sourceV)
    (hspine :
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo : KExpr .anon).collectSpine =
      (.const headId us headInfo, #[argA, argB])) :
    RecM.WF .noAccel semantics trProj world support uvars Δ s
      (tryReduceNatWithSuccMode
        (.app (.app (.const headId us headInfo) argA firstInfo)
          argB secondInfo) natSuccMode)
      (fun outcome _ => match outcome with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Δ
                (.app (.app (.const headId us headInfo) argA firstInfo)
                  argB secondInfo) reduced) := by
  intro methods hmethods hI
  have hinv := tryReduceNatWithSuccMode_bin_inv_wf context
    hsourceSupport hsource hspine methods hmethods hI
  match hrun : (tryReduceNatWithSuccMode
      (.app (.app (.const headId us headInfo) argA firstInfo)
        argB secondInfo) natSuccMode).run methods s with
  | .error err s' =>
      rw [hrun] at hinv
      simp only at hinv ⊢
      exact hinv
  | .ok outcome s' =>
      rw [hrun] at hinv
      cases outcome with
      | none =>
          simp only at hinv ⊢
          exact hinv
      | some result =>
          simp only at hinv ⊢
          have trace := NatBinSuccessTrace.complete hspine hrun
          have haccept := trace.acceptance context hmethods hI
            hsourceSupport hsource hspine
          exact ⟨haccept.1, haccept.2⟩

/-! ### General-spine Nat state and finite-success closure -/

/-- Recover finite support and structural translations for the two consumed
Nat arguments from an arbitrary translated application spine.  The proof
peels the unchanged suffix from the canonical spine rather than assuming
that the original application metadata was canonical. -/
theorem natBinSpine_inputs
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB : KExpr .anon}
    {sourceV : VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix) :
    ∃ argAV argBV,
      support argA ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta argA argAV ∧
      support argB ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta argB argBV := by
  have hspineTr := trAppSpine_of_collectSpine hsource hspine
  have hcanonicalSource :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN (.const headId us headInfo) args) sourceV := by
    rw [KExpr.mkAppN]
    simpa only [Array.foldl_toList] using hspineTr.tr
  have hcanonicalSuffix :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (KExpr.mkAppN
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
          suffix) sourceV := by
    simpa [hargs, KExpr.mkAppN] using hcanonicalSource
  have hcanonicalSuffixList :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (suffix.toList.foldl KExpr.mkApp
          (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB))
        sourceV := by
    simpa only [KExpr.mkAppN, Array.foldl_toList] using hcanonicalSuffix
  obtain ⟨baseV, hbaseTr⟩ :=
    TrKExprS.foldlMkApp_initial (rest := suffix.toList)
      hcanonicalSuffixList
  rw [KExpr.mkApp_shape, KExpr.mkApp_shape] at hbaseTr
  let .app _ _ hprefixTr hargBTr := hbaseTr
  let .app _ _ _ hargATr := hprefixTr
  have hinputSupport := context.inputs.spine hsourceSupport hspine
  have hargASupport : support argA := by
    simpa [hargs] using hinputSupport.2 0 (by
      rw [hargs]
      grind)
  have hargBSupport : support argB := by
    simpa [hargs] using hinputSupport.2 1 (by
      rw [hargs]
      grind)
  exact ⟨_, _, hargASupport, hargATr, hargBSupport, hargBTr⟩

/-- Postcondition used by the general-spine miss/error partition.  Primitive
hits are intentionally vacuous here: the operational-trace and certified-
success layers interpret them separately from finite suffix certificates. -/
def NatSpineNonHitInv
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (Delta : KVLCtx)
    (outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))) : Prop :=
  match outcome with
  | .error _ s' =>
      WhnfStateInv .noAccel semantics trProj world support uvars Delta s'
  | .ok none s' =>
      WhnfStateInv .noAccel semantics trProj world support uvars Delta s'
  | .ok (some _) _ => True

/-- Exhaustive miss/error invariant for the general predicate helper.  Once
both literals are recognized, direct Bool interning and suffix rebuilding are
operationally total, so every remaining execution is a hit. -/
theorem tryReduceNatPredicate_spine_nonhit_inv
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {addr : Address}
    {args suffix : Array (KExpr .anon)} {argA argB : KExpr .anon}
    {argAV argBV : VExpr}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hargASupport : support argA)
    (hargATr : TrKExprS world.venv uvars world.nameOf trProj Delta argA argAV)
    (hargBSupport : support argB)
    (hargBTr : TrKExprS world.venv uvars world.nameOf trProj Delta argB argBV)
    (hargs : args = #[argA, argB] ++ suffix)
    (hrun : (tryReduceNatPredicate addr args).run methods s = outcome) :
    NatSpineNonHitInv semantics trProj world support uvars Delta outcome := by
  have hzero : args[0]! = argA := by rw [hargs]; grind
  have hone : args[1]! = argB := by rw [hargs]; grind
  unfold tryReduceNatPredicate at hrun
  rw [hzero, ReaderT.run_bind] at hrun
  change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = outcome
    at hrun
  unfold EStateM.bind at hrun
  match hargA : (whnfNatReducerArg argA).run methods s with
  | .error err s₁ =>
      rw [hargA] at hrun
      rw [← hrun]
      exact whnfNatReducerArg_error_inv hargASupport hargATr hmethods hI hargA
  | .ok first s₁ =>
      rw [hargA] at hrun
      have hI₁ := whnfNatReducerArg_ok_inv hargASupport hargATr
        hmethods hI hargA
      cases first with
      | none =>
          simp only at hrun
          rw [← hrun]
          exact hI₁
      | some argAResult =>
          simp only at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind (RecM.prims.run methods) _ s₁ = outcome at hrun
          unfold EStateM.bind at hrun
          have hprims₁ : RecM.prims.run methods s₁ = .ok s₁.prims s₁ := rfl
          rw [hprims₁] at hrun
          simp only at hrun
          match hextractA : extractNatLit argAResult s₁.prims with
          | none =>
              rw [hextractA] at hrun
              rw [← hrun]
              exact hI₁
          | some a =>
              rw [hextractA] at hrun
              simp only at hrun
              rw [hone, ReaderT.run_bind] at hrun
              change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ =
                outcome at hrun
              unfold EStateM.bind at hrun
              match hargB : (whnfNatReducerArg argB).run methods s₁ with
              | .error err s₂ =>
                  rw [hargB] at hrun
                  rw [← hrun]
                  exact whnfNatReducerArg_error_inv hargBSupport hargBTr
                    hmethods hI₁ hargB
              | .ok second s₂ =>
                  rw [hargB] at hrun
                  have hI₂ := whnfNatReducerArg_ok_inv hargBSupport hargBTr
                    hmethods hI₁ hargB
                  cases second with
                  | none =>
                      simp only at hrun
                      rw [← hrun]
                      exact hI₂
                  | some argBResult =>
                      simp only at hrun
                      match hextractB : extractNatLit argBResult s₁.prims with
                      | none =>
                          rw [hextractB] at hrun
                          rw [← hrun]
                          exact hI₂
                      | some b =>
                          rw [hextractB] at hrun
                          simp only at hrun
                          let decision :=
                            if addr == s₁.prims.natBeq.addr then a == b
                            else a.ble b
                          let requested := KExpr.mkConst
                            (if decision then s₁.prims.boolTrue
                              else s₁.prims.boolFalse) #[]
                          have hrequestedSupport : support requested :=
                            context.generated.boolConst
                              hI₁.noAccel_primitives decision
                          obtain ⟨s₃, hintern, hI₃, _⟩ :=
                            TcM.intern_whnf_eval context.collisionFree
                              hrequestedSupport hI₂
                          rw [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
                          change EStateM.bind (TcM.intern requested) _ s₂ =
                            outcome at hrun
                          unfold EStateM.bind at hrun
                          rw [hintern] at hrun
                          simp only at hrun
                          rw [ReaderT.run_bind] at hrun
                          change EStateM.bind
                            ((finishAppResult requested args 2).run methods) _
                              s₃ = outcome at hrun
                          unfold EStateM.bind at hrun
                          obtain ⟨final, s₄, hfinish⟩ :=
                            finishAppResult_total
                              (methods := methods) (s := s₃) requested args 2
                          rw [hfinish] at hrun
                          simp only at hrun
                          rw [← hrun]
                          trivial

/-- The state partition lifted from exact binary syntax to every translated
spine with two consumed arguments and an arbitrary trailing suffix.  All
callback errors retain their actual partial states; a hit remains outside
this theorem's semantic claim. -/
theorem tryReduceNatWithSuccMode_spine_nonhit_inv
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB : KExpr .anon}
    {sourceV : VExpr}
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix) :
    match (tryReduceNatWithSuccMode source natSuccMode).run methods s with
    | .error _ s' =>
        WhnfStateInv .noAccel semantics trProj world support uvars Delta s'
    | .ok none s' =>
        WhnfStateInv .noAccel semantics trProj world support uvars Delta s'
    | .ok (some _) _ => True := by
  obtain ⟨argAV, argBV, hargASupport, hargATr,
      hargBSupport, hargBTr⟩ :=
    natBinSpine_inputs context hsourceSupport hsource hspine hargs
  generalize hrun :
    (tryReduceNatWithSuccMode source natSuccMode).run methods s = outcome
  change NatSpineNonHitInv semantics trProj world support uvars Delta outcome
  let isArith :=
    headId.addr == s.prims.natAdd.addr ||
      headId.addr == s.prims.natSub.addr ||
      headId.addr == s.prims.natMul.addr ||
      headId.addr == s.prims.natDiv.addr ||
      headId.addr == s.prims.natMod.addr ||
      headId.addr == s.prims.natPow.addr ||
      headId.addr == s.prims.natGcd.addr ||
      headId.addr == s.prims.natLand.addr ||
      headId.addr == s.prims.natLor.addr ||
      headId.addr == s.prims.natXor.addr ||
      headId.addr == s.prims.natShiftLeft.addr ||
      headId.addr == s.prims.natShiftRight.addr
  let isPred := headId.addr == s.prims.natBeq.addr ||
    headId.addr == s.prims.natBle.addr
  have harith : (isNatBinArithAddr headId.addr).run methods s =
      .ok isArith s := isNatBinArithAddr_eval methods s headId.addr
  have hpred : (isNatBinPredAddr headId.addr).run methods s =
      .ok isPred s := isNatBinPredAddr_eval methods s headId.addr
  have hzero : args[0]! = argA := by
    rw [hargs]
    grind
  have hone : args[1]! = argB := by
    rw [hargs]
    grind
  unfold tryReduceNatWithSuccMode at hrun
  rw [hspine, ReaderT.run_bind] at hrun
  change EStateM.bind (RecM.prims.run methods) _ s = outcome at hrun
  unfold EStateM.bind at hrun
  have hprims : RecM.prims.run methods s = .ok s.prims s := rfl
  rw [hprims] at hrun
  simp only at hrun
  have hnotSuccArity : (args.size == 1) = false := by
    rw [hargs]
    grind
  rw [hnotSuccArity] at hrun
  simp only [Bool.and_false, Bool.false_eq_true, if_false] at hrun
  have hnotShort : ¬(args.size < 2) := by
    rw [hargs]
    grind
  rw [if_neg hnotShort] at hrun
  simp only [pure_bind] at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinArithAddr headId.addr).run methods) _ s =
    outcome at hrun
  unfold EStateM.bind at hrun
  rw [harith] at hrun
  simp only at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((isNatBinPredAddr headId.addr).run methods) _ s =
    outcome at hrun
  unfold EStateM.bind at hrun
  rw [hpred] at hrun
  cases hisArith : isArith <;> cases hisPred : isPred
  · simp only [hisArith, hisPred, Bool.not_false, Bool.false_eq_true,
      if_false] at hrun
    rw [← hrun]
    exact hI
  · simp only [hisArith, hisPred, Bool.not_false, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, if_false, if_true] at hrun
    have hhelper : (tryReduceNatPredicate headId.addr args).run methods s =
        outcome := by simpa using hrun
    exact tryReduceNatPredicate_spine_nonhit_inv context hmethods hI
      hargASupport hargATr hargBSupport hargBTr hargs hhelper
  · simp only [hisArith, hisPred, Bool.not_true, Bool.not_false,
      Bool.false_and, Bool.false_eq_true, if_false] at hrun
    rw [hzero, ReaderT.run_bind] at hrun
    change EStateM.bind ((whnfNatReducerArg argA).run methods) _ s = outcome
      at hrun
    unfold EStateM.bind at hrun
    match hargA : (whnfNatReducerArg argA).run methods s with
    | .error err s₁ =>
        rw [hargA] at hrun
        rw [← hrun]
        exact whnfNatReducerArg_error_inv hargASupport hargATr hmethods hI
          hargA
    | .ok first s₁ =>
        rw [hargA] at hrun
        have hI₁ := whnfNatReducerArg_ok_inv hargASupport hargATr
          hmethods hI hargA
        cases first with
        | none =>
          simp only at hrun
          rw [← hrun]
          exact hI₁
        | some argAResult =>
          simp only at hrun
          rw [hone, ReaderT.run_bind] at hrun
          change EStateM.bind ((whnfNatReducerArg argB).run methods) _ s₁ =
            outcome at hrun
          unfold EStateM.bind at hrun
          match hargB : (whnfNatReducerArg argB).run methods s₁ with
          | .error err s₂ =>
              rw [hargB] at hrun
              rw [← hrun]
              exact whnfNatReducerArg_error_inv hargBSupport hargBTr
                hmethods hI₁ hargB
          | .ok second s₂ =>
              rw [hargB] at hrun
              have hI₂ := whnfNatReducerArg_ok_inv hargBSupport hargBTr
                hmethods hI₁ hargB
              cases second with
              | none =>
                simp only at hrun
                rw [← hrun]
                exact hI₂
              | some argBResult =>
                simp only at hrun
                match hextractA : extractNatLit argAResult s.prims with
                | none =>
                  rw [hextractA] at hrun
                  rw [← hrun]
                  exact hI₂
                | some a =>
                  rw [hextractA] at hrun
                  simp only at hrun
                  match hextractB : extractNatLit argBResult s.prims with
                  | none =>
                    rw [hextractB] at hrun
                    rw [← hrun]
                    exact hI₂
                  | some b =>
                    rw [hextractB] at hrun
                    simp only at hrun
                    match hcompute : computeNatBin headId.addr
                        PrimAddrs.canonical a b with
                    | none =>
                      rw [hcompute] at hrun
                      rw [← hrun]
                      exact hI₂
                    | some value =>
                      rw [hcompute] at hrun
                      simp only [if_true] at hrun
                      obtain ⟨final, s₃, hfinish⟩ :=
                        finishAppResult_total
                          (methods := methods) (s := s₂)
                          (natExprFromValue value) args 2
                      rw [ReaderT.run_bind] at hrun
                      change EStateM.bind
                        ((finishAppResult (natExprFromValue value) args 2).run
                          methods) _ s₂ = outcome at hrun
                      unfold EStateM.bind at hrun
                      rw [hfinish] at hrun
                      simp only at hrun
                      rw [← hrun]
                      trivial
  · simp only [hisArith, hisPred, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, if_false, if_true] at hrun
    have hhelper : (tryReduceNatPredicate headId.addr args).run methods s =
        outcome := by simpa using hrun
    exact tryReduceNatPredicate_spine_nonhit_inv context hmethods hI
      hargASupport hargATr hargBSupport hargBTr hargs hhelper

/-- A successful general-spine trace paired with exactly the finite intern
requests needed to rebuild its observed suffix.  The predicate certificate
starts from the requested canonical Bool node; collision-safe interning and
deterministic execution later identify it with production's returned base. -/
inductive NatSpineCertifiedSuccess (requests : List WalkerRequest)
    (methods : Methods .anon) (natSuccMode : NatSuccMode)
    (source : KExpr .anon) (headId : KId .anon)
    (us : Array (KUniv .anon)) (headInfo : ExprInfo .anon)
    (args : Array (KExpr .anon)) (argA argB : KExpr .anon)
    (s : TcState .anon) : KExpr .anon → TcState .anon → Prop
  | arithmetic {s₁ s₂ s₃ : TcState .anon}
      {argAResult argBResult final : KExpr .anon} {a b value : Nat}
      (harith : (isNatBinArithAddr headId.addr).run methods s = .ok true s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok false s)
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractA : extractNatLit argAResult s.prims = some a)
      (hextractB : extractNatLit argBResult s.prims = some b)
      (hcompute : computeNatBin headId.addr PrimAddrs.canonical a b =
        some value)
      (hfinishRun :
        (finishAppResult (natExprFromValue (m := .anon) value) args 2).run
          methods s₂ = .ok final s₃)
      (hfinish : FinishAppRequests requests
        (args.extract 2 args.size).toList
        (natExprFromValue (m := .anon) value) final) :
      NatSpineCertifiedSuccess requests methods natSuccMode source
        headId us headInfo args argA argB s final s₃
  | predicate {s₁ s₂ s₃ s₄ : TcState .anon}
      {argAResult argBResult requested base final : KExpr .anon}
      {a b : Nat} {isArith : Bool}
      (harith : (isNatBinArithAddr headId.addr).run methods s =
        .ok isArith s)
      (hpred : (isNatBinPredAddr headId.addr).run methods s = .ok true s)
      (hargA : (whnfNatReducerArg argA).run methods s =
        .ok (some argAResult) s₁)
      (hextractA : extractNatLit argAResult s₁.prims = some a)
      (hargB : (whnfNatReducerArg argB).run methods s₁ =
        .ok (some argBResult) s₂)
      (hextractB : extractNatLit argBResult s₁.prims = some b)
      (hrequested : requested = KExpr.mkConst
        (if (if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b)
          then s₁.prims.boolTrue else s₁.prims.boolFalse) #[])
      (hintern : TcM.intern requested s₂ = .ok base s₃)
      (hfinishRun : (finishAppResult base args 2).run methods s₃ =
        .ok final s₄)
      (hfinish : FinishAppRequests requests
        (args.extract 2 args.size).toList requested final) :
      NatSpineCertifiedSuccess requests methods natSuccMode source
        headId us headInfo args argA argB s final s₄

namespace NatSpineCertifiedSuccess

/-- Erase finite request coverage and recover the exhaustive operational
success trace. -/
theorem trace
    {requests : List WalkerRequest} {methods : Methods .anon}
    {natSuccMode : NatSuccMode} {source : KExpr .anon}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args : Array (KExpr .anon)}
    {argA argB result : KExpr .anon} {s s' : TcState .anon}
    (cert : NatSpineCertifiedSuccess requests methods natSuccMode
      source headId us headInfo args argA argB s result s') :
    NatSpineSuccessTrace methods natSuccMode source headId us headInfo
      args argA argB s result s' := by
  cases cert with
  | arithmetic harith hpred hargA hargB hextractA hextractB hcompute
      hfinishRun hfinish =>
      exact .arithmetic harith hpred
        (.intro hargA hargB hextractA hextractB hcompute hfinishRun)
  | predicate harith hpred hargA hextractA hargB hextractB hrequested
      hintern hfinishRun hfinish =>
      exact .predicate harith hpred
        (.intro hargA hextractA hargB hextractB hrequested hintern hfinishRun)

/-- Interpret a finitely certified general-spine hit in Theory.  The
certificate executes only the observed finite suffix; no global application
closure of `RunSupport` is assumed. -/
theorem acceptance
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {s : TcState .anon} {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB result : KExpr .anon}
    {sourceV : VExpr} {s' : TcState .anon}
    (hrun : RunAssumptions initial program requests support)
    (theory : WhnfTheory trProj world uvars)
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (cert : NatSpineCertifiedSuccess requests methods natSuccMode
      source headId us headInfo args argA argB s result s') :
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s' ∧
      support result ∧
      WhnfMeaning trProj world uvars Delta source result := by
  have hactualRun := cert.trace.eval hspine hargs
  cases cert with
  | arithmetic harith hpred hargA hargB hextractA hextractB hcompute
      hfinishRun hfinish =>
      obtain ⟨canonicalState, hcanonicalRun, hcanonicalInv,
          hresultSupport, hmeaning⟩ :=
        tryReduceNatWithSuccMode_binArithSuffix_acceptance context hrun theory
          hmethods hI hsourceSupport hsource hspine hargs hargA hargB
          hextractA hextractB hcompute hfinish
      have heq := hactualRun.symm.trans hcanonicalRun
      have hstateEq : s' = canonicalState := (EStateM.Result.ok.inj heq).2
      subst canonicalState
      exact ⟨hcanonicalInv, hresultSupport, hmeaning⟩
  | predicate harith hpred hargA hextractA hargB hextractB hrequested
      hintern hfinishRun hfinish =>
      have haddr := isNatBinPredAddr_true hpred
      rw [hrequested] at hfinish
      obtain ⟨canonicalState, hcanonicalRun, hcanonicalInv,
          hresultSupport, hmeaning⟩ :=
        tryReduceNatWithSuccMode_binPredSuffix_acceptance context hrun theory
          hmethods hI hsourceSupport hsource hspine hargs haddr hargA
          hextractA hargB hextractB hfinish
      have heq := hactualRun.symm.trans hcanonicalRun
      have hstateEq : s' = canonicalState := (EStateM.Result.ok.inj heq).2
      subst canonicalState
      exact ⟨hcanonicalInv, hresultSupport, hmeaning⟩

end NatSpineCertifiedSuccess

/-- Fixed-execution finite coverage for the only successful Nat reduction
that can be observed from these methods, source, and entry state.  Although
the predicate is quantified over success traces, the production computation
is deterministic, so this does not require closure under infinitely many
hypothetical application bases. -/
def NatSpineFinishCoverage (requests : List WalkerRequest)
    (methods : Methods .anon) (natSuccMode : NatSuccMode)
    (source : KExpr .anon) (headId : KId .anon)
    (us : Array (KUniv .anon)) (headInfo : ExprInfo .anon)
    (args : Array (KExpr .anon)) (argA argB : KExpr .anon)
    (s : TcState .anon) : Prop :=
  ∀ {result s'},
    NatSpineSuccessTrace methods natSuccMode source headId us headInfo
      args argA argB s result s' →
    NatSpineCertifiedSuccess requests methods natSuccMode source headId us
      headInfo args argA argB s result s'

/-! ### Finite request census for Nat suffix rebuilding -/

/-- A finite request-list census for every suffix rebuild observable from a
supported, translated Nat dispatcher entry under the real method/state
invariants.  Its fields stop at direct `FinishAppRequests`: neither field
assumes the semantic conclusion nor identifies production's result/state
with the certified fold.  Keeping the arithmetic value and predicate Bool
request as ordinary field indices avoids extracting computational data from
a proof-irrelevant success trace. -/
structure NatCollapseRequestCensus (requests : List WalkerRequest)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  arithmetic : ∀ {uvars : Nat} {Delta : KVLCtx}
      {source : KExpr .anon} {sourceV : VExpr}
      {headId : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {args suffix : Array (KExpr .anon)}
      {argA argB : KExpr .anon} {s s₁ s₂ s₃ : TcState .anon}
      {methods : Methods .anon}
      {argAResult argBResult final : KExpr .anon} {a b value : Nat},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    source.collectSpine = (.const headId us headInfo, args) →
    args = #[argA, argB] ++ suffix →
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (isNatBinArithAddr headId.addr).run methods s = .ok true s →
    (isNatBinPredAddr headId.addr).run methods s = .ok false s →
    (whnfNatReducerArg argA).run methods s = .ok (some argAResult) s₁ →
    (whnfNatReducerArg argB).run methods s₁ = .ok (some argBResult) s₂ →
    extractNatLit argAResult s.prims = some a →
    extractNatLit argBResult s.prims = some b →
    computeNatBin headId.addr PrimAddrs.canonical a b = some value →
    (finishAppResult (natExprFromValue (m := .anon) value) args 2).run
      methods s₂ = .ok final s₃ →
    ∃ certifiedFinal,
      FinishAppRequests requests (args.extract 2 args.size).toList
        (natExprFromValue (m := .anon) value) certifiedFinal
  predicate : ∀ {uvars : Nat} {Delta : KVLCtx}
      {source : KExpr .anon} {sourceV : VExpr}
      {headId : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {args suffix : Array (KExpr .anon)}
      {argA argB : KExpr .anon} {s s₁ s₂ s₃ s₄ : TcState .anon}
      {methods : Methods .anon}
      {argAResult argBResult requested base final : KExpr .anon}
      {a b : Nat} {isArith : Bool},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    source.collectSpine = (.const headId us headInfo, args) →
    args = #[argA, argB] ++ suffix →
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    (isNatBinArithAddr headId.addr).run methods s = .ok isArith s →
    (isNatBinPredAddr headId.addr).run methods s = .ok true s →
    (whnfNatReducerArg argA).run methods s = .ok (some argAResult) s₁ →
    extractNatLit argAResult s₁.prims = some a →
    (whnfNatReducerArg argB).run methods s₁ = .ok (some argBResult) s₂ →
    extractNatLit argBResult s₁.prims = some b →
    requested = KExpr.mkConst
      (if (if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b)
        then s₁.prims.boolTrue else s₁.prims.boolFalse) #[] →
    TcM.intern requested s₂ = .ok base s₃ →
    (finishAppResult base args 2).run methods s₃ = .ok final s₄ →
    ∃ certifiedFinal,
      FinishAppRequests requests (args.extract 2 args.size).toList requested
        certifiedFinal

namespace NatCollapseRequestCensus

/-- The Theory fact actually needed to rule out a trailing application after
a successful binary Nat reduction.  It is deliberately stated at the type
level: canonical `Nat` and `Bool` result types cannot be definitionally equal
to a function type in a well-formed context.

This is strictly narrower than `ExactArity` below.  It says nothing about
production classifiers, concrete spines, method tables, or run support, and
is the intended target for Lean4Lean's eventual canonical-type
no-confusion theorem. -/
structure NatBoolResultShapeSeparation (world : VerifyWorld) : Prop where
  nat : ∀ {uvars : Nat} {Gamma : List VExpr} {A B : VExpr},
    Lean4Lean.OnCtx Gamma (world.venv.IsType uvars) →
    ¬ world.venv.IsDefEqU uvars Gamma .nat (.forallE A B)
  bool : ∀ {uvars : Nat} {Gamma : List VExpr} {A B : VExpr},
    Lean4Lean.OnCtx Gamma (world.venv.IsType uvars) →
    ¬ world.venv.IsDefEqU uvars Gamma .bool (.forallE A B)

/-- A translated application suffix must be empty when its base has a
certified canonical result type that is not definitionally a function.

If the suffix had a first argument, structural translation of that
application would type the base as a `forallE`.  Translation uniqueness and
the base reduction meaning transport the separately certified result type
back to the same base expression.  Theory type uniqueness then yields the
forbidden result-type/function-type equality. -/
theorem suffix_eq_empty_of_result_shape
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {base result : KExpr .anon} {suffix : Array (KExpr .anon)}
    {fullV resultV resultTy : VExpr}
    (hfull : TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkAppN base suffix) fullV)
    (hmeaning : WhnfMeaning trProj world uvars Delta base result)
    (hresult : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hresultType : world.venv.HasType uvars Delta.toCtx resultV resultTy)
    (hnotFunction : ∀ {A B : VExpr},
      ¬ world.venv.IsDefEqU uvars Delta.toCtx resultTy (.forallE A B)) :
    suffix = #[] := by
  by_contra hne
  have hlistNe : suffix.toList ≠ [] := by
    intro hnil
    apply hne
    apply Array.toList_inj.mp
    simpa using hnil
  obtain ⟨arg, rest, hlist⟩ := List.exists_cons_of_ne_nil hlistNe
  have hfullList :
      TrKExprS world.venv uvars world.nameOf trProj Delta
        (suffix.toList.foldl KExpr.mkApp base) fullV := by
    simpa only [KExpr.mkAppN, Array.foldl_toList] using hfull
  rw [hlist] at hfullList
  simp only [List.foldl_cons] at hfullList
  obtain ⟨appV, happTr⟩ :=
    TrKExprS.foldlMkApp_initial (rest := rest) hfullList
  rw [KExpr.mkApp_shape] at happTr
  let .app hbaseFun _ hbaseTr _ := happTr
  obtain ⟨meaningBaseV, meaningResultV, hmeaningBase, hmeaningResult,
    hmeaningEq⟩ := hmeaning
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have hbaseEq := hbaseTr.uniq world.venvWF theory.literalWF
    theory.projections hctx hmeaningBase
  have hresultEq := hmeaningResult.uniq world.venvWF theory.literalWF
    theory.projections hctx hresult
  have hbaseResultEq := hbaseEq.trans world.venvWF hDelta
    (hmeaningEq.trans world.venvWF hDelta hresultEq)
  have hbaseResultType :=
    (hbaseResultEq.of_r world.venvWF hDelta hresultType).hasType.1
  have htypes := hbaseResultType.uniqU world.venvWF hDelta hbaseFun
  exact hnotFunction htypes

/-- Typed-arity boundary for classifier-confirmed binary Nat primitives.
Only these heads are constrained: unrelated supported applications may have
arbitrary arity.  A Theory shape-separation result for canonical Nat/Bool
result types can construct the weaker success-scoped census directly via
`of_result_shape`; this stronger classifier-only form remains as a
compatibility interface. -/
def ExactArity
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ {uvars : Nat} {Delta : KVLCtx}
      {source : KExpr .anon} {sourceV : VExpr}
      {headId : KId .anon} {us : Array (KUniv .anon)}
      {headInfo : ExprInfo .anon} {args suffix : Array (KExpr .anon)}
      {argA argB : KExpr .anon} {s : TcState .anon}
      {methods : Methods .anon},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    source.collectSpine = (.const headId us headInfo, args) →
    args = #[argA, argB] ++ suffix →
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
    ((isNatBinArithAddr headId.addr).run methods s = .ok true s ∨
      (isNatBinPredAddr headId.addr).run methods s = .ok true s) →
    suffix = #[]

/-- Runs whose supported Nat-success entries have no trailing arguments need
no suffix requests at all.  This is the exact bridge expected from a future
typed-arity theorem: once the translated primitive application is known to
end after its two Nat arguments, both census fields reduce to
`FinishAppRequests.nil`. -/
theorem of_no_suffix
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hnoSuffix : ExactArity semantics trProj world support) :
    NatCollapseRequestCensus requests semantics trProj world support := by
  constructor
  · intro uvars Delta source sourceV headId us headInfo args suffix argA argB
      s s₁ s₂ s₃ methods argAResult argBResult final a b value
      hsourceSupport hsource hspine hargs hmethods hI harith _ _ _ _ _ _ _
    have hsuffix := hnoSuffix hsourceSupport hsource hspine hargs hmethods hI
      (Or.inl harith)
    have hrest : (args.extract 2 args.size).toList = [] := by
      rw [hargs, hsuffix]
      simp
    refine ⟨natExprFromValue (m := .anon) value, ?_⟩
    rw [hrest]
    exact .nil _
  · intro uvars Delta source sourceV headId us headInfo args suffix argA argB
      s s₁ s₂ s₃ s₄ methods argAResult argBResult requested base final a b
      isArith hsourceSupport hsource hspine hargs hmethods hI _ hpred _ _ _ _
      _ _ _
    have hsuffix := hnoSuffix hsourceSupport hsource hspine hargs hmethods hI
      (Or.inr hpred)
    have hrest : (args.extract 2 args.size).toList = [] := by
      rw [hargs, hsuffix]
      simp
    refine ⟨requested, ?_⟩
    rw [hrest]
    exact .nil _

/-- Construct the finite suffix census from the semantic result-shape fact
that is actually exercised by successful reducer traces.

The arithmetic and predicate fields first replay their two successful
argument callbacks far enough to prove meaning for the exact binary prefix.
The canonical result literal gives that prefix type `Nat` or `Bool`.  A
nonempty translated suffix would simultaneously give the prefix a function
type, so `NatBoolResultShapeSeparation` forces the suffix to be empty and the
request certificate is `FinishAppRequests.nil`.  This removes the broader
classifier-only `ExactArity` assumption from the production closure path. -/
theorem of_result_shape
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (shape : NatBoolResultShapeSeparation world) :
    NatCollapseRequestCensus requests semantics trProj world support := by
  constructor
  · intro uvars Delta source sourceV headId us headInfo args suffix argA argB
      s s₁ s₂ s₃ methods argAResult argBResult final a b value
      hsourceSupport hsource hspine hargs hmethods hI _ _ hargA hargB
      hextractA hextractB hcompute _
    have hcatalog := hI.1.core.trustedCatalog
    have hDelta := hI.2.1.wf
    have hcanonical := hI.noAccel_primitives
    have htable := context.stateTable hI
    obtain ⟨name, hname, hreflect⟩ :=
      context.computeNatBin_defeq hcatalog hcanonical hcompute
    have hspineTr := trAppSpine_of_collectSpine hsource hspine
    have hcanonicalSource :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (KExpr.mkAppN (.const headId us headInfo) args) sourceV := by
      rw [KExpr.mkAppN]
      simpa only [Array.foldl_toList] using hspineTr.tr
    have hcanonicalSuffix :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (KExpr.mkAppN
            (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
            suffix) sourceV := by
      simpa [hargs, KExpr.mkAppN] using hcanonicalSource
    have hcanonicalSuffixList :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (suffix.toList.foldl KExpr.mkApp
            (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB))
          sourceV := by
      simpa only [KExpr.mkAppN, Array.foldl_toList] using hcanonicalSuffix
    obtain ⟨baseV, hbaseTr⟩ :=
      TrKExprS.foldlMkApp_initial (rest := suffix.toList)
        hcanonicalSuffixList
    have hbaseTrExact := hbaseTr
    rw [KExpr.mkApp_shape, KExpr.mkApp_shape] at hbaseTrExact
    obtain ⟨argAV, argBV, hbaseV, hargATr, hargBTr⟩ :=
      hbaseTrExact.natBinExact_inv hDelta hname hreflect
    subst baseV
    have hinputSupport := context.inputs.spine hsourceSupport hspine
    have hargASupport : support argA := by
      simpa [hargs] using hinputSupport.2 0 (by rw [hargs]; grind)
    have hargBSupport : support argB := by
      simpa [hargs] using hinputSupport.2 1 (by rw [hargs]; grind)
    have hargAPost :=
      whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
    rw [hargA] at hargAPost
    change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
      support argAResult ∧
        WhnfPost trProj world uvars Delta argAV argAResult at hargAPost
    have hargBPost :=
      whnfNatReducerArg_post_wf hargBSupport hargBTr methods hmethods
        hargAPost.1
    rw [hargB] at hargBPost
    change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₂ ∧
      support argBResult ∧
        WhnfPost trProj world uvars Delta argBV argBResult at hargBPost
    have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
        (natExprFromValue (m := .anon) value) (.natLit value) :=
      TrKExprS.natExprFromValue hcatalog htable value
    have hbaseMeaningExact := WhnfMeaning.natBinExact hDelta htable
      context.theoryPrimitives hbaseTrExact hargAPost.2.2 hargBPost.2.2
      hextractA hextractB hreflect hresultTr
    have hbaseMeaning : WhnfMeaning trProj world uvars Delta
        (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
        (natExprFromValue (m := .anon) value) := by
      rw [KExpr.mkApp_shape, KExpr.mkApp_shape]
      exact hbaseMeaningExact
    have hnatType₀ : world.venv.HasType uvars [] (.natLit value) .nat := by
      simpa [Lean4Lean.VLCtx.toCtx] using
        (Lean4Lean.TrExprS.natLit
          (Us := List.replicate uvars Lean.Name.anonymous) (Δ := [])
          context.theoryPrimitives (htable.nat.contains hcatalog) value).2
    have hnatType : world.venv.HasType uvars Delta.toCtx
        (.natLit value) .nat :=
      hnatType₀.weak0 world.venvWF
    have hsuffix := suffix_eq_empty_of_result_shape (theory uvars) hDelta
      hcanonicalSuffix hbaseMeaning hresultTr hnatType (shape.nat hDelta)
    have hrest : (args.extract 2 args.size).toList = [] := by
      rw [hargs, hsuffix]
      simp
    refine ⟨natExprFromValue (m := .anon) value, ?_⟩
    rw [hrest]
    exact .nil _
  · intro uvars Delta source sourceV headId us headInfo args suffix argA argB
      s s₁ s₂ s₃ s₄ methods argAResult argBResult requested base final a b
      isArith hsourceSupport hsource hspine hargs hmethods hI _ hpred hargA
      hextractA hargB hextractB hrequested _ _
    have hcatalog := hI.1.core.trustedCatalog
    have hDelta := hI.2.1.wf
    have hspineTr := trAppSpine_of_collectSpine hsource hspine
    have hcanonicalSource :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (KExpr.mkAppN (.const headId us headInfo) args) sourceV := by
      rw [KExpr.mkAppN]
      simpa only [Array.foldl_toList] using hspineTr.tr
    have hcanonicalSuffix :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (KExpr.mkAppN
            (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
            suffix) sourceV := by
      simpa [hargs, KExpr.mkAppN] using hcanonicalSource
    have hcanonicalSuffixList :
        TrKExprS world.venv uvars world.nameOf trProj Delta
          (suffix.toList.foldl KExpr.mkApp
            (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB))
          sourceV := by
      simpa only [KExpr.mkAppN, Array.foldl_toList] using hcanonicalSuffix
    obtain ⟨baseV, hbaseTr⟩ :=
      TrKExprS.foldlMkApp_initial (rest := suffix.toList)
        hcanonicalSuffixList
    have hbaseTrExact := hbaseTr
    rw [KExpr.mkApp_shape, KExpr.mkApp_shape] at hbaseTrExact
    let .app _ _ hprefixTr hargBTr := hbaseTrExact
    let .app _ _ _ hargATr := hprefixTr
    have hinputSupport := context.inputs.spine hsourceSupport hspine
    have hargASupport : support argA := by
      simpa [hargs] using hinputSupport.2 0 (by rw [hargs]; grind)
    have hargBSupport : support argB := by
      simpa [hargs] using hinputSupport.2 1 (by rw [hargs]; grind)
    have hargAPost :=
      whnfNatReducerArg_post_wf hargASupport hargATr methods hmethods hI
    rw [hargA] at hargAPost
    change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
      support argAResult ∧
        WhnfPost trProj world uvars Delta _ argAResult at hargAPost
    have hcanonical₀ := hI.noAccel_primitives
    have hcanonical₁ := hargAPost.1.noAccel_primitives
    have hbeq₀ : s.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
      simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
        congrArg PrimAddrs.natBeq hcanonical₀
    have hble₀ : s.prims.natBle.addr = PrimAddrs.canonical.natBle := by
      simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
        congrArg PrimAddrs.natBle hcanonical₀
    have hbeq₁ : s₁.prims.natBeq.addr = PrimAddrs.canonical.natBeq := by
      simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
        congrArg PrimAddrs.natBeq hcanonical₁
    have hble₁ : s₁.prims.natBle.addr = PrimAddrs.canonical.natBle := by
      simpa [Primitives.CanonicalAnon, Primitives.addressTable] using
        congrArg PrimAddrs.natBle hcanonical₁
    have haddr := isNatBinPredAddr_true hpred
    have haddr₁ : headId.addr = s₁.prims.natBeq.addr ∨
        headId.addr = s₁.prims.natBle.addr := by
      rcases haddr with hbeq | hble
      · exact .inl (hbeq.trans (hbeq₀.trans hbeq₁.symm))
      · exact .inr (hble.trans (hble₀.trans hble₁.symm))
    obtain ⟨name, decision, hname, hdecision, hreflect⟩ :=
      context.natPredicate_defeq hcatalog hcanonical₁ haddr₁
    subst decision
    obtain ⟨argAV, argBV, hbaseV, hargATrExact, hargBTrExact⟩ :=
      hbaseTrExact.natBinExact_inv hDelta hname hreflect
    subst baseV
    have hargAPostExact :=
      whnfNatReducerArg_post_wf hargASupport hargATrExact methods hmethods hI
    rw [hargA] at hargAPostExact
    change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₁ ∧
      support argAResult ∧
        WhnfPost trProj world uvars Delta argAV argAResult at hargAPostExact
    have hargBPost :=
      whnfNatReducerArg_post_wf hargBSupport hargBTrExact methods hmethods
        hargAPostExact.1
    rw [hargB] at hargBPost
    change WhnfStateInv .noAccel semantics trProj world support uvars Delta s₂ ∧
      support argBResult ∧
        WhnfPost trProj world uvars Delta argBV argBResult at hargBPost
    let decision :=
      if headId.addr == s₁.prims.natBeq.addr then a == b else a.ble b
    let reduced := KExpr.mkConst
      (if decision then s₁.prims.boolTrue else s₁.prims.boolFalse) #[]
    have hrequested' : requested = reduced := by
      simpa [decision, reduced] using hrequested
    subst requested
    have htable := context.stateTable hargAPostExact.1
    have hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
        reduced (.boolLit decision) :=
      TrKExprS.boolExprFromDecision hcatalog htable
        context.theoryPrimitives _
    have hbaseMeaningExact := WhnfMeaning.natBinExact hDelta htable
      context.theoryPrimitives hbaseTrExact hargAPostExact.2.2 hargBPost.2.2
      hextractA hextractB hreflect hresultTr
    have hbaseMeaning : WhnfMeaning trProj world uvars Delta
        (KExpr.mkApp (KExpr.mkApp (.const headId us headInfo) argA) argB)
        reduced := by
      rw [KExpr.mkApp_shape, KExpr.mkApp_shape]
      exact hbaseMeaningExact
    have hboolType₀ : world.venv.HasType uvars []
        (.boolLit decision) .bool := by
      simpa [Lean4Lean.VLCtx.toCtx] using
        (Lean4Lean.TrExprS.boolLit
          (Us := List.replicate uvars Lean.Name.anonymous) (Δ := [])
          context.theoryPrimitives (htable.boolType.contains hcatalog)
          decision).2
    have hboolType : world.venv.HasType uvars Delta.toCtx
        (.boolLit decision) .bool :=
      hboolType₀.weak0 world.venvWF
    have hsuffix := suffix_eq_empty_of_result_shape (theory uvars) hDelta
      hcanonicalSuffix hbaseMeaning hresultTr hboolType (shape.bool hDelta)
    have hrest : (args.extract 2 args.size).toList = [] := by
      rw [hargs, hsuffix]
      simp
    refine ⟨reduced, ?_⟩
    rw [hrest]
    exact .nil _

/-- Turn the request-only census into the older fixed-entry success
certificate.  The arithmetic and predicate callbacks first recover the
state invariant at the start of suffix rebuilding.  The census fold is then
executed through `RunAssumptions`, and determinism identifies its result and
post-state with production's observed run.  In the predicate case, the
collision-free direct Bool intern is separately replayed before the suffix
certificate is accepted. -/
theorem certify
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    (hrun : RunAssumptions initial program requests support)
    (census : NatCollapseRequestCensus requests semantics trProj world
      support)
    {uvars : Nat} {Delta : KVLCtx}
    {source : KExpr .anon} {sourceV : VExpr}
    {headId : KId .anon} {us : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {args suffix : Array (KExpr .anon)}
    {argA argB : KExpr .anon} {s : TcState .anon}
    {methods : Methods .anon} {result : KExpr .anon} {s' : TcState .anon}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hmethods : Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hI : WhnfStateInv .noAccel semantics trProj world support uvars Delta s)
    (trace : NatSpineSuccessTrace methods natSuccMode source headId us
      headInfo args argA argB s result s') :
    NatSpineCertifiedSuccess requests methods natSuccMode source headId us
      headInfo args argA argB s result s' := by
  obtain ⟨argAV, argBV, hargASupport, hargATr, hargBSupport, hargBTr⟩ :=
    natBinSpine_inputs context hsourceSupport hsource hspine hargs
  cases trace with
  | arithmetic harith hpred body =>
      cases body with
      | intro hargA hargB hextractA hextractB hcompute hfinishRun =>
          obtain ⟨certifiedFinal, hfinishCert⟩ :=
            census.arithmetic hsourceSupport hsource hspine hargs hmethods
              hI harith hpred hargA hargB hextractA hextractB hcompute
              hfinishRun
          have hI₁ := whnfNatReducerArg_ok_inv hargASupport hargATr
            hmethods hI hargA
          have hI₂ := whnfNatReducerArg_ok_inv hargBSupport hargBTr
            hmethods hI₁ hargB
          obtain ⟨certifiedState, hcertifiedRun, _, _⟩ :=
            hfinishCert.eval hrun hI₂
          have heq := hfinishRun.symm.trans hcertifiedRun
          have hresultEq : result = certifiedFinal :=
            (EStateM.Result.ok.inj heq).1
          have hstateEq : s' = certifiedState :=
            (EStateM.Result.ok.inj heq).2
          subst certifiedFinal
          subst certifiedState
          exact .arithmetic harith hpred hargA hargB hextractA hextractB
            hcompute hfinishRun hfinishCert
  | predicate harith hpred body =>
      cases body with
      | intro hargA hextractA hargB hextractB hrequested hintern
          hfinishRun =>
          rename_i isArith s₁ s₂ s₃ argAResult argBResult requested base a b
          obtain ⟨certifiedFinal, hfinishCert⟩ :=
            census.predicate hsourceSupport hsource hspine hargs hmethods
              hI harith hpred hargA hextractA hargB hextractB hrequested
              hintern hfinishRun
          have hI₁ := whnfNatReducerArg_ok_inv hargASupport hargATr
            hmethods hI hargA
          have hI₂ := whnfNatReducerArg_ok_inv hargBSupport hargBTr
            hmethods hI₁ hargB
          have hcanonical₁ := hI₁.noAccel_primitives
          have hrequestedSupport : support requested := by
            rw [hrequested]
            exact context.generated.boolConst hcanonical₁ _
          obtain ⟨canonicalState, hcanonicalIntern, hI₃, _⟩ :=
            TcM.intern_whnf_eval context.collisionFree hrequestedSupport hI₂
          have hinternEq := hintern.symm.trans hcanonicalIntern
          have hbaseEq : base = requested :=
            (EStateM.Result.ok.inj hinternEq).1
          have hstateEq : s₃ = canonicalState :=
            (EStateM.Result.ok.inj hinternEq).2
          subst base
          subst canonicalState
          obtain ⟨certifiedState, hcertifiedRun, _, _⟩ :=
            hfinishCert.eval hrun hI₃
          have heq := hfinishRun.symm.trans hcertifiedRun
          have hresultEq : result = certifiedFinal :=
            (EStateM.Result.ok.inj heq).1
          have hfinalStateEq : s' = certifiedState :=
            (EStateM.Result.ok.inj heq).2
          subst certifiedFinal
          subst certifiedState
          exact .predicate harith hpred hargA hextractA hargB hextractB
            hrequested hintern hfinishRun hfinishCert

end NatCollapseRequestCensus

/-- General-spine Nat optional-reduction contract for one fixed entry state.
Misses and errors are unconditional; only an observed hit consumes the finite
`NatSpineFinishCoverage` witness.  The surrounding run assumptions supply
collision freedom and exact support for those requests. -/
theorem tryReduceNatWithSuccMode_spine_optional_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {headId : KId .anon}
    {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
    {args suffix : Array (KExpr .anon)} {argA argB : KExpr .anon}
    {sourceV : VExpr}
    (hrun : RunAssumptions initial program requests support)
    (theory : WhnfTheory trProj world uvars)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : source.collectSpine = (.const headId us headInfo, args))
    (hargs : args = #[argA, argB] ++ suffix)
    (hcoverage : ∀ methods,
      Methods.WFAt .noAccel semantics trProj world support uvars methods →
      WhnfStateInv .noAccel semantics trProj world support uvars Delta s →
      NatSpineFinishCoverage requests methods natSuccMode source headId
        us headInfo args argA argB s) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatWithSuccMode source natSuccMode)
      (fun outcome _ => match outcome with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Delta source reduced) := by
  intro methods hmethods hI
  have hnonhit := tryReduceNatWithSuccMode_spine_nonhit_inv context
    hmethods hI hsourceSupport hsource hspine hargs
  match hactual : (tryReduceNatWithSuccMode source natSuccMode).run methods s with
  | .error err s' =>
      rw [hactual] at hnonhit
      simp only at hnonhit ⊢
      exact ⟨hnonhit, trivial⟩
  | .ok outcome s' =>
      rw [hactual] at hnonhit
      cases outcome with
      | none =>
          simp only at hnonhit ⊢
          exact ⟨hnonhit, trivial⟩
      | some result =>
          simp only at hnonhit ⊢
          have trace := NatSpineSuccessTrace.complete hspine hargs hactual
          have cert := hcoverage methods hmethods hI trace
          have haccept := cert.acceptance context hrun theory hmethods hI
            hsourceSupport hsource hspine hargs
          exact ⟨haccept.1, haccept.2⟩

/-! ### Successor-collapse operational and memo-write closure -/

/-- A memo hit at successor-loop entry bypasses the bounded loop and returns
the original optional-reduction miss at the exact post-key state. -/
theorem tryReduceNatSuccIter_entryHit
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {arg : KExpr .anon} {key : Address × Address}
    (hkey : TcM.whnfKey arg s = .ok key s₁)
    (hhit : s₁.env.natSuccStuck.contains key = true) :
    (tryReduceNatSuccIter arg).run methods s = .ok none s₁ := by
  unfold tryReduceNatSuccIter
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey arg) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  have hget : ReaderT.run
      (get : RecM .anon (TcState .anon)) methods s₁ = .ok s₁ s₁ := rfl
  change EStateM.bind
    (ReaderT.run (get : RecM .anon (TcState .anon)) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hget]
  simp [hhit]
  rfl

/-- Failure of the initial context-key computation is propagated with its
actual partial state; the memo and bounded loop are not consulted. -/
theorem tryReduceNatSuccIter_entryKeyError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {arg : KExpr .anon} {err : TcError .anon}
    (hkey : TcM.whnfKey arg s = .error err s₁) :
    (tryReduceNatSuccIter arg).run methods s = .error err s₁ := by
  unfold tryReduceNatSuccIter
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey arg) _ s = _
  unfold EStateM.bind
  rw [hkey]

/-- On an entry-memo miss, the public successor helper is exactly the named
bounded loop initialized with offset one and the entry key as its first
visited marker. -/
theorem tryReduceNatSuccIter_entryMiss
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {arg : KExpr .anon} {key : Address × Address}
    (hkey : TcM.whnfKey arg s = .ok key s₁)
    (hmiss : s₁.env.natSuccStuck.contains key = false) :
    (tryReduceNatSuccIter arg).run methods s =
      (runBounded tryReduceNatSuccIterStep maxWhnfFuel.toNat
        (arg, 1, #[key])).run methods s₁ := by
  unfold tryReduceNatSuccIter
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey arg) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simp only
  rw [ReaderT.run_bind]
  have hget : ReaderT.run
      (get : RecM .anon (TcState .anon)) methods s₁ = .ok s₁ s₁ := rfl
  change EStateM.bind
    (ReaderT.run (get : RecM .anon (TcState .anon)) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hget]
  simp [hmiss]

/-- The linear-recognizer hit has strict precedence over recursive WHNF. -/
theorem tryReduceNatSuccIterStep_linearHit
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {cur result : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    (hlinear : (tryReduceNatSuccLinearRec cur offset).run methods s =
      .ok (some result) s₁) :
    (tryReduceNatSuccIterStep (cur, offset, visited)).run methods s =
      .ok (.done (some result)) s₁ := by
  unfold tryReduceNatSuccIterStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((tryReduceNatSuccLinearRec cur offset).run methods)
    _ s = _
  unfold EStateM.bind
  rw [hlinear]
  rfl

/-- A linear-recognizer error is propagated before recursive WHNF begins. -/
theorem tryReduceNatSuccIterStep_linearError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {err : TcError .anon}
    (hlinear : (tryReduceNatSuccLinearRec cur offset).run methods s =
      .error err s₁) :
    (tryReduceNatSuccIterStep (cur, offset, visited)).run methods s =
      .error err s₁ := by
  unfold tryReduceNatSuccIterStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((tryReduceNatSuccLinearRec cur offset).run methods)
    _ s = _
  unfold EStateM.bind
  rw [hlinear]

/-- After a linear miss, recursive-WHNF errors retain the callback's exact
partial state and never reach literal classification or a memo write. -/
theorem tryReduceNatSuccIterStep_whnfError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {err : TcError .anon}
    (hlinear : (tryReduceNatSuccLinearRec cur offset).run methods s =
      .ok none s₁)
    (hwhnf : (whnfModeRec cur .stuck).run methods s₁ = .error err s₂) :
    (tryReduceNatSuccIterStep (cur, offset, visited)).run methods s =
      .error err s₂ := by
  unfold tryReduceNatSuccIterStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((tryReduceNatSuccLinearRec cur offset).run methods)
    _ s = _
  unfold EStateM.bind
  rw [hlinear]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfModeRec cur .stuck).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hwhnf]

/-- Once both recursive phases have succeeded, the named classification seam
is used without changing or filtering any of its success/error outcomes. -/
theorem tryReduceNatSuccIterStep_afterWhnf
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {cur w : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (BoundedStep (KExpr .anon × Nat × Array (Address × Address))
        (Option (KExpr .anon)))}
    (hlinear : (tryReduceNatSuccLinearRec cur offset).run methods s =
      .ok none s₁)
    (hwhnf : (whnfModeRec cur .stuck).run methods s₁ = .ok w s₂)
    (hafter : (tryReduceNatSuccAfterWhnf w offset visited).run methods s₂ =
      outcome) :
    (tryReduceNatSuccIterStep (cur, offset, visited)).run methods s =
      outcome := by
  unfold tryReduceNatSuccIterStep
  rw [ReaderT.run_bind]
  change EStateM.bind ((tryReduceNatSuccLinearRec cur offset).run methods)
    _ s = _
  unfold EStateM.bind
  rw [hlinear]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((whnfModeRec cur .stuck).run methods) _ s₁ = _
  unfold EStateM.bind
  rw [hwhnf]
  simpa using hafter

/-- Literal recognition terminates the iteration state-purely and adds the
accumulated successor offset exactly once. -/
theorem tryReduceNatSuccAfterWhnf_literal
    {methods : Methods .anon} {s : TcState .anon}
    {w : KExpr .anon} {offset n : Nat}
    {visited : Array (Address × Address)} {p : Primitives .anon}
    (hprims : s.prims = p)
    (hextract : extractNatLit w p = some n) :
    (tryReduceNatSuccAfterWhnf w offset visited).run methods s =
      .ok (.done (some (natExprFromValue (n + offset)))) s := by
  unfold tryReduceNatSuccAfterWhnf
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok p s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok p s
    rw [hprims]
  rw [hprimsRun]
  simp [hextract]
  rfl

/-- A normalized non-successor writes exactly the visited marker fold, then
returns `.done none`; it cannot proceed to either key computation. -/
theorem tryReduceNatSuccAfterWhnf_stuck
    {methods : Methods .anon} {s : TcState .anon}
    {w : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {p : Primitives .anon}
    (hprims : s.prims = p)
    (hextract : extractNatLit w p = none)
    (hclass : (isNatSuccSpine w).run methods s = .ok false s) :
    let after := {s with env := {s.env with natSuccStuck :=
      (visited.foldl (fun set key => set.insert key) s.env.natSuccStuck)}}
    (tryReduceNatSuccAfterWhnf w offset visited).run methods s =
      .ok (.done none) after := by
  dsimp only
  unfold tryReduceNatSuccAfterWhnf
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok p s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok p s
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextract]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatSuccSpine w).run methods) _ s = _
  unfold EStateM.bind
  rw [hclass]
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- Exact evaluator for the shared stuck-marker commit. -/
theorem recordNatSuccStuck_eval
    {methods : Methods .anon} {s : TcState .anon}
    (visited : Array (Address × Address)) :
    let after := {s with env := {s.env with natSuccStuck :=
      (visited.foldl (fun set key => set.insert key) s.env.natSuccStuck)}}
    (recordNatSuccStuck visited).run methods s = .ok () after := by
  rfl

/-- The shared memo commit preserves every K1 state component when each
visited marker has explicit cache provenance. -/
theorem recordNatSuccStuck_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    (visited : Array (Address × Address))
    (hnew : ∀ key ∈ visited,
      CacheProvenance semantics (CacheAuthority.stable world) support
        (.natSuccStuck key)) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (recordNatSuccStuck visited) (fun _ _ => True) := by
  unfold recordNatSuccStuck
  apply RecM.WF.modify
  · intro hI
    exact NatSuccStuckCacheUpdate.fold_whnfStateInv visited hI hnew
  · intro _
    trivial

/-- The first peeled-argument key failure is propagated before memo lookup. -/
theorem tryReduceNatSuccPeel_keyError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {err : TcError .anon}
    (hkey : TcM.whnfKey cur s = .error err s₁) :
    (tryReduceNatSuccPeel w cur offset visited).run methods s =
      .error err s₁ := by
  unfold tryReduceNatSuccPeel
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.whnfKey cur) _ s = _
  unfold EStateM.bind
  rw [hkey]

/-- A successful peeled-argument key is handed to the memo-decision seam
without altering any of its possible outcomes. -/
theorem tryReduceNatSuccPeel_afterKey
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {curKey : Address × Address}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (BoundedStep (KExpr .anon × Nat × Array (Address × Address))
        (Option (KExpr .anon)))}
    (hkey : TcM.whnfKey cur s = .ok curKey s₁)
    (hafter : (tryReduceNatSuccPeelAfterKey w cur offset visited curKey).run
      methods s₁ = outcome) :
    (tryReduceNatSuccPeel w cur offset visited).run methods s = outcome := by
  unfold tryReduceNatSuccPeel
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.whnfKey cur) _ s = _
  unfold EStateM.bind
  rw [hkey]
  simpa using hafter

/-- A known-stuck suffix commits the visited prefix and terminates without
computing the normalized successor expression's key. -/
theorem tryReduceNatSuccPeelAfterKey_hit
    {methods : Methods .anon} {s : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {curKey : Address × Address}
    (hhit : s.env.natSuccStuck.contains curKey = true) :
    let after := {s with env := {s.env with natSuccStuck :=
      (visited.foldl (fun set key => set.insert key) s.env.natSuccStuck)}}
    (tryReduceNatSuccPeelAfterKey w cur offset visited curKey).run methods s =
      .ok (.done none) after := by
  dsimp only
  unfold tryReduceNatSuccPeelAfterKey
  rw [ReaderT.run_bind]
  have hget : ReaderT.run
      (get : RecM .anon (TcState .anon)) methods s = .ok s s := rfl
  change EStateM.bind
    (ReaderT.run (get : RecM .anon (TcState .anon)) methods) _ s = _
  unfold EStateM.bind
  rw [hget]
  simp [hhit, recordNatSuccStuck]
  rfl

/-- A peeled-key memo miss delegates exactly to the second-key seam. -/
theorem tryReduceNatSuccPeelAfterKey_miss
    {methods : Methods .anon} {s : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {curKey : Address × Address}
    (hmiss : s.env.natSuccStuck.contains curKey = false) :
    (tryReduceNatSuccPeelAfterKey w cur offset visited curKey).run methods s =
      (tryReduceNatSuccPeelMiss w cur offset visited curKey).run methods s := by
  unfold tryReduceNatSuccPeelAfterKey
  rw [ReaderT.run_bind]
  have hget : ReaderT.run
      (get : RecM .anon (TcState .anon)) methods s = .ok s s := rfl
  change EStateM.bind
    (ReaderT.run (get : RecM .anon (TcState .anon)) methods) _ s = _
  unfold EStateM.bind
  rw [hget]
  simp [hmiss]

/-- The second key failure retains the partial state reached after the first
key and memo miss. -/
theorem tryReduceNatSuccPeelMiss_keyError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {curKey : Address × Address}
    {err : TcError .anon}
    (hkey : TcM.whnfKey w s = .error err s₁) :
    (tryReduceNatSuccPeelMiss w cur offset visited curKey).run methods s =
      .error err s₁ := by
  unfold tryReduceNatSuccPeelMiss
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.whnfKey w) _ s = _
  unfold EStateM.bind
  rw [hkey]

/-- Both successor keys are appended in production order before the loop
continues, and the numeric offset is incremented exactly once. -/
theorem tryReduceNatSuccPeelMiss_next
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)} {curKey wKey : Address × Address}
    (hkey : TcM.whnfKey w s = .ok wKey s₁) :
    (tryReduceNatSuccPeelMiss w cur offset visited curKey).run methods s =
      .ok (.next (cur, offset + 1, (visited.push curKey).push wKey)) s₁ := by
  unfold tryReduceNatSuccPeelMiss
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.whnfKey w) _ s = _
  unfold EStateM.bind
  rw [hkey]
  rfl

/-- A positive successor classification delegates to the peel seam without
filtering either its successful action or its partial error state. -/
theorem tryReduceNatSuccAfterWhnf_succ
    {methods : Methods .anon} {s : TcState .anon}
    {w head cur : KExpr .anon} {args : Array (KExpr .anon)}
    {offset : Nat} {visited : Array (Address × Address)}
    {p : Primitives .anon}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (BoundedStep (KExpr .anon × Nat × Array (Address × Address))
        (Option (KExpr .anon)))}
    (hprims : s.prims = p)
    (hextract : extractNatLit w p = none)
    (hspine : w.collectSpine = (head, args))
    (harg : args[0]! = cur)
    (hclass : (isNatSuccSpine w).run methods s = .ok true s)
    (hpeel : (tryReduceNatSuccPeel w cur offset visited).run methods s =
      outcome) :
    (tryReduceNatSuccAfterWhnf w offset visited).run methods s = outcome := by
  unfold tryReduceNatSuccAfterWhnf
  rw [ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok p s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok p s
    rw [hprims]
  rw [hprimsRun]
  simp only
  rw [hextract]
  simp only
  rw [hspine]
  rw [ReaderT.run_bind]
  change EStateM.bind ((isNatSuccSpine w).run methods) _ s = _
  unfold EStateM.bind
  rw [hclass]
  simp only [if_true]
  rw [harg]
  simpa using hpeel

/-- In `stuck` mode the outer Nat dispatcher recognizes `Nat.succ` but
intentionally bypasses the successor loop. -/
theorem tryReduceNatWithSuccMode_succ_stuck
    {methods : Methods .anon} {s : TcState .anon}
    {source arg : KExpr .anon} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {p : Primitives .anon}
    (hspine : source.collectSpine = (.const id us info, #[arg]))
    (hprims : s.prims = p)
    (haddr : id.addr = p.natSucc.addr) :
    (tryReduceNatWithSuccMode source .stuck).run methods s =
      .ok none s := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok p s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok p s
    rw [hprims]
  rw [hprimsRun]
  simp [haddr]
  rfl

/-- In collapse mode the exact same one-argument spine delegates to the
successor loop, preserving both successes and partial errors. -/
theorem tryReduceNatWithSuccMode_succ_collapse
    {methods : Methods .anon} {s : TcState .anon}
    {source arg : KExpr .anon} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {p : Primitives .anon}
    {outcome : EStateM.Result (TcError .anon) (TcState .anon)
      (Option (KExpr .anon))}
    (hspine : source.collectSpine = (.const id us info, #[arg]))
    (hprims : s.prims = p)
    (haddr : id.addr = p.natSucc.addr)
    (hiter : (tryReduceNatSuccIter arg).run methods s = outcome) :
    (tryReduceNatWithSuccMode source .collapse).run methods s = outcome := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  have hprimsRun : RecM.prims.run methods s = .ok p s := by
    unfold RecM.prims
    change EStateM.Result.ok s.prims s = .ok p s
    rw [hprims]
  rw [hprimsRun]
  simp [haddr]
  simpa [show (NatSuccMode.collapse == NatSuccMode.stuck) = false from rfl] using hiter

/-! ### Semantic successor-loop closure -/

/-- Theory expression obtained by applying `Nat.succ` `offset` times.  The
successor loop's concrete state stores the inner expression and this offset
separately; this function is their ghost semantic reconstruction. -/
def natSuccIterV : Nat → VExpr → VExpr
  | 0, value => value
  | offset + 1, value => .app .natSucc (natSuccIterV offset value)

@[simp] theorem natSuccIterV_zero (value : VExpr) :
    natSuccIterV 0 value = value := rfl

@[simp] theorem natSuccIterV_succ (offset : Nat) (value : VExpr) :
    natSuccIterV (offset + 1) value =
      .app .natSucc (natSuccIterV offset value) := rfl

/-- Peeling one concrete successor and incrementing the ghost offset are the
same Theory expression. -/
theorem natSuccIterV_peel (offset : Nat) (value : VExpr) :
    natSuccIterV offset (.app .natSucc value) =
      natSuccIterV (offset + 1) value := by
  induction offset with
  | zero => rfl
  | succ offset ih =>
      simp only [natSuccIterV_succ, ih]

/-- Reconstructed successors over a numeral are exactly addition by the
stored offset. -/
theorem natSuccIterV_natLit (offset n : Nat) :
    natSuccIterV offset (.natLit n) = .natLit (n + offset) := by
  induction offset with
  | zero => simp
  | succ offset ih =>
      rw [natSuccIterV_succ, ih, Nat.add_succ]
      rfl

/-- The catalog entry selected by the production successor address has the
canonical Theory type `Nat → Nat`. -/
theorem natSucc_hasType
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {prims : Primitives .anon}
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives) :
    world.venv.HasType uvars Delta.toCtx .natSucc
      (.forallE .nat .nat) := by
  obtain ⟨ci, hlookup⟩ := htable.natSucc.contains hcatalog
  have hci := hprims.natSucc hlookup
  subst ci
  exact Lean4Lean.VEnv.HasType.const hlookup (by simp) rfl

/-- Successor reconstruction preserves the canonical Nat type. -/
theorem natSuccIterV_hasType
    {env : Lean4Lean.VEnv} {uvars : Nat} {Gamma : List VExpr}
    (hsucc : env.HasType uvars Gamma .natSucc (.forallE .nat .nat))
    {value : VExpr} (hvalue : env.HasType uvars Gamma value .nat)
    (offset : Nat) :
    env.HasType uvars Gamma (natSuccIterV offset value) .nat := by
  induction offset with
  | zero => exact hvalue
  | succ offset ih => exact Lean4Lean.VEnv.HasType.app hsucc ih

/-- Definitional equality of the current inner Nat lifts through every
successor already represented by the loop offset. -/
theorem natSuccIterV_congr
    {env : Lean4Lean.VEnv} (henv : env.WF)
    {uvars : Nat} {Gamma : List VExpr}
    (hGamma : Lean4Lean.OnCtx Gamma (env.IsType uvars))
    (hsucc : env.HasType uvars Gamma .natSucc (.forallE .nat .nat))
    {left right : VExpr}
    (hleft : env.HasType uvars Gamma left .nat)
    (heq : env.IsDefEqU uvars Gamma left right)
    (offset : Nat) :
    env.IsDefEqU uvars Gamma
      (natSuccIterV offset left) (natSuccIterV offset right) := by
  induction offset with
  | zero => exact heq
  | succ offset ih =>
      have hleftIter := natSuccIterV_hasType hsucc hleft offset
      have hi := ih.of_l henv hGamma hleftIter
      exact (hsucc.appDF hi).toU

/-- Exact one-argument successor spine accepted by `isNatSuccSpine`. -/
def NatSuccSpine (prims : Primitives .anon)
    (source cur : KExpr .anon) : Prop :=
  ∃ id us info,
    source.collectSpine = (.const id us info, #[cur]) ∧
      id.addr = prims.natSucc.addr

/-- The successor classifier is a state-transparent read, and every positive
answer exposes the exact concrete spine that caused it. -/
theorem isNatSuccSpine_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    (source : KExpr .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isNatSuccSpine source)
      (fun answer after => after = s ∧
        (answer = true → ∃ cur, NatSuccSpine s.prims source cur)) := by
  unfold isNatSuccSpine
  generalize hspine : source.collectSpine = spine
  cases spine with
  | mk head args =>
    cases head with
    | const id us info =>
        apply RecM.WF.bind (prims_wf (s := s))
        intro prims after hread
        rcases hread with ⟨hprims, hafter⟩
        apply RecM.WF.pure
        intro _
        constructor
        · exact hafter
        · intro htrue
          simp only [Bool.and_eq_true] at htrue
          have haddr : id.addr = prims.natSucc.addr :=
            beq_iff_eq.mp htrue.1
          have hsize : args.size = 1 := beq_iff_eq.mp htrue.2
          obtain ⟨cur, hargs⟩ := Array.size_eq_one_iff.mp hsize
          exact ⟨cur, id, us, info,
            hspine.trans
              (congrArg (fun a => (KExpr.const id us info, a)) hargs),
            haddr.trans (congrArg (fun p : Primitives .anon =>
              p.natSucc.addr) hprims)⟩
    | var idx name info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | fvar id name info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | sort u info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | app f a info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | lam name bi ty body info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | all name bi ty body info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | letE name ty val body nondep info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | prj id field val info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | nat value blob info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩
    | str value blob info =>
        apply RecM.WF.pure
        intro _
        exact ⟨rfl, by simp⟩

/-- Singleton inversion for the typed application-spine view. -/
theorem trAppSpine_singleton
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx} {head arg : KExpr .anon}
    {resultV : VExpr}
    (h : TrAppSpine env uvars nameOf trProj Delta head [arg] resultV) :
    ∃ headV argV A B,
      resultV = .app headV argV ∧
      TrKExprS env uvars nameOf trProj Delta head headV ∧
      env.HasType uvars Delta.toCtx headV (.forallE A B) ∧
      env.HasType uvars Delta.toCtx argV A ∧
      TrKExprS env uvars nameOf trProj Delta arg argV := by
  generalize hargs : [arg] = args at h
  cases h with
  | head hhead => simp at hargs
  | @app args fV arg' argV A B hprefix hfun harg htr =>
      have hshape : args = [] ∧ arg' = arg := by
        have hsingleton := List.append_eq_singleton_iff.mp hargs.symm
        rcases hsingleton with ⟨hargs, harg'⟩ | ⟨_, himpossible⟩
        · exact ⟨hargs, List.singleton_inj.mp harg'⟩
        · simp at himpossible
      rcases hshape with ⟨rfl, rfl⟩
      have hhead : TrKExprS env uvars nameOf trProj Delta head fV := by
        simpa using hprefix.tr
      exact ⟨fV, argV, A, B, rfl, hhead, hfun, harg, htr⟩

/-- A translated concrete successor spine exposes a translated, Nat-typed
inner expression and the canonical Theory successor application. -/
theorem natSuccSpine_tr
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx} {prims : Primitives .anon}
    {source cur : KExpr .anon} {sourceV : VExpr}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hcatalog : TrustedCatalogRel trProj world)
    (htable : NoDeltaPrimitiveTableAgrees world prims)
    (hprims : world.venv.HasPrimitives)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : NatSuccSpine prims source cur) :
    ∃ curV,
      TrKExprS world.venv uvars world.nameOf trProj Delta cur curV ∧
        world.venv.HasType uvars Delta.toCtx curV .nat ∧
        sourceV = .app .natSucc curV := by
  obtain ⟨id, us, info, hcollect, haddr⟩ := hspine
  have hview := trAppSpine_of_collectSpine hsource hcollect
  change TrAppSpine world.venv uvars world.nameOf trProj Delta
    (.const id us info) [cur] sourceV at hview
  obtain ⟨headV, curV, A, B, rfl, hhead, hfun, harg, hcur⟩ :=
    trAppSpine_singleton hview
  let .const (c := c) (ci := ci) hname hlookup hunivs hsize := hhead
  have hc : c = ``Nat.succ := by
    rw [haddr, htable.natSucc.2] at hname
    exact Option.some.inj hname.symm
  subst c
  have hci := hprims.natSucc hlookup
  subst ci
  have hus : us = #[] := Array.eq_empty_of_size_eq_zero hsize
  subst us
  have hsucc := natSucc_hasType (uvars := uvars) (Delta := Delta)
    hcatalog htable hprims
  have htypes := hfun.uniqU world.venvWF hDelta.toCtx hsucc
  obtain ⟨⟨_, hdomain⟩, _⟩ :=
    htypes.forallE_inv world.venvWF hDelta.toCtx
  have hargNat := Lean4Lean.VEnv.HasType.defeqU_r
    world.venvWF hDelta.toCtx
    ⟨_, hdomain⟩ harg
  exact ⟨curV, hcur, hargNat, rfl⟩

/-- Authorization boundary for the negative successor memo.  The second
context-key component is irrelevant to soundness because a marker suppresses
only an optional optimization; its source address, support, references, and
semantic cache family remain fully certified. -/
structure NatSuccStuckWriteOracle (semantics : CacheSemantics)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  authorize : ∀ {source : KExpr .anon} {key : Address × Address},
    support source → key.1 = source.addr →
    CacheProvenance semantics (CacheAuthority.stable world) support
      (.natSuccStuck key)

namespace NatSuccStuckWriteOracle

/-- Construct the marker oracle for K1's WHNF semantic overlay once every
finite-support expression is known to reference trusted declarations. -/
theorem forWhnfCache
    {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {world : VerifyWorld}
    {support : RunSupport}
    (hreferences : ∀ {source : KExpr .anon} {id : KId .anon},
      support source → source.References id → world.trusted id) :
    NatSuccStuckWriteOracle (whnfCacheSemantics keys trProj fallback)
      world support := by
  constructor
  intro source key hsource haddr
  apply CacheProvenance.whnfNatSuccStuck
  · exact ⟨source, hsource, haddr.symm⟩
  · intro id href
    obtain ⟨found, hfound, _, hfoundRef⟩ := href
    exact hreferences hfound hfoundRef

end NatSuccStuckWriteOracle

/-- Every marker accumulated by the current successor-loop execution already
has the exact provenance required by a later bulk commit. -/
def NatSuccVisited (semantics : CacheSemantics) (world : VerifyWorld)
    (support : RunSupport) (visited : Array (Address × Address)) : Prop :=
  ∀ key ∈ visited,
    CacheProvenance semantics (CacheAuthority.stable world) support
      (.natSuccStuck key)

/-! ### Linear Nat-recognizer semantic boundary -/

/-- Structural fact retained by a successful `natRecLiteralParts` lookup.
The descriptor controls the returned indices, but the spine itself must be
the production spine of the expression being inspected. -/
def NatRecLiteralPartsPost (source : KExpr .anon) :
    Option (NatRecLiteralParts .anon) → Prop
  | none => True
  | some parts => source.collectSpine.2 = parts.spine

/-- State-safety contract for the descriptor lookup inside the linear Nat
recognizer.  This is deliberately separated from Nat.rec semantics: its only
nontrivial effect is the driver's lazy `tryGetConst` ingress. -/
def NatRecLiteralPartsPreserves (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ {uvars : Nat} {Delta : KVLCtx} {source : KExpr .anon}
      {s : TcState .anon},
    RecM.WF layer semantics trProj world support uvars Delta s
      (natRecLiteralParts source)
      (fun result _ => NatRecLiteralPartsPost source result)

/-- A successful linear-recognition run has exactly one remaining semantic
claim: the numeral it returned denotes the successor-offset reconstruction
of the original Nat.  State preservation, callback closure, misses, and
partial errors are not part of this boundary. -/
structure NatSuccLinearReflection (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx} {cur reduced : KExpr .anon}
      {curV : VExpr} {offset : Nat} {s after : TcState .anon}
      {methods : Methods .anon},
    support cur →
    TrKExprS world.venv uvars world.nameOf trProj Delta cur curV →
    world.venv.HasType uvars Delta.toCtx curV .nat →
    Methods.WFAt layer semantics trProj world support uvars methods →
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    (tryReduceNatSuccLinearRec cur offset).run methods s =
      .ok (some reduced) after →
    ∃ reducedV,
      TrKExprS world.venv uvars world.nameOf trProj Delta reduced reducedV ∧
        world.venv.IsDefEqU uvars Delta.toCtx
          (natSuccIterV offset curV) reducedV

/-- The syntactic step recognizer preserves K1 state through its sole
recursive WHNF callback.  All later lambda/spine/address tests and primitive
reads are state-transparent. -/
theorem isNatSuccIhStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {step : KExpr .anon}
    {stepV : VExpr} {s : TcState .anon}
    (hstep : support step)
    (hstepTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      step stepV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isNatSuccIhStep step) (fun _ _ => True) := by
  unfold isNatSuccIhStep
  apply RecM.WF.bind (whnfRec_wf hstep hstepTr)
  intro reduced after hcallback
  cases reduced <;> simp only
  all_goals try exact RecM.WF.pure (fun _ => trivial)
  case lam name bi ty body info =>
    cases body <;> simp only
    all_goals try exact RecM.WF.pure (fun _ => trivial)
    case lam name' bi' ty' body info' =>
      generalize hspine : body.collectSpine = spine
      rcases spine with ⟨head, args⟩
      cases head <;> simp only
      all_goals try exact RecM.WF.pure (fun _ => trivial)
      case const id us info =>
        apply RecM.WF.bind (prims_wf (s := after))
        intro prims afterRead _
        split
        · exact RecM.WF.pure fun _ => trivial
        · generalize harg : args[0]! = arg
          cases arg
          all_goals try exact RecM.WF.pure (fun _ => trivial)
          case var idx name info =>
            split <;> exact RecM.WF.pure fun _ => trivial

/-- Once descriptor lookup preserves the invariant, the complete linear
recognizer preserves it too.  The proof obtains support and translation for
the runtime-selected base and step positions from the original typed spine,
then uses the ordinary recursive-method contracts for both callbacks. -/
theorem tryReduceNatSuccLinearRec_effect_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (partsPreserve : NatRecLiteralPartsPreserves layer semantics trProj
      world support)
    {uvars : Nat} {Delta : KVLCtx} {cur : KExpr .anon}
    {curV : VExpr} {offset : Nat} {s : TcState .anon}
    (hcur : support cur)
    (hcurTr : TrKExprS world.venv uvars world.nameOf trProj Delta cur curV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryReduceNatSuccLinearRec cur offset) (fun _ _ => True) := by
  unfold tryReduceNatSuccLinearRec
  apply RecM.WF.bind (partsPreserve (source := cur) (s := s))
  intro found afterParts hparts
  cases found with
  | none =>
      simp only
      exact RecM.WF.pure fun _ => trivial
  | some parts =>
      simp only
      change cur.collectSpine.2 = parts.spine at hparts
      have hspineSupport := context.inputs.spine hcur
        (show cur.collectSpine =
          (cur.collectSpine.1, cur.collectSpine.2) from rfl)
      have hspineTr := trAppSpine_of_collectSpine hcurTr
        (show cur.collectSpine =
          (cur.collectSpine.1, cur.collectSpine.2) from rfl)
      cases hbase : parts.spine[parts.baseIdx]? with
      | none =>
          exact RecM.WF.pure fun _ => trivial
      | some base =>
          obtain ⟨hbaseIdx, hbaseAt⟩ := getElem?_eq_some_iff.mp hbase
          have hbaseSupport : support base := by
            have := hspineSupport.2 parts.baseIdx (by
              simpa only [← hparts] using hbaseIdx)
            simpa only [hparts, hbaseAt] using this
          obtain ⟨baseV, baseType, hbaseType, hbaseTr⟩ :=
            hspineTr.argument (arg := base) (by
              rw [hparts]
              exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hbase))
          cases hstep : parts.spine[parts.stepIdx]? with
          | none =>
              exact RecM.WF.pure fun _ => trivial
          | some step =>
              obtain ⟨hstepIdx, hstepAt⟩ := getElem?_eq_some_iff.mp hstep
              have hstepSupport : support step := by
                have := hspineSupport.2 parts.stepIdx (by
                  simpa only [← hparts] using hstepIdx)
                simpa only [hparts, hstepAt] using this
              obtain ⟨stepV, stepType, hstepType, hstepTr⟩ :=
                hspineTr.argument (arg := step) (by
                  rw [hparts]
                  exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hstep))
              apply RecM.WF.bind
                (isNatSuccIhStep_wf hstepSupport hstepTr)
              intro accepted afterStep _
              cases accepted with
              | false =>
                  exact RecM.WF.pure fun _ => trivial
              | true =>
                  apply RecM.WF.bind (whnfRec_wf hbaseSupport hbaseTr)
                  intro baseWhnf afterBase _
                  apply RecM.WF.bind (prims_wf (s := afterBase))
                  intro prims afterRead _
                  cases hextract : extractNatValue baseWhnf prims with
                  | none =>
                      cases hsize :
                          parts.spine.size != parts.majorIdx + 1 with
                      | true =>
                          simp only [if_true]
                          exact RecM.WF.pure fun _ => trivial
                      | false =>
                          simp only [Bool.false_eq_true, if_false, pure_bind]
                          have hadd : RecM.WF layer semantics trProj world
                              support uvars Delta afterRead
                              (mkNatAdd baseWhnf
                                (natExprFromValue (parts.major + offset)))
                              (fun _ _ => True) := by
                            unfold mkNatAdd
                            apply RecM.WF.bind (prims_wf (s := afterRead))
                            intro _ _ _
                            exact RecM.WF.pure fun _ => trivial
                          apply RecM.WF.bind hadd
                          intro _ _ _
                          exact RecM.WF.pure fun _ => trivial
                  | some baseVal =>
                      exact RecM.WF.pure fun _ => trivial

/-- Compatibility form consumed by the successor-loop proof.  The preceding
recognizer decomposition derives this whole-computation contract from
separately audited operational effects and a success-only Nat.rec reflection
law. -/
structure NatSuccLinearOracle (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  reduce : ∀ {uvars : Nat} {Delta : KVLCtx} {cur : KExpr .anon}
      {curV : VExpr} {offset : Nat} {s : TcState .anon},
    support cur →
    TrKExprS world.venv uvars world.nameOf trProj Delta cur curV →
    world.venv.HasType uvars Delta.toCtx curV .nat →
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryReduceNatSuccLinearRec cur offset)
      (fun result _ => match result with
        | none => True
        | some reduced => ∃ reducedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta
              reduced reducedV ∧
            world.venv.IsDefEqU uvars Delta.toCtx
              (natSuccIterV offset curV) reducedV)

namespace NatSuccLinearOracle

/-- Construct the compatibility oracle from the proved operational effect
theorem and the one success-only Nat.rec reflection law. -/
theorem of_reflection
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (partsPreserve : NatRecLiteralPartsPreserves layer semantics trProj
      world support)
    (reflection : NatSuccLinearReflection layer semantics trProj world
      support) :
    NatSuccLinearOracle layer semantics trProj world support := by
  constructor
  intro uvars Delta cur curV offset s hcur hcurTr hcurType
  have heffect := tryReduceNatSuccLinearRec_effect_wf context partsPreserve
    (offset := offset) (s := s) hcur hcurTr
  intro methods hmethods hI
  have hpost := heffect methods hmethods hI
  match hrun : (tryReduceNatSuccLinearRec cur offset).run methods s with
  | .error err after =>
      rw [hrun] at hpost
      exact hpost
  | .ok result after =>
      rw [hrun] at hpost
      cases result with
      | none => exact ⟨hpost.1, trivial⟩
      | some reduced =>
          exact ⟨hpost.1,
            reflection.success hcur hcurTr hcurType hmethods hI hrun⟩

end NatSuccLinearOracle

/-- Ghost invariant carried by the actual bounded successor loop.  It ties
the original source translation to the current inner expression plus offset,
and retains provenance for every key that either stuck exit may commit. -/
def NatSuccLoopState (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (sourceV : VExpr)
    (cur : KExpr .anon) (offset : Nat)
    (visited : Array (Address × Address)) : Prop :=
  ∃ curV,
    support cur ∧
    TrKExprS world.venv uvars world.nameOf trProj Delta cur curV ∧
    world.venv.HasType uvars Delta.toCtx curV .nat ∧
    world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV offset curV) ∧
    NatSuccVisited semantics world support visited

/-- Semantic postcondition of the bounded loop before the outer concrete
source translation is reattached as `WhnfMeaning`. -/
def NatSuccLoopResult (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (sourceV : VExpr) :
    Option (KExpr .anon) → Prop
  | none => True
  | some reduced => ∃ reducedV,
      TrKExprS world.venv uvars world.nameOf trProj Delta reduced reducedV ∧
      world.venv.IsDefEqU uvars Delta.toCtx sourceV reducedV

/-- Uniform semantic postcondition for one concrete successor-loop action. -/
def NatSuccLoopAction (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (sourceV : VExpr) :
    BoundedStep (KExpr .anon × Nat × Array (Address × Address))
      (Option (KExpr .anon)) → Prop
  | .next (cur, offset, visited) =>
      NatSuccLoopState semantics trProj world support uvars Delta sourceV
        cur offset visited
  | .done result => NatSuccLoopResult trProj world uvars Delta sourceV result

/-- On a peeled-key miss, the second key is certified and both new markers
extend the loop provenance before the next state is returned. -/
theorem tryReduceNatSuccPeelMiss_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (writes : NatSuccStuckWriteOracle semantics world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {sourceV curV : VExpr} {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    {curKey : Address × Address}
    (hw : support w) (hcur : support cur)
    (hcurTr : TrKExprS world.venv uvars world.nameOf trProj Delta cur curV)
    (hcurType : world.venv.HasType uvars Delta.toCtx curV .nat)
    (hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV (offset + 1) curV))
    (hvisited : NatSuccVisited semantics world support visited)
    (hcurKey : curKey.1 = cur.addr) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccPeelMiss w cur offset visited curKey)
      (fun action _ => NatSuccLoopAction semantics trProj world support
        uvars Delta sourceV action) := by
  unfold tryReduceNatSuccPeelMiss
  apply RecM.WF.bind
    (Q₁ := fun key after => key.1 = w.addr ∧ ContextKeyFrame s after)
    (RecM.WF.liftTcM
      (TcM.whnfKey_wf (layer := .noAccel) (semantics := semantics)
        (trProj := trProj) (world := world) (support := support)
        (uvars := uvars) (Δ := Delta) (source := w) (s := s)))
  intro wKey after hwKey
  apply RecM.WF.pure
  intro _
  refine ⟨curV, hcur, hcurTr, hcurType, hsourceEq, ?_⟩
  intro key hmem
  simp only [Array.mem_push] at hmem
  rcases hmem with (hmem | hkey) | hkey
  · exact hvisited key hmem
  · subst key
    exact writes.authorize hcur hcurKey
  · subst key
    exact writes.authorize hw hwKey.1

/-- A peeled key hit safely commits the old trace; a miss delegates to the
second-key path while retaining the strengthened semantic state. -/
theorem tryReduceNatSuccPeelAfterKey_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (writes : NatSuccStuckWriteOracle semantics world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {sourceV curV : VExpr} {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    {curKey : Address × Address}
    (hw : support w) (hcur : support cur)
    (hcurTr : TrKExprS world.venv uvars world.nameOf trProj Delta cur curV)
    (hcurType : world.venv.HasType uvars Delta.toCtx curV .nat)
    (hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV (offset + 1) curV))
    (hvisited : NatSuccVisited semantics world support visited)
    (hcurKey : curKey.1 = cur.addr) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccPeelAfterKey w cur offset visited curKey)
      (fun action _ => NatSuccLoopAction semantics trProj world support
        uvars Delta sourceV action) := by
  unfold tryReduceNatSuccPeelAfterKey
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = s ∧ after = s)
    (RecM.WF.get (s := s) fun _ => ⟨rfl, rfl⟩)
  rintro observed after ⟨rfl, rfl⟩
  split
  · apply RecM.WF.bind (recordNatSuccStuck_wf visited hvisited)
    intro _ after _
    exact RecM.WF.pure fun _ => trivial
  · exact tryReduceNatSuccPeelMiss_wf writes hw hcur hcurTr
      hcurType hsourceEq hvisited hcurKey

/-- The first peeled key is state-framed and its source address is retained
for either the hit or miss branch. -/
theorem tryReduceNatSuccPeel_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (writes : NatSuccStuckWriteOracle semantics world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {sourceV curV : VExpr} {w cur : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    (hw : support w) (hcur : support cur)
    (hcurTr : TrKExprS world.venv uvars world.nameOf trProj Delta cur curV)
    (hcurType : world.venv.HasType uvars Delta.toCtx curV .nat)
    (hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV (offset + 1) curV))
    (hvisited : NatSuccVisited semantics world support visited) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccPeel w cur offset visited)
      (fun action _ => NatSuccLoopAction semantics trProj world support
        uvars Delta sourceV action) := by
  unfold tryReduceNatSuccPeel
  apply RecM.WF.bind
    (Q₁ := fun key after => key.1 = cur.addr ∧ ContextKeyFrame s after)
    (RecM.WF.liftTcM
      (TcM.whnfKey_wf (layer := .noAccel) (semantics := semantics)
        (trProj := trProj) (world := world) (support := support)
        (uvars := uvars) (Δ := Delta) (source := cur) (s := s)))
  intro curKey after hkey
  exact tryReduceNatSuccPeelAfterKey_wf writes hw hcur hcurTr
    hcurType hsourceEq hvisited hkey.1

/-- Literal, successor, and stuck classification after recursive WHNF all
preserve the loop invariant. A successor peel uses typing uniqueness to
recover the next inner Nat before incrementing the ghost offset. -/
theorem tryReduceNatSuccAfterWhnf_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (writes : NatSuccStuckWriteOracle semantics world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {sourceV curV : VExpr} {w : KExpr .anon} {offset : Nat}
    {visited : Array (Address × Address)}
    (hw : support w)
    (hpost : WhnfPost trProj world uvars Delta curV w)
    (hcurType : world.venv.HasType uvars Delta.toCtx curV .nat)
    (hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV offset curV))
    (hvisited : NatSuccVisited semantics world support visited) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccAfterWhnf w offset visited)
      (fun action _ => NatSuccLoopAction semantics trProj world support
        uvars Delta sourceV action) := by
  unfold tryReduceNatSuccAfterWhnf
  apply RecM.WF.bind
    (Q₁ := fun p after =>
      WhnfStateInv .noAccel semantics trProj world support uvars Delta after ∧
      p = s.prims ∧ after = s)
    (RecM.WF.withInv (prims_wf (s := s)))
  rintro p after ⟨hI, hp, rfl⟩
  simp only
  split
  · rename_i n hextract
    apply RecM.WF.pure
    intro _
    have htable := context.stateTable hI
    have htableP : NoDeltaPrimitiveTableAgrees world p := by
      simpa only [hp] using htable
    have hsucc := natSucc_hasType (uvars := uvars) (Delta := Delta)
      hI.1.core.trustedCatalog htableP context.theoryPrimitives
    have hcurLit := hpost.of_extractNatLit htableP
      context.theoryPrimitives hextract
    have hlift := natSuccIterV_congr world.venvWF hI.2.1.wf.toCtx
      hsucc hcurType hcurLit offset
    refine ⟨_, TrKExprS.natExprFromValue hI.1.core.trustedCatalog
      htableP (n + offset), ?_⟩
    exact hsourceEq.trans world.venvWF hI.2.1.wf <| by
      simpa only [natSuccIterV_natLit] using hlift
  · rename_i hextract
    generalize hcollect : w.collectSpine = spine
    cases spine with
    | mk head args =>
      apply RecM.WF.bind
        (Q₁ := fun answer classified =>
          WhnfStateInv .noAccel semantics trProj world support uvars Delta
              classified ∧
            classified = after ∧
            (answer = true → ∃ cur, NatSuccSpine after.prims w cur))
        (RecM.WF.withInv (isNatSuccSpine_wf (s := after) w))
      rintro answer classified ⟨hClassI, rfl, hclass⟩
      split
      · rename_i htrue
        obtain ⟨cur, hspine⟩ := hclass htrue
        obtain ⟨wV, hwTr, hcurW⟩ := hpost
        have htable := context.stateTable hClassI
        obtain ⟨nextV, hnextTr, hnextType, hwV⟩ :=
          natSuccSpine_tr hClassI.2.1.wf
            hClassI.1.core.trustedCatalog htable
            context.theoryPrimitives hwTr hspine
        obtain ⟨id, us, info, hnextSpine, haddr⟩ := hspine
        have hnext := (context.inputs.spine hw hnextSpine).2 0 (by simp)
        have hargs : args = #[cur] := congrArg Prod.snd
          (hcollect.symm.trans hnextSpine)
        have hcurAt : args[0]! = cur := by simp [hargs]
        have hsucc := natSucc_hasType (uvars := uvars) (Delta := Delta)
          hClassI.1.core.trustedCatalog htable context.theoryPrimitives
        have hlift := natSuccIterV_congr world.venvWF
          hClassI.2.1.wf.toCtx hsucc hcurType hcurW offset
        have hnextEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
            (natSuccIterV (offset + 1) nextV) :=
          hsourceEq.trans world.venvWF hClassI.2.1.wf <| by
            rw [hwV, natSuccIterV_peel] at hlift
            exact hlift
        rw [hcurAt]
        exact tryReduceNatSuccPeel_wf writes hw hnext hnextTr
          hnextType hnextEq hvisited
      · apply RecM.WF.bind (recordNatSuccStuck_wf visited hvisited)
        intro _ committed _
        exact RecM.WF.pure fun _ => trivial

/-- One actual successor-loop iteration satisfies the ghost action contract.
Linear recognition has precedence; on a miss, recursive stuck-mode WHNF and
the complete post-WHNF classifier preserve the same source meaning. -/
theorem tryReduceNatSuccIterStep_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (linear : NatSuccLinearOracle .noAccel semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {sourceV : VExpr}
    (state : KExpr .anon × Nat × Array (Address × Address))
    (s : TcState .anon)
    (hstate : NatSuccLoopState semantics trProj world support uvars Delta
      sourceV state.1 state.2.1 state.2.2) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccIterStep state)
      (fun action _ => NatSuccLoopAction semantics trProj world support
        uvars Delta sourceV action) := by
  rcases state with ⟨cur, offset, visited⟩
  obtain ⟨curV, hcur, hcurTr, hcurType, hsourceEq, hvisited⟩ := hstate
  unfold tryReduceNatSuccIterStep
  apply RecM.WF.bind (linear.reduce hcur hcurTr hcurType)
  intro result after hlinear
  cases result with
  | some reduced =>
      apply RecM.WF.pure
      intro hI
      obtain ⟨reducedV, hreducedTr, hreducedEq⟩ := hlinear
      exact ⟨reducedV, hreducedTr,
        hsourceEq.trans world.venvWF hI.2.1.wf hreducedEq⟩
  | none =>
      simp only [pure_bind]
      apply RecM.WF.bind (whnfModeRec_wf hcur hcurTr)
      intro w afterWhnf hwhnf
      exact tryReduceNatSuccAfterWhnf_wf context writes hwhnf.1
        hwhnf.2 hcurType hsourceEq hvisited

/-- The public successor-collapse helper satisfies its semantic result
contract for arbitrary successor chains. The entry memo hit is a safe miss;
the miss path seeds certified provenance and invokes the generic bounded-loop
driver, whose exhaustion and callback errors still preserve K1 state. -/
theorem tryReduceNatSuccIter_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (linear : NatSuccLinearOracle .noAccel semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {sourceV argV : VExpr} {arg : KExpr .anon}
    (harg : support arg)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
    (hargType : world.venv.HasType uvars Delta.toCtx argV .nat)
    (hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV 1 argV)) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatSuccIter arg)
      (fun result _ =>
        NatSuccLoopResult trProj world uvars Delta sourceV result) := by
  unfold tryReduceNatSuccIter
  apply RecM.WF.bind
    (Q₁ := fun key after => key.1 = arg.addr ∧ ContextKeyFrame s after)
    (RecM.WF.liftTcM
      (TcM.whnfKey_wf (layer := .noAccel) (semantics := semantics)
        (trProj := trProj) (world := world) (support := support)
        (uvars := uvars) (Δ := Delta) (source := arg) (s := s)))
  intro entryKey afterKey hkey
  apply RecM.WF.bind
    (Q₁ := fun observed after => observed = afterKey ∧ after = afterKey)
    (RecM.WF.get (s := afterKey) fun _ => ⟨rfl, rfl⟩)
  rintro observed afterGet ⟨rfl, rfl⟩
  split
  · exact RecM.WF.pure fun _ => trivial
  · apply runBounded_wf
      (P := fun state => NatSuccLoopState semantics trProj world support
        uvars Delta sourceV state.1 state.2.1 state.2.2)
      (Q := fun result _ =>
        NatSuccLoopResult trProj world uvars Delta sourceV result)
      (E := fun _ _ => True)
    · intro state loopState hloop
      apply RecM.WF.mono
        (tryReduceNatSuccIterStep_wf context writes linear
          state loopState hloop)
      · intro action after haction
        cases action with
        | next next =>
            rcases next with ⟨cur, offset, visited⟩
            exact haction
        | done result => exact haction
      · intro err after _
        trivial
    · intro exhausted hI
      trivial
    · exact ⟨argV, harg, hargTr, hargType, hsourceEq, by
        intro key hmem
        simp only [Array.mem_singleton] at hmem
        subst key
        exact writes.authorize harg hkey.1⟩

/-! ### Outer and uniform Nat-dispatch closure -/

/-- The production Nat dispatcher preserves optional-reduction semantics on
an exact one-argument `Nat.succ` spine in collapse mode.  Successful support
is recovered from the actual outer execution rather than assumed for the
inner loop result; absent results and partial-error states retain the loop's
full `RecM.WF` invariant. -/
theorem tryReduceNatWithSuccMode_succ_optional_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (linear : NatSuccLinearOracle .noAccel semantics trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source arg : KExpr .anon} {sourceV : VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source sourceV)
    (hspine : NatSuccSpine s.prims source arg) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (tryReduceNatWithSuccMode source .collapse)
      (fun result _ => match result with
        | none => True
        | some reduced =>
            support reduced ∧
              WhnfMeaning trProj world uvars Delta source reduced) := by
  intro methods hmethods hI
  have hspineData := hspine
  obtain ⟨id, us, info, hcollect, haddr⟩ := hspineData
  have htable := context.stateTable hI
  obtain ⟨argV, hargTr, hargType, hsourceV⟩ :=
    natSuccSpine_tr (source := source) (cur := arg)
      hI.2.1.wf hI.1.core.trustedCatalog htable
      context.theoryPrimitives hsource hspine
  have hargSupport : support arg := by
    simpa using (context.inputs.spine hsourceSupport hcollect).2 0 (by simp)
  have hsucc := natSucc_hasType (uvars := uvars) (Delta := Delta)
    hI.1.core.trustedCatalog htable context.theoryPrimitives
  have happType : world.venv.HasType uvars Delta.toCtx
      (.app .natSucc argV) .nat :=
    Lean4Lean.VEnv.HasType.app hsucc hargType
  have hsourceEq : world.venv.IsDefEqU uvars Delta.toCtx sourceV
      (natSuccIterV 1 argV) := by
    rw [hsourceV]
    simpa only [natSuccIterV_succ, natSuccIterV_zero] using
      (show world.venv.IsDefEqU uvars Delta.toCtx
        (.app .natSucc argV) (.app .natSucc argV) from ⟨_, happType⟩)
  have hinnerWF := tryReduceNatSuccIter_wf context writes linear
    hargSupport hargTr hargType hsourceEq methods hmethods hI
  match hinner : (tryReduceNatSuccIter arg).run methods s with
  | .error err after =>
      rw [hinner] at hinnerWF
      have houter := tryReduceNatWithSuccMode_succ_collapse hcollect rfl
        haddr hinner
      rw [houter]
      exact hinnerWF
  | .ok result after =>
      rw [hinner] at hinnerWF
      have houter := tryReduceNatWithSuccMode_succ_collapse hcollect rfl
        haddr hinner
      rw [houter]
      cases result with
      | none => exact hinnerWF
      | some reduced =>
          obtain ⟨reducedV, hreducedTr, hreducedEq⟩ := hinnerWF.2
          exact ⟨hinnerWF.1,
            context.generated.nat hsourceSupport houter,
            sourceV, reducedV, hsource, hreducedTr, hreducedEq⟩

/-- Every array of at least two arguments is its binary prefix followed by
the exact production suffix consumed by `finishAppResult`. -/
theorem natArgs_eq_binaryPrefix_append_extract
    {args : Array (KExpr .anon)} (hsize : 2 ≤ args.size) :
    args = #[args[0], args[1]] ++ args.extract 2 args.size := by
  have hprefix : args.extract 0 2 = #[args[0], args[1]] := by
    apply Array.ext
    · simp [Array.size_extract]
      omega
    · intro i hi hi'
      have hiCases : i = 0 ∨ i = 1 := by
        simp at hi'
        omega
      rcases hiCases with hzero | hone
      · subst i
        simp [Array.getElem_extract]
      · subst i
        simp [Array.getElem_extract]
  calc
    args = args.extract 0 args.size := by simp
    _ = args.extract 0 2 ++ args.extract 2 args.size := by
      rw [Array.extract_append_extract]
      rw [Nat.max_eq_right hsize]
      rfl
    _ = #[args[0], args[1]] ++ args.extract 2 args.size := by rw [hprefix]

/-- Finite suffix-rebuild coverage for every supported binary-or-longer Nat
dispatcher entry.  This is the global assembly form of the fixed-entry
certificate: it remains scoped to the finite run support and to successful
traces actually possible under a well-formed method table. -/
def NatCollapseFinishCoverage (requests : List WalkerRequest)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ {uvars : Nat} {source : KExpr .anon} {headId : KId .anon}
      {us : Array (KUniv .anon)} {headInfo : ExprInfo .anon}
      {args suffix : Array (KExpr .anon)} {argA argB : KExpr .anon}
      {s : TcState .anon},
    support source →
    source.collectSpine = (.const headId us headInfo, args) →
    args = #[argA, argB] ++ suffix → ∀ methods,
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    NatSpineFinishCoverage requests methods .collapse source headId us
      headInfo args argA argB s

/-! ### Uniform Nat closure for both successor policies -/

/-- In stuck-successor mode every constant-headed spine shorter than two
arguments is an exact state-transparent miss.  This includes the canonical
one-argument `Nat.succ` case, which is deliberately reserved for the outer
successor loop. -/
theorem tryReduceNatWithSuccMode_stuck_short
    {methods : Methods .anon} {s : TcState .anon}
    {source : KExpr .anon} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    (hspine : source.collectSpine = (.const id us info, args))
    (hshort : args.size < 2) :
    (tryReduceNatWithSuccMode source .stuck).run methods s = .ok none s := by
  unfold tryReduceNatWithSuccMode
  rw [hspine, ReaderT.run_bind]
  change EStateM.bind (RecM.prims.run methods) _ s = _
  unfold EStateM.bind
  rw [show RecM.prims.run methods s = .ok s.prims s from rfl]
  simp [hshort]
  split <;> rfl

/-- Exhaustive stuck-successor Nat optional-reduction contract.  The reserved
one-argument successor is a miss; every successful binary primitive uses the
same finite request census and deterministic replay as collapse mode. -/
theorem tryReduceNatWithSuccMode_stuck_optional_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .stuck)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (census : NatCollapseRequestCensus requests semantics trProj world
      support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source .stuck) := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  generalize hcollect : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us info =>
      by_cases hshort : args.size < 2
      · intro methods hmethods hI
        rw [tryReduceNatWithSuccMode_stuck_short hcollect hshort]
        exact ⟨hI, trivial⟩
      · have hsize : 2 ≤ args.size := by omega
        have hargs := natArgs_eq_binaryPrefix_append_extract hsize
        exact tryReduceNatWithSuccMode_spine_optional_wf context hrun
          (theory uvars) hsourceSupport hsource hcollect hargs
            (fun methods hmethods hI {_ _} trace =>
              NatCollapseRequestCensus.certify context hrun census
                hsourceSupport hsource hcollect hargs hmethods hI trace)
  | var idx name info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | fvar id name info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | sort u info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | app f a info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | lam name bi ty body info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | all name bi ty body info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | letE name ty val body nondep info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | prj id field val info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | nat value blob info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | str value blob info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .stuck).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩

/-- Exhaustive collapse-mode Nat optional-reduction contract.  Non-constant
heads and short non-successor spines are state-transparent misses, the exact
one-argument successor branch uses the verified bounded loop, and every
binary-or-longer spine is recovered from the finite suffix-request census by
deterministic replay. -/
theorem tryReduceNatWithSuccMode_collapse_optional_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (linear : NatSuccLinearOracle .noAccel semantics trProj world support)
    (census : NatCollapseRequestCensus requests semantics trProj world
      support) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source .collapse) := by
  intro uvars Delta source sourceV s hsourceSupport hsource
  generalize hcollect : source.collectSpine = spine
  rcases spine with ⟨head, args⟩
  cases head with
  | const id us info =>
      by_cases hsizeOne : args.size = 1
      · obtain ⟨arg, hargs⟩ := Array.size_eq_one_iff.mp hsizeOne
        subst args
        by_cases haddr : id.addr = s.prims.natSucc.addr
        · exact tryReduceNatWithSuccMode_succ_optional_wf context writes
            linear hsourceSupport hsource
              ⟨id, us, info, hcollect, haddr⟩
        · intro methods hmethods hI
          have hrun :
              (tryReduceNatWithSuccMode source .collapse).run methods s =
                .ok none s := by
            unfold tryReduceNatWithSuccMode
            rw [hcollect, ReaderT.run_bind]
            change EStateM.bind (RecM.prims.run methods) _ s = _
            unfold EStateM.bind
            have hprimsRun : RecM.prims.run methods s = .ok s.prims s := rfl
            rw [hprimsRun]
            simp [haddr]
            rfl
          rw [hrun]
          exact ⟨hI, trivial⟩
      · by_cases hshort : args.size < 2
        · intro methods hmethods hI
          have hrun :
              (tryReduceNatWithSuccMode source .collapse).run methods s =
                .ok none s := by
            unfold tryReduceNatWithSuccMode
            rw [hcollect, ReaderT.run_bind]
            change EStateM.bind (RecM.prims.run methods) _ s = _
            unfold EStateM.bind
            have hprimsRun : RecM.prims.run methods s = .ok s.prims s := rfl
            rw [hprimsRun]
            simp [hsizeOne, hshort]
            rfl
          rw [hrun]
          exact ⟨hI, trivial⟩
        · have hsize : 2 ≤ args.size := by omega
          have hargs := natArgs_eq_binaryPrefix_append_extract hsize
          exact tryReduceNatWithSuccMode_spine_optional_wf context hrun
            (theory uvars) hsourceSupport hsource hcollect hargs
              (fun methods hmethods hI {_ _} trace =>
                NatCollapseRequestCensus.certify context hrun census
                  hsourceSupport hsource hcollect hargs hmethods hI trace)
  | var idx name info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | fvar id name info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | sort u info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | app f a info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | lam name bi ty body info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | all name bi ty body info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | letE name ty val body nondep info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | prj id field val info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | nat value blob info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩
  | str value blob info =>
      intro methods hmethods hI
      have hrun : (tryReduceNatWithSuccMode source .collapse).run methods s =
          .ok none s := by
        unfold tryReduceNatWithSuccMode
        rw [hcollect]
        rfl
      rw [hrun]
      exact ⟨hI, trivial⟩

/-- K1's narrow collapse-mode Nat closure surface.  The implementation proof
constructs both former whole-computation assumptions: descriptor ingress
plus callback closure yield the linear recognizer's effect contract, while
successful callback meaning plus canonical result-shape separation yields an
empty suffix census.  What remains semantic is stated directly as Nat.rec
reflection and the `Nat`/`Bool`-versus-function Theory fact. -/
theorem tryReduceNatWithSuccMode_collapse_optional_wf_of_boundaries
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .collapse)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (partsPreserve : NatRecLiteralPartsPreserves .noAccel semantics trProj
      world support)
    (reflection : NatSuccLinearReflection .noAccel semantics trProj world
      support)
    (shape : NatCollapseRequestCensus.NatBoolResultShapeSeparation world) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source .collapse) :=
  tryReduceNatWithSuccMode_collapse_optional_wf context hrun theory writes
    (NatSuccLinearOracle.of_reflection context partsPreserve reflection)
    (NatCollapseRequestCensus.of_result_shape context theory shape)

/-- K1's stuck-mode Nat closure surface.  Unary `Nat.succ` is deliberately
reserved for the surrounding successor loop, so this mode needs neither the
linear Nat.rec reflection boundary nor stuck-cache writes.  Canonical
Nat/Bool result-shape separation is the only semantic boundary beyond the
common primitive context, callback contracts, and run certificate. -/
theorem tryReduceNatWithSuccMode_stuck_optional_wf_of_boundary
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : NoDeltaPrimitiveContext world support flags .stuck)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (shape : NatCollapseRequestCensus.NatBoolResultShapeSeparation world) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source .stuck) :=
  tryReduceNatWithSuccMode_stuck_optional_wf context hrun theory
    (NatCollapseRequestCensus.of_result_shape context theory shape)

/-- Uniform Nat field for both production successor policies.  Case analysis
on the finite policy type exposes that collapse mode alone consumes the
linear-recognizer and memo-write boundaries; both modes share the canonical
Nat/Bool result-shape theorem. -/
theorem tryReduceNatWithSuccMode_optional_wf_of_boundaries
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : ∀ mode,
      NoDeltaPrimitiveContext world support flags mode)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (partsPreserve : NatRecLiteralPartsPreserves .noAccel semantics trProj
      world support)
    (reflection : NatSuccLinearReflection .noAccel semantics trProj world
      support)
    (shape : NatCollapseRequestCensus.NatBoolResultShapeSeparation world)
    (mode : NatSuccMode) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source mode) := by
  cases mode with
  | collapse =>
      exact tryReduceNatWithSuccMode_collapse_optional_wf_of_boundaries
        (context .collapse) hrun theory writes partsPreserve reflection
        shape
  | stuck =>
      exact tryReduceNatWithSuccMode_stuck_optional_wf_of_boundary
        (context .stuck) hrun theory shape

end RecM

/-! Uniform semantic contract for the structural result consumed by the
no-delta reducer tail.  This is deliberately the production
`whnfCoreWithFlags`, not a method-table callback or an execution equation. -/
namespace StructuralReduction

def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Δ : KVLCtx) (flags : WhnfFlags) : Prop :=
  ∀ {source sourceV s},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Δ source sourceV →
    RecM.WF layer semantics trProj world support uvars Δ s
      (RecM.whnfCoreWithFlags source flags)
      (fun reduced _ =>
        support reduced ∧
          WhnfMeaning trProj world uvars Δ source reduced)

end StructuralReduction

/-- Exhaustive semantic boundary for the seven optional reducers in one
no-delta tail.  The fields mirror production order and distinguish the
full-only projection-wrapper stage from the unconditional quotient stage.
This is proof debt, not an axiom: primitive, projection, quotient, and native
verification must construct the corresponding fields. -/
structure NoDeltaReductionOracle (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (flags : WhnfFlags) (natSuccMode : NatSuccMode) : Prop where
  projApp : OptionalReduction.WF layer semantics trProj world support
    (fun source => RecM.tryProjAppReduceFinished source flags)
  bitvec : OptionalReduction.WF layer semantics trProj world support
    RecM.tryReduceBitvec
  nat : OptionalReduction.WF layer semantics trProj world support
    (fun source => RecM.tryReduceNatWithSuccMode source natSuccMode)
  native : OptionalReduction.WF layer semantics trProj world support
    RecM.tryReduceNative
  string : OptionalReduction.WF layer semantics trProj world support
    RecM.tryReduceString
  projectionDef : OptionalReduction.WF layer semantics trProj world support
    RecM.tryReduceProjectionDefinition
  quot : OptionalReduction.WF layer semantics trProj world support
    RecM.tryQuotReduce

namespace RecM

/-- With `noAccel` pinned, the general native helper returns `none` without
changing state and without consulting the method table. -/
theorem tryReduceNative_noAccel {methods : Methods .anon}
    {s : TcState .anon} (h : s.noAccel = true) (e : KExpr .anon) :
    (tryReduceNative e).run methods s = .ok none s := by
  unfold tryReduceNative
  rw [ReaderT.run_bind]
  change (EStateM.bind EStateM.get _) s = _
  simp [EStateM.bind, EStateM.get, h]
  rfl

/-- The BitVec acceleration gate is absent from the no-acceleration layer. -/
theorem tryReduceBitvec_noAccel {methods : Methods .anon}
    {s : TcState .anon} (h : s.noAccel = true) (e : KExpr .anon) :
    (tryReduceBitvec e).run methods s = .ok none s := by
  unfold tryReduceBitvec
  rw [ReaderT.run_bind]
  change (EStateM.bind EStateM.get _) s = _
  simp [EStateM.bind, EStateM.get, h]
  rfl

/-- The production native gate satisfies the complete optional-reducer Hoare
contract in the no-acceleration layer: it returns `none` before reading the
source shape, invoking callbacks, or changing state. -/
theorem tryReduceNative_noAccel_optional_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryReduceNative := by
  intro uvars Δ source sourceV s hsource htr
  intro methods hmethods hI
  rw [tryReduceNative_noAccel hI.2.2.1 source]
  exact ⟨hI, trivial⟩

/-- The production BitVec gate has the same exact no-acceleration contract.
In particular, no support-closure or primitive semantic premise is smuggled
into this proof: a hit is operationally impossible under `StateOK`. -/
theorem tryReduceBitvec_noAccel_optional_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryReduceBitvec := by
  intro uvars Δ source sourceV s hsource htr
  intro methods hmethods hI
  rw [tryReduceBitvec_noAccel hI.2.2.1 source]
  exact ⟨hI, trivial⟩

end RecM

namespace NoDeltaBaseOracle

/-- Complete the seven-field production oracle in the no-acceleration layer.
The two omitted fields are not assumptions: they are the concrete gate
proofs above. -/
theorem toNoAccel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (oracle : NoDeltaBaseOracle semantics trProj world support flags
      natSuccMode) :
    NoDeltaReductionOracle .noAccel semantics trProj world support flags
      natSuccMode where
  projApp := oracle.projApp
  bitvec := RecM.tryReduceBitvec_noAccel_optional_wf
  nat := oracle.nat
  native := RecM.tryReduceNative_noAccel_optional_wf
  string := oracle.string
  projectionDef := oracle.projectionDef
  quot := oracle.quot

end NoDeltaBaseOracle

namespace RecM

/-- The Decidable synthesis acceleration gate is absent from the
no-acceleration layer. -/
theorem tryReduceDecidable_noAccel {methods : Methods .anon}
    {s : TcState .anon} (h : s.noAccel = true) (e : KExpr .anon) :
    (tryReduceDecidable e).run methods s = .ok none s := by
  unfold tryReduceDecidable
  rw [ReaderT.run_bind]
  change (EStateM.bind EStateM.get _) s = _
  simp [EStateM.bind, EStateM.get, h]
  rfl

/-- The specialized `Fin.val`/`Decidable.rec` acceleration gate is absent
from the no-acceleration layer. -/
theorem tryReduceFinValDecidableRec_noAccel {methods : Methods .anon}
    {s : TcState .anon} (h : s.noAccel = true) (id : KId .anon)
    (field : UInt64) (head : KExpr .anon) (args : Array (KExpr .anon)) :
    (tryReduceFinValDecidableRec id field head args).run methods s =
      .ok none s := by
  unfold tryReduceFinValDecidableRec
  rw [ReaderT.run_bind]
  change (EStateM.bind EStateM.get _) s = _
  simp [EStateM.bind, EStateM.get, h]
  rfl

/-! ### No-delta reducer seam -/

/-- Exact successful projection-app completion: the projection helper's
spine is rebuilt by the same certified left-to-right helper used by beta and
changed-head application reduction. -/
theorem tryProjAppReduceFinished_some
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {e projResult result : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags}
    (hproj : (tryProjAppReduce e flags).run methods s =
      .ok (some (projResult, args)) s₁)
    (hfinish : (finishAppResult projResult args 0).run methods s₁ =
      .ok result s₂) :
    (tryProjAppReduceFinished e flags).run methods s =
      .ok (some result) s₂ := by
  unfold tryProjAppReduceFinished
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryProjAppReduce e flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  change EStateM.bind
    (ReaderT.run (finishAppResult projResult args 0) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

/-- A projection-app miss is state-transparent through the completion seam. -/
theorem tryProjAppReduceFinished_none
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {e : KExpr .anon} {flags : WhnfFlags}
    (hproj : (tryProjAppReduce e flags).run methods s = .ok none s₁) :
    (tryProjAppReduceFinished e flags).run methods s = .ok none s₁ := by
  unfold tryProjAppReduceFinished
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryProjAppReduce e flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  rfl

/-- Projection-app helper errors retain their exact partial state and prevent
the rebuilding helper from running. -/
theorem tryProjAppReduceFinished_projError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {e : KExpr .anon} {flags : WhnfFlags} {err : TcError .anon}
    (hproj : (tryProjAppReduce e flags).run methods s = .error err s₁) :
    (tryProjAppReduceFinished e flags).run methods s = .error err s₁ := by
  unfold tryProjAppReduceFinished
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryProjAppReduce e flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]

/-- Rebuilding errors, if the helper's implementation ever becomes fallible,
are propagated after projection success with the rebuild's partial state. -/
theorem tryProjAppReduceFinished_finishError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {e projResult : KExpr .anon} {args : Array (KExpr .anon)}
    {flags : WhnfFlags} {err : TcError .anon}
    (hproj : (tryProjAppReduce e flags).run methods s =
      .ok (some (projResult, args)) s₁)
    (hfinish : (finishAppResult projResult args 0).run methods s₁ =
      .error err s₂) :
    (tryProjAppReduceFinished e flags).run methods s =
      .error err s₂ := by
  unfold tryProjAppReduceFinished
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryProjAppReduce e flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  change EStateM.bind
    (ReaderT.run (finishAppResult projResult args 0) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hfinish]

/-- Projection-app is the first no-delta reducer and short-circuits every
later helper on success. -/
theorem whnfNoDeltaReducersStep_projApp
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok (some result) s₁) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₁ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  rfl

/-- BitVec reduction is attempted exactly after a projection-app miss. -/
theorem whnfNoDeltaReducersStep_bitvec
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ =
      .ok (some result) s₂) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₂ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  rfl

/-- Nat reduction follows projection-app and BitVec misses. -/
theorem whnfNoDeltaReducersStep_nat
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok (some result) s₃) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₃ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  rfl

/-- Native reduction follows projection-app, BitVec, and Nat misses. -/
theorem whnfNoDeltaReducersStep_native
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ =
      .ok (some result) s₄) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₄ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  rfl

/-- String reduction follows projection-app, BitVec, Nat, and native misses. -/
theorem whnfNoDeltaReducersStep_string
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ =
      .ok (some result) s₅) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₅ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  rfl

/-- Full-mode projection-wrapper rewriting occurs only after all earlier
literal/native reducers miss. -/
theorem whnfNoDeltaReducersStep_projectionDef
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hfull : flags.isFull = true)
    (hprojection : (tryReduceProjectionDefinition cur).run methods s₅ =
      .ok (some result) s₆) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₆ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hfull]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceProjectionDefinition cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hprojection]
  rfl

/-- In full mode, quotient reduction follows a projection-wrapper miss. -/
theorem whnfNoDeltaReducersStep_quotFull
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ s₇ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hfull : flags.isFull = true)
    (hprojection : (tryReduceProjectionDefinition cur).run methods s₅ =
      .ok none s₆)
    (hquot : (tryQuotReduce cur).run methods s₆ =
      .ok (some result) s₇) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₇ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hfull]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceProjectionDefinition cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hprojection]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₆ = _
  unfold EStateM.bind
  rw [hquot]
  rfl

/-- Cheap mode skips projection-wrapper rewriting and proceeds directly to
quotient reduction after the common reducer prefix. -/
theorem whnfNoDeltaReducersStep_quotCheap
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ : TcState .anon}
    {cur result : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hcheap : flags.isFull = false)
    (hquot : (tryQuotReduce cur).run methods s₅ =
      .ok (some result) s₆) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.next result) s₆ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hcheap]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hquot]
  rfl

/-- Full-mode stuck fallback records misses from every reducer, including
projection-wrapper and quotient helpers, and returns the structural result. -/
theorem whnfNoDeltaReducersStep_doneFull
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ s₇ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hfull : flags.isFull = true)
    (hprojection : (tryReduceProjectionDefinition cur).run methods s₅ =
      .ok none s₆)
    (hquot : (tryQuotReduce cur).run methods s₆ = .ok none s₇) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.done cur) s₇ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hfull]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceProjectionDefinition cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hprojection]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₆ = _
  unfold EStateM.bind
  rw [hquot]
  rfl

/-- Cheap-mode stuck fallback proves that the projection-wrapper helper was
not merely assumed to miss: it was not executed at all. -/
theorem whnfNoDeltaReducersStep_doneCheap
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hcheap : flags.isFull = false)
    (hquot : (tryQuotReduce cur).run methods s₅ = .ok none s₆) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .ok (.done cur) s₆ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hcheap]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hquot]
  rfl

/-- Projection-app errors stop the reducer chain at its first helper. -/
theorem whnfNoDeltaReducersStep_projError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .error err s₁) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₁ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]

/-- BitVec errors are propagated only after a projection-app miss. -/
theorem whnfNoDeltaReducersStep_bitvecError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .error err s₂) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₂ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]

/-- Nat-helper errors retain the state reached after both earlier misses. -/
theorem whnfNoDeltaReducersStep_natError
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .error err s₃) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₃ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]

/-- Native-helper errors occur only after all three preceding reducers miss. -/
theorem whnfNoDeltaReducersStep_nativeError
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .error err s₄) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₄ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]

/-- String-helper errors retain every earlier helper's post-state. -/
theorem whnfNoDeltaReducersStep_stringError
    {methods : Methods .anon} {s s₁ s₂ s₃ s₄ s₅ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .error err s₅) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₅ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]

/-- Projection-wrapper errors are possible only in full mode and preserve
the exact state produced after the common reducer prefix. -/
theorem whnfNoDeltaReducersStep_projectionDefError
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hfull : flags.isFull = true)
    (hprojection : (tryReduceProjectionDefinition cur).run methods s₅ =
      .error err s₆) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₆ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hfull]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceProjectionDefinition cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hprojection]

/-- Full-mode quotient errors occur after an explicit projection-wrapper
miss and retain the quotient helper's partial state. -/
theorem whnfNoDeltaReducersStep_quotFullError
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ s₇ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hfull : flags.isFull = true)
    (hprojection : (tryReduceProjectionDefinition cur).run methods s₅ =
      .ok none s₆)
    (hquot : (tryQuotReduce cur).run methods s₆ = .error err s₇) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₇ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hfull]
  simp only [if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceProjectionDefinition cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hprojection]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₆ = _
  unfold EStateM.bind
  rw [hquot]

/-- Cheap-mode quotient errors demonstrate that projection-wrapper rewriting
was skipped rather than assumed successful or missed. -/
theorem whnfNoDeltaReducersStep_quotCheapError
    {methods : Methods .anon}
    {s s₁ s₂ s₃ s₄ s₅ s₆ : TcState .anon}
    {cur : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hproj : (tryProjAppReduceFinished cur flags).run methods s =
      .ok none s₁)
    (hbitvec : (tryReduceBitvec cur).run methods s₁ = .ok none s₂)
    (hnat : (tryReduceNatWithSuccMode cur natSuccMode).run methods s₂ =
      .ok none s₃)
    (hnative : (tryReduceNative cur).run methods s₃ = .ok none s₄)
    (hstring : (tryReduceString cur).run methods s₄ = .ok none s₅)
    (hcheap : flags.isFull = false)
    (hquot : (tryQuotReduce cur).run methods s₅ = .error err s₆) :
    (whnfNoDeltaReducersStep flags natSuccMode cur).run methods s =
      .error err s₆ := by
  unfold whnfNoDeltaReducersStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryProjAppReduceFinished cur flags) methods) _ s = _
  unfold EStateM.bind
  rw [hproj]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceBitvec cur) methods) _ s₁ = _
  unfold EStateM.bind
  rw [hbitvec]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (tryReduceNatWithSuccMode cur natSuccMode) methods) _ s₂ = _
  unfold EStateM.bind
  rw [hnat]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceNative cur) methods) _ s₃ = _
  unfold EStateM.bind
  rw [hnative]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryReduceString cur) methods) _ s₄ = _
  unfold EStateM.bind
  rw [hstring]
  simp only
  rw [hcheap]
  simp only [Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (tryQuotReduce cur) methods) _ s₅ = _
  unfold EStateM.bind
  rw [hquot]

/-- The outer no-delta step is exactly structural WHNF followed by the named
ordered reducer seam, with both intermediate states visible. -/
theorem whnfNoDeltaImplStep_ofCore
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source core : KExpr .anon}
    {action : BoundedStep (KExpr .anon) (KExpr .anon)}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (hcore : (whnfCoreWithFlags source flags).run methods s =
      .ok core s₁)
    (htail : (whnfNoDeltaReducersStep flags natSuccMode core).run methods s₁ =
      .ok action s₂) :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
      .ok action s₂ := by
  unfold whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlags source flags) methods) _ s = _
  unfold EStateM.bind
  rw [hcore]
  exact htail

/-- A structural-WHNF error stops the no-delta iteration before any optional
reducer executes and retains the structural driver's partial state. -/
theorem whnfNoDeltaImplStep_coreError
    {methods : Methods .anon} {s s₁ : TcState .anon}
    {source : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hcore : (whnfCoreWithFlags source flags).run methods s =
      .error err s₁) :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
      .error err s₁ := by
  unfold whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlags source flags) methods) _ s = _
  unfold EStateM.bind
  rw [hcore]

/-- An error in the ordered reducer seam is propagated after structural WHNF
with the reducer's exact partial post-state. -/
theorem whnfNoDeltaImplStep_reducerError
    {methods : Methods .anon} {s s₁ s₂ : TcState .anon}
    {source core : KExpr .anon} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hcore : (whnfCoreWithFlags source flags).run methods s =
      .ok core s₁)
    (htail : (whnfNoDeltaReducersStep flags natSuccMode core).run methods s₁ =
      .error err s₂) :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
      .error err s₂ := by
  unfold whnfNoDeltaImplStep
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (whnfCoreWithFlags source flags) methods) _ s = _
  unfold EStateM.bind
  rw [hcore]
  exact htail

/-- Semantic acceptance for any successful reducer branch.  Structural and
reducer meanings are composed in the fixed Theory context; support and the
post-state invariant remain branch-local evidence rather than consequences
of the operational equation alone. -/
theorem whnfNoDeltaImplStep_next_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {source core result : KExpr .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (theory : WhnfTheory trProj world uvars)
    (hI : WhnfStateInv layer semantics trProj world support uvars Δ s)
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s₂)
    (hcore : (whnfCoreWithFlags source flags).run methods s =
      .ok core s₁)
    (htail : (whnfNoDeltaReducersStep flags natSuccMode core).run methods s₁ =
      .ok (.next result) s₂)
    (hresultSupport : support result)
    (hcoreMeaning : WhnfMeaning trProj world uvars Δ source core)
    (hreducerMeaning : WhnfMeaning trProj world uvars Δ core result) :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
        .ok (.next result) s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfStep.Meaning trProj world support uvars Δ id source
        (.next result) := by
  exact ⟨whnfNoDeltaImplStep_ofCore hcore htail, hpost,
    hresultSupport,
    theory.transMeaning hI.2.1.wf hcoreMeaning hreducerMeaning⟩

/-- Semantic acceptance for the fully stuck reducer tail.  The tail returns
the structural result unchanged, so its local semantic contribution is
reflexive and the structural driver's meaning is retained exactly. -/
theorem whnfNoDeltaImplStep_done_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s₁ s₂ : TcState .anon} {source core : KExpr .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s₂)
    (hcore : (whnfCoreWithFlags source flags).run methods s =
      .ok core s₁)
    (htail : (whnfNoDeltaReducersStep flags natSuccMode core).run methods s₁ =
      .ok (.done core) s₂)
    (hcoreSupport : support core)
    (hcoreMeaning : WhnfMeaning trProj world uvars Δ source core) :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
        .ok (.done core) s₂ ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s₂ ∧
      WhnfStep.Meaning trProj world support uvars Δ id source
        (.done core) :=
  ⟨whnfNoDeltaImplStep_ofCore hcore htail, hpost,
    hcoreSupport, hcoreMeaning⟩

/-- Error acceptance keeps partial-state preservation explicit for both the
structural driver and all reducer helpers.  Later exhaustive `WhnfStep.WF`
assembly discharges this premise from their individual Hoare contracts. -/
theorem whnfNoDeltaImplStep_error_acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {methods : Methods .anon}
    {s s' : TcState .anon} {source : KExpr .anon}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode} {err : TcError .anon}
    (hrun : (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
      .error err s')
    (hpost : WhnfStateInv layer semantics trProj world support uvars Δ s') :
    (whnfNoDeltaImplStep flags natSuccMode source).run methods s =
        .error err s' ∧
      WhnfStateInv layer semantics trProj world support uvars Δ s' :=
  ⟨hrun, hpost⟩

/-- The ordered optional-reducer seam satisfies the complete one-step
contract once each concrete helper supplies its uniform Hoare field.  The
proof follows production order exactly, short-circuits on the first hit, and
uses reflexive meaning only after every reachable helper misses. -/
theorem whnfNoDeltaReducersStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (theory : WhnfTheory trProj world uvars)
    (oracle : NoDeltaReductionOracle layer semantics trProj world support
      flags natSuccMode) :
    WhnfStep.WF layer semantics trProj world support uvars Δ id
      (whnfNoDeltaReducersStep flags natSuccMode) (fun _ _ => True) := by
  intro source s hsource
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  unfold whnfNoDeltaReducersStep
  apply RecM.WF.bind (oracle.projApp hsourceSupport hsourceTr)
  intro projResult s₁ hproj
  cases projResult with
  | some result =>
      apply RecM.WF.pure
      intro _
      simpa [WhnfStep.Meaning] using hproj
  | none =>
      simp only [pure_bind]
      apply RecM.WF.bind (oracle.bitvec hsourceSupport hsourceTr)
      intro bitvecResult s₂ hbitvec
      cases bitvecResult with
      | some result =>
          apply RecM.WF.pure
          intro _
          simpa [WhnfStep.Meaning] using hbitvec
      | none =>
          apply RecM.WF.bind (oracle.nat hsourceSupport hsourceTr)
          intro natResult s₃ hnat
          cases natResult with
          | some result =>
              apply RecM.WF.pure
              intro _
              simpa [WhnfStep.Meaning] using hnat
          | none =>
              apply RecM.WF.bind (oracle.native hsourceSupport hsourceTr)
              intro nativeResult s₄ hnative
              cases nativeResult with
              | some result =>
                  apply RecM.WF.pure
                  intro _
                  simpa [WhnfStep.Meaning] using hnative
              | none =>
                  apply RecM.WF.bind (oracle.string hsourceSupport hsourceTr)
                  intro stringResult s₅ hstring
                  cases stringResult with
                  | some result =>
                      apply RecM.WF.pure
                      intro _
                      simpa [WhnfStep.Meaning] using hstring
                  | none =>
                      cases hfull : flags.isFull with
                      | false =>
                          simp only [Bool.false_eq_true, if_false]
                          apply RecM.WF.bind
                            (oracle.quot hsourceSupport hsourceTr)
                          intro quotResult s₆ hquot
                          cases quotResult with
                          | some result =>
                              apply RecM.WF.pure
                              intro _
                              simpa [WhnfStep.Meaning] using hquot
                          | none =>
                              apply RecM.WF.pure
                              intro hI
                              exact ⟨hsourceSupport,
                                WhnfMeaning.refl hsourceTr
                                  (theory.exprWF hI.2.1 hsourceTr)⟩
                      | true =>
                          simp only [if_true]
                          apply RecM.WF.bind
                            (oracle.projectionDef hsourceSupport hsourceTr)
                          intro projectionResult s₆ hprojection
                          cases projectionResult with
                          | some result =>
                              apply RecM.WF.pure
                              intro _
                              simpa [WhnfStep.Meaning] using hprojection
                          | none =>
                              apply RecM.WF.bind
                                (oracle.quot hsourceSupport hsourceTr)
                              intro quotResult s₇ hquot
                              cases quotResult with
                              | some result =>
                                  apply RecM.WF.pure
                                  intro _
                                  simpa [WhnfStep.Meaning] using hquot
                              | none =>
                                  apply RecM.WF.pure
                                  intro hI
                                  exact ⟨hsourceSupport,
                                    WhnfMeaning.refl hsourceTr
                                      (theory.exprWF hI.2.1 hsourceTr)⟩

/-- The production reducer tail in the no-acceleration layer needs only the
five genuinely active helper contracts.  Native and BitVec are discharged by
their concrete state gate, not carried as oracle premises. -/
theorem whnfNoDeltaReducersStep_noAccel_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (theory : WhnfTheory trProj world uvars)
    (oracle : NoDeltaBaseOracle semantics trProj world support flags
      natSuccMode) :
    WhnfStep.WF .noAccel semantics trProj world support uvars Δ id
      (whnfNoDeltaReducersStep flags natSuccMode) (fun _ _ => True) :=
  whnfNoDeltaReducersStep_wf theory oracle.toNoAccel

/-- Compose the actual structural reducer and the actual ordered no-delta
tail into one exhaustive `WhnfStep.WF`.  The static context-WF premise is
exactly what Theory transitivity needs when the structural and tail
translations of their shared middle term are not definitionally identical. -/
theorem whnfNoDeltaImplStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (theory : WhnfTheory trProj world uvars)
    (hΔ : KVLCtx.WF world.venv uvars Δ)
    (core : StructuralReduction.WF layer semantics trProj world support
      uvars Δ flags)
    (oracle : NoDeltaReductionOracle layer semantics trProj world support
      flags natSuccMode) :
    WhnfStep.WF layer semantics trProj world support uvars Δ id
      (whnfNoDeltaImplStep flags natSuccMode) (fun _ _ => True) := by
  intro source s hsource
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  unfold whnfNoDeltaImplStep
  apply RecM.WF.bind (core hsourceSupport hsourceTr)
  intro reduced s₁ hreduced
  obtain ⟨hreducedSupport, hreducedMeaning⟩ := hreduced
  have hreducedMeaningCopy := hreducedMeaning
  obtain ⟨_, reducedV, _, hreducedTr, _⟩ := hreducedMeaningCopy
  have htail :=
    whnfNoDeltaReducersStep_wf (uvars := uvars) (Δ := Δ)
      theory oracle reduced s₁
      ⟨hreducedSupport, reducedV, hreducedTr⟩
  apply RecM.WF.mono htail
  · intro action s₂ haction
    cases action with
    | next result =>
        exact ⟨haction.1,
          theory.transMeaning hΔ hreducedMeaning haction.2⟩
    | done result =>
        exact ⟨haction.1,
          theory.transMeaning hΔ hreducedMeaning haction.2⟩
  · intro err s₂ herror
    exact herror

/-- No-acceleration specialization of the complete outer no-delta step. -/
theorem whnfNoDeltaImplStep_noAccel_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {flags : WhnfFlags}
    {natSuccMode : NatSuccMode}
    (theory : WhnfTheory trProj world uvars)
    (hΔ : KVLCtx.WF world.venv uvars Δ)
    (core : StructuralReduction.WF .noAccel semantics trProj world support
      uvars Δ flags)
    (oracle : NoDeltaBaseOracle semantics trProj world support flags
      natSuccMode) :
    WhnfStep.WF .noAccel semantics trProj world support uvars Δ id
      (whnfNoDeltaImplStep flags natSuccMode) (fun _ _ => True) :=
  whnfNoDeltaImplStep_wf theory hΔ core oracle.toNoAccel

/-- Feed the assembled no-acceleration step directly into the already proved
public no-delta cache/dispatcher shell.  The remaining premises are now
separated by ownership: structural WHNF, the five active base reducers,
context-key/lazy-read framing, and collision-robust cache writes. -/
theorem whnfNoDeltaImpl_noAccel_wf_of_base
    {keys : WhnfContextKeys} {fallback : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {Δ : KVLCtx} {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    {source : KExpr .anon}
    (theory : WhnfTheory trProj world keys.uvars)
    (hΔ : KVLCtx.WF world.venv keys.uvars Δ)
    (core : StructuralReduction.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ flags)
    (oracle : NoDeltaBaseOracle (whnfCacheSemantics keys trProj fallback)
      trProj world support flags natSuccMode)
    (hkeyRep : WhnfKey.Represents keys trProj world source Δ)
    (htransient : TransientNatWork.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Δ source)
    (hwrites : WhnfCacheWriteOracle keys trProj fallback world support)
    (hsourceSupport : support source)
    {sourceV : VExpr} {s : TcState .anon}
    (hsource : TrKExprS world.venv keys.uvars world.nameOf trProj Δ source
      sourceV) :
    RecM.WF .noAccel (whnfCacheSemantics keys trProj fallback) trProj world
      support keys.uvars Δ s (whnfNoDeltaImpl source flags natSuccMode)
      (fun result _ => support result ∧
        WhnfPost trProj world keys.uvars Δ sourceV result) :=
  whnfNoDeltaImpl_wf theory hkeyRep htransient
    (whnfNoDeltaImplStep_noAccel_wf theory hΔ core oracle)
    hwrites hsourceSupport hsource

end RecM

end Ix.Tc
