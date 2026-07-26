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
  Represents : Address → KVLCtx → Prop

namespace WhnfContextKeys

/-- Closed expressions use the distinguished empty-context key. -/
def closed (uvars : Nat) : WhnfContextKeys where
  uvars := uvars
  Represents key Δ := key = emptyCtxAddr ∧ Δ = []

@[simp] theorem closed_represents {uvars : Nat} {key : Address}
    {Δ : KVLCtx} :
    (closed uvars).Represents key Δ ↔ key = emptyCtxAddr ∧ Δ = [] :=
  Iff.rfl

/-- A represented semantic context tied to the actual production cache-key
computation in a concrete state.  Constructing this witness—not merely
postulating `Represents`—is the K1/K2 context-key proof obligation. -/
def Matches (keys : WhnfContextKeys) (trProj : RawProjRel)
    (world : VerifyWorld) (s : TcState .anon) (Δ : KVLCtx)
    (source : KExpr .anon) (key : Address × Address) : Prop :=
  CtxRecon world.venv keys.uvars world.nameOf trProj s Δ ∧
    keys.Represents key.2 Δ ∧
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

/-- Minimal fallback used by a WHNF-only verification slice: cached block
errors remain replayable, while every semantic family not owned by K1 is
rejected.  K2 replaces this fallback when inference and defeq caches become
available. -/
def blockErrorsOnly : CacheSemantics where
  Valid _ _ entry :=
    match entry with
    | .blockResult _ (.error _) => True
    | _ => False
  mono := by
    intro before after support entry hle h
    exact h
  blockError := by
    intro authority support block err
    trivial

end CacheSemantics

/-- Exact K1 validity for one tagged entry.  The fallback owns every non-K1
cache family.  A WHNF entry must be sound for every finite-support source
whose address is its first key component and every context represented by
its second component. -/
def WhnfCacheValid (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .expr .whnf key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfNoDelta key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfNoDeltaCheap key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfCore key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
  | .expr .whnfCoreCheap key value =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Δ, keys.Represents key.2 Δ →
          WhnfMeaning trProj authority.world keys.uvars Δ source value
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
  | defEq | defEqFailure | unfold | natSuccStuck | isProp | isRec |
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
    {Δ : KVLCtx} (hctx : keys.Represents key.2 Δ) :
    WhnfMeaning trProj authority.world keys.uvars Δ source value := by
  cases hkind <;> exact h source hsource haddr Δ hctx

end WhnfCacheValid

/-- Overlay the exact K1 meanings on an existing semantic family. -/
def whnfCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := WhnfCacheValid keys trProj fallback
  mono := WhnfCacheValid.mono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err

namespace CacheProvenance

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
    (hctx : keys.Represents key.2 Δ) :
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
    (hctx : keys.Represents key.2 Δ) :
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

/-- The two theorem layers required by K1.  The no-acceleration layer pins
the production flag; the accelerated layer permits native helpers and hence
requires `NativeOracle` at their successful branches. -/
inductive WhnfLayer where
  | noAccel
  | accelerated
  deriving Repr, DecidableEq

def WhnfLayer.StateOK : WhnfLayer → TcState .anon → Prop
  | .noAccel, s => s.noAccel = true
  | .accelerated, _ => True

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
    (hnoAccel : after.noAccel = before.noAccel) :
    WhnfStateInv layer semantics trProj world support uvars Δ after := by
  rcases h with ⟨hkernel, hrecon, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hkernel.core.of_env_eq henv
      internSupport := by simpa only [henv] using hkernel.internSupport
      caches := by simpa only [henv] using hkernel.caches }
  · exact hrecon.of_fields_eq hctx hlet hnum hlctx (by simp [henv])
  · cases layer with
    | noAccel => simpa only [WhnfLayer.StateOK, hnoAccel] using hlayer
    | accelerated => trivial

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
  refine ⟨?_, ?_, ?_⟩
  · exact {
      core := hkernel.core.of_env_eq henv
      internSupport := by simpa [henv] using hkernel.internSupport
      caches := by simpa [henv] using hkernel.caches }
  · exact hctx.of_fields_eq hctxEq hlet hnum hlctx (by simp [henv])
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK, hnoAccel] using hlayer
    | accelerated => trivial

end ContextKeyFrame

namespace InternUpdateFrame

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
  refine ⟨hkernel, ?_, ?_⟩
  · exact hctx.of_fields_eq hctxEq hlet hnum hlctx (by simp [hnext])
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK, hnoAccel] using hlayer
    | accelerated => trivial

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
      hpost.2.2, hkernel.caches.of_intern_update⟩
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
  simp only [pure_bind]
  rw [hval]
  change EStateM.bind (TcM.runIntern (lift val (idx + 1) 0))
    (fun r => pure (some r)) s = _
  unfold EStateM.bind
  rw [hlift]
  rfl

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
  split
  · exact TcM.WF.pure fun _ => rfl
  · apply TcM.WF.bind
      (Q₁ := fun _ after => after = before)
      (TcM.WF.pure fun _ => rfl)
    intro _ after hafter
    subst after
    simp only
    split
    · exact TcM.WF.pure fun _ => rfl
    · apply TcM.WF.bind
        (Q₁ := fun _ after => after = before)
        (TcM.WF.pure fun _ => rfl)
      intro _ after hafter
      subst after
      refine TcM.WF.bind
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
    (hrep : ∀ key s', TcM.whnfKey source s = .ok key s' →
      keys.Represents key.2 Δ) :
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
        ⟨⟨hI.2.1, hrep key s' hrun, ⟨s', hrun⟩⟩, hwf.2.2⟩⟩
  | .error err s' =>
      rw [hrun] at hwf
      exact hwf

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

/-- Conditional semantic closure of all six K0 method-table back-edges.
K1 consumes this record while proving WHNF; K2 proves the inference/defeq
fields and closes `methodsN` by induction. -/
structure WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) : Prop where
  whnf : ∀ {uvars Δ s e sourceV},
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnf e)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result)
  whnfCore : ∀ {uvars Δ s e sourceV},
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCore e)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result)
  whnfMode : ∀ {uvars Δ s e sourceV} {mode : NatSuccMode},
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfMode e mode)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result)
  whnfCoreFlags : ∀ {uvars Δ s e sourceV} {flags : WhnfFlags},
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.whnfCoreFlags e flags)
      (fun result _ => WhnfPost trProj world uvars Δ sourceV result)
  infer : ∀ {uvars Δ s e sourceV},
    TrKExprS world.venv uvars world.nameOf trProj Δ e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.infer e)
      (fun ty _ => InferPost trProj world uvars Δ sourceV ty)
  isDefEq : ∀ {uvars Δ s a b va vb},
    TrKExprS world.venv uvars world.nameOf trProj Δ a va →
    TrKExprS world.venv uvars world.nameOf trProj Δ b vb →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (methods.isDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Δ.toCtx va vb)

end Methods

/-! ## Projection/iota semantic boundary -/

/-- Conditional K1e boundary for the two inductive structural reducers.

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
    Methods.WF layer semantics trProj world support methods →
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
    Methods.WF layer semantics trProj world support methods →
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
  ∀ methods, methods.WF layer semantics trProj world support →
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

end WF

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
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfCore hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK] using hlayer
    | accelerated => trivial

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
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfCoreCheap hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK] using hlayer
    | accelerated => trivial

end WhnfCoreCacheUpdate

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

end WhnfFullTrace

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
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfNoDelta hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK] using hlayer
    | accelerated => trivial

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
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnfNoDeltaCheap hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK] using hlayer
    | accelerated => trivial

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
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertWhnf hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer with
    | noAccel => simpa [WhnfLayer.StateOK] using hlayer
    | accelerated => trivial

end WhnfDriverCacheUpdate

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
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
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
  rw [ReaderT.run_bind, ReaderT.run_pure, pure_bind]
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

/-- Every structural leaf terminates one named production loop iteration. -/
theorem whnfCoreWithFlagsStep_leaf {methods : Methods .anon}
    {s : TcState .anon} {e : KExpr .anon} (hleaf : WhnfCoreLeaf e)
    (flags : WhnfFlags) :
    (whnfCoreWithFlagsStep e flags).run methods s = .ok (.done e) s := by
  cases hleaf <;> rfl

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

/-- Conditional K1e projection package.  The production execution is proved
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
    (hmethods : Methods.WF layer semantics trProj world support methods)
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

/-- Conditional K1e iota package.  The source translation premise is
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
    (hmethods : Methods.WF layer semantics trProj world support methods)
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

/-- K1d legacy-zeta package.  The execution-indexed lift walker supplies the
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

/-- K1d fvar-zeta package.  Unlike the legacy branch this execution is
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

end RecM

end Ix.Tc
