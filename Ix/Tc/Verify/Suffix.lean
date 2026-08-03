import Ix.Tc.Verify.Whnf

/-!
# K2 suffix-context transport boundary

WHNF cache keys hash only the de-Bruijn suffix reachable from an expression.
The hash itself is not semantic evidence.  This module states the two facts a
concrete verification of `TcM.ctxAddrForLbr` must establish and derives the
global, collision-robust cache-write rule from them.

`WhnfSuffixModel.represents` is operational: it applies only to a checker
state reconciled with the claimed semantic context.  `transport` is semantic:
two contexts represented by one suffix key preserve WHNF meaning.  Separating
these clauses prevents either arbitrary-state context identification or bare
address equality from entering the cache proof.
-/

namespace Ix.Tc

/-! ## Exact production memo behavior -/

namespace TcM

/-- The zero-radius/empty-context fast path is state-pure.  Combining the two
guards in one theorem makes the operational case split exhaustive. -/
theorem ctxAddrForLbr_trivial
    {lbr : UInt64} {s : TcState .anon}
    (htrivial : (lbr == 0 || s.ctx.isEmpty) = true) :
    ctxAddrForLbr lbr s = .ok emptyCtxAddr s := by
  unfold ctxAddrForLbr
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [htrivial]
  rfl

/-- A nontrivial memo hit returns the stored address without changing state. -/
theorem ctxAddrForLbr_cacheHit
    {lbr : UInt64} {s : TcState .anon} {cached : Address}
    (hactive : (lbr == 0 || s.ctx.isEmpty) = false)
    (hcache : s.ctxAddrCache[(s.ctxId, lbr)]? = some cached) :
    ctxAddrForLbr lbr s = .ok cached s := by
  unfold ctxAddrForLbr
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [hactive, hcache]
  rfl

/-- A nontrivial memo miss returns the exact pure suffix calculation and
inserts precisely that result under the current `(ctxId, lbr)` key. -/
theorem ctxAddrForLbr_cacheMiss
    {lbr : UInt64} {s : TcState .anon}
    (hactive : (lbr == 0 || s.ctx.isEmpty) = false)
    (hcache : s.ctxAddrCache[(s.ctxId, lbr)]? = none) :
    ctxAddrForLbr lbr s =
      .ok (ctxAddrForLbrUncached s lbr)
        {s with ctxAddrCache := (s.ctxAddrCache.insert (s.ctxId, lbr)
          (ctxAddrForLbrUncached s lbr))} := by
  unfold ctxAddrForLbr
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp [hactive, hcache]
  rfl

/-- Every successful suffix-key computation is stable on immediate replay.
This covers fast paths, pre-existing memo hits, and the newly inserted miss
entry against the actual production implementation. -/
theorem ctxAddrForLbr_replay
    {lbr : UInt64} {before after : TcState .anon} {ctxAddr : Address}
    (hrun : ctxAddrForLbr lbr before = .ok ctxAddr after) :
    ctxAddrForLbr lbr after = .ok ctxAddr after := by
  cases hactive : (lbr == 0 || before.ctx.isEmpty) with
  | true =>
      have heval := ctxAddrForLbr_trivial hactive
      rw [heval] at hrun
      injection hrun with haddr hstate
      subst ctxAddr
      subst after
      exact heval
  | false =>
      cases hcache : before.ctxAddrCache[(before.ctxId, lbr)]? with
      | some cached =>
          have heval := ctxAddrForLbr_cacheHit hactive hcache
          rw [heval] at hrun
          injection hrun with haddr hstate
          subst ctxAddr
          subst after
          exact ctxAddrForLbr_cacheHit hactive hcache
      | none =>
          have heval := ctxAddrForLbr_cacheMiss hactive hcache
          rw [heval] at hrun
          injection hrun with haddr hstate
          subst ctxAddr
          subst after
          apply ctxAddrForLbr_cacheHit
          · simpa using hactive
          · simp

/-- Coherence of every memo entry that is observable in the current context.
Entries belonging to older `ctxId`s remain intentionally unconstrained: the
production lookup cannot consult them.  Zero-radius and empty-context entries
are likewise irrelevant because those fast paths bypass the memo. -/
def ContextAddrMemoValid (s : TcState .anon) : Prop :=
  ∀ {lbr : UInt64} {cached : Address},
    (lbr == 0 || s.ctx.isEmpty) = false →
    s.ctxAddrCache[(s.ctxId, lbr)]? = some cached →
    cached = ctxAddrForLbrUncached s lbr

@[simp] theorem ctxSuffixNeedStep_setCache
    (s : TcState .anon) (cache : Std.HashMap (Address × UInt64) Address)
    (need : Nat) :
    ctxSuffixNeedStep {s with ctxAddrCache := cache} need =
      ctxSuffixNeedStep s need := by
  unfold ctxSuffixNeedStep
  rfl

@[simp] theorem ctxSuffixNeed_setCache
    (s : TcState .anon) (cache : Std.HashMap (Address × UInt64) Address) :
    ∀ fuel need,
      ctxSuffixNeed {s with ctxAddrCache := cache} fuel need =
        ctxSuffixNeed s fuel need
  | 0, _ => rfl
  | fuel + 1, need => by
      simp only [ctxSuffixNeed]
      rw [ctxSuffixNeedStep_setCache]
      split
      · rfl
      · exact ctxSuffixNeed_setCache s cache fuel _

/-- The pure suffix calculation is insensitive to the memo table. -/
@[simp] theorem ctxAddrForLbrUncached_setCache
    (s : TcState .anon) (cache : Std.HashMap (Address × UInt64) Address)
    (lbr : UInt64) :
    ctxAddrForLbrUncached {s with ctxAddrCache := cache} lbr =
      ctxAddrForLbrUncached s lbr := by
  unfold ctxAddrForLbrUncached
  simp only
  rw [ctxSuffixNeed_setCache]

/-- The real memoized suffix computation preserves current-context memo
coherence.  The proof audits both the overwritten key and every framed entry;
it does not infer coherence merely from replay determinism. -/
theorem ctxAddrForLbr_memoValid
    {lbr : UInt64} {before after : TcState .anon} {ctxAddr : Address}
    (hvalid : ContextAddrMemoValid before)
    (hrun : ctxAddrForLbr lbr before = .ok ctxAddr after) :
    ContextAddrMemoValid after := by
  cases hactive : (lbr == 0 || before.ctx.isEmpty) with
  | true =>
      have heval := ctxAddrForLbr_trivial hactive
      rw [heval] at hrun
      injection hrun with _ hstate
      subst after
      change ContextAddrMemoValid before
      exact hvalid
  | false =>
      cases hcache : before.ctxAddrCache[(before.ctxId, lbr)]? with
      | some cached =>
          have heval := ctxAddrForLbr_cacheHit hactive hcache
          rw [heval] at hrun
          injection hrun with _ hstate
          subst after
          change ContextAddrMemoValid before
          exact hvalid
      | none =>
          have heval := ctxAddrForLbr_cacheMiss hactive hcache
          rw [heval] at hrun
          injection hrun with haddr hstate
          subst ctxAddr
          subst after
          intro other cached hother hlookup
          rw [Std.HashMap.getElem?_insert] at hlookup
          split at hlookup
          · next hbeq =>
            have hpair := eq_of_beq hbeq
            have hlbr : lbr = other := congrArg Prod.snd hpair
            subst other
            cases hlookup
            simp
          · have hold := hvalid (by simpa using hother) hlookup
            simpa using hold

end TcM

/-- Canonical ghost interpretation generated by real suffix-key executions.
Unlike an arbitrary `WhnfContextKeys`, membership cannot be asserted from a
bare address: it stores a reconciled pre-state and the exact production run
that emitted the context component. -/
def operationalWhnfContextKeys (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) : WhnfContextKeys where
  uvars := uvars
  Represents lbr ctxAddr Delta :=
    exists before after,
      CtxRecon world.venv uvars world.nameOf trProj before Delta ∧
        TcM.ctxAddrForLbr lbr before = .ok ctxAddr after

namespace operationalWhnfContextKeys

/-- Every reconciled execution is represented by the canonical operational
interpretation. -/
theorem represents {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {before after : TcState .anon}
    {source : KExpr .anon} {key : Address × Address} {Delta : KVLCtx}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj before Delta)
    (hrun : TcM.whnfKey source before = .ok key after) :
    (operationalWhnfContextKeys trProj world uvars).Represents
      source.lbr key.2 Delta :=
  ⟨before, after, hctx, TcM.whnfKey_ctx hrun⟩

/-- Direct suffix-address executions, including DefEq's shared-context key,
are represented without manufacturing an expression wrapper. -/
theorem representsCtx {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {before after : TcState .anon} {lbr : UInt64}
    {ctxAddr : Address} {Delta : KVLCtx}
    (hctx : CtxRecon world.venv uvars world.nameOf trProj before Delta)
    (hrun : TcM.ctxAddrForLbr lbr before = .ok ctxAddr after) :
    (operationalWhnfContextKeys trProj world uvars).Represents
      lbr ctxAddr Delta :=
  ⟨before, after, hctx, hrun⟩

end operationalWhnfContextKeys

/-! ## Finite composite-digest boundary -/

/-- Declarative specification of the exact composite input hashed by
`ctxAddrForLbr`.

`Input` is intentionally abstract: an implementation may normalize closed
contexts, whole-context `ctxId` inputs, and proper suffix encodings
differently.  `execution` is the load-bearing implementation theorem.  In
particular, it must justify memo hits as well as freshly computed hashes; an
arbitrary `ctxAddrCache` entry cannot satisfy this field merely because it was
returned by production. -/
structure ContextDigestSpec (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) where
  Input : Type
  inputOf : UInt64 → KVLCtx → Input
  digest : Input → Address
  /-- States whose context-id chain and suffix memo are coherent with
  `inputOf`/`digest`.  This cannot be omitted: arbitrary checker states may
  contain arbitrary `ctxAddrCache` entries. -/
  StateValid : TcState .anon → Prop
  /-- The abstract valid-state predicate must expose the concrete memo
  coherence that production actually consults. -/
  memoValid : ∀ {s}, StateValid s → TcM.ContextAddrMemoValid s
  /-- State validity is stable under the real memo operation.  This is needed
  to chain a finite run: validity of the first key computation alone says
  nothing about the next memoized call. -/
  preserves : ∀ {before after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address},
    StateValid before →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    StateValid after
  execution : ∀ {before after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address} {Delta : KVLCtx},
    StateValid before →
    CtxRecon world.venv uvars world.nameOf trProj before Delta →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    digest (inputOf lbr Delta) = ctxAddr

/-- A genuinely finite collection of composite context-digest inputs for one
verified run.  The list representation keeps finiteness constructive and
does not require classical finite-set membership. -/
structure ContextDigestScope {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (spec : ContextDigestSpec trProj world uvars) where
  entries : List spec.Input

namespace ContextDigestScope

variable {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {spec : ContextDigestSpec trProj world uvars}

/-- Membership in the run's finite composite-digest input list. -/
def Contains (scope : ContextDigestScope spec) (input : spec.Input) : Prop :=
  input ∈ scope.entries

/-- Explicit collision freedom for the *composite* digest on this finite
scope.  It is deliberately separate from `RunSupport.CollisionFree`, which
only controls expression and universe addresses. -/
def CollisionFree (scope : ContextDigestScope spec) : Prop :=
  ∀ {a b : spec.Input}, scope.Contains a → scope.Contains b →
    spec.digest a = spec.digest b → a = b

/-- Every reconciled production key execution from one concrete state must
land in the finite scope.  Keeping `before` explicit is load-bearing: a run
scope covers reachable states, not every state that could satisfy the
unscoped context relation. -/
def Captures (scope : ContextDigestScope spec)
    (before : TcState .anon) : Prop :=
  ∀ {after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address} {Delta : KVLCtx},
    CtxRecon world.venv uvars world.nameOf trProj before Delta →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    scope.Contains (spec.inputOf lbr Delta)

end ContextDigestScope

/-- The operational representation restricted to a finite run scope.  Both
conjuncts are required: list membership without an actual production run is
not a key witness, while an arbitrary-state run outside the verified scope
cannot consume the run-scoped collision hypothesis. -/
def scopedOperationalWhnfContextKeys {trProj : RawProjRel}
    {world : VerifyWorld} {uvars : Nat}
    (spec : ContextDigestSpec trProj world uvars)
    (scope : ContextDigestScope spec) : WhnfContextKeys where
  uvars := uvars
  Represents lbr ctxAddr Delta :=
    ∃ before after,
      spec.StateValid before ∧
        CtxRecon world.venv uvars world.nameOf trProj before Delta ∧
        TcM.ctxAddrForLbr lbr before = .ok ctxAddr after ∧
        scope.Contains (spec.inputOf lbr Delta)

namespace scopedOperationalWhnfContextKeys

variable {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {spec : ContextDigestSpec trProj world uvars}
    {scope : ContextDigestScope spec}

/-- A captured WHNF/inference key execution constructs scoped
representation; no address-only membership premise is accepted. -/
theorem represents {before after : TcState .anon} {source : KExpr .anon}
    {key : Address × Address} {Delta : KVLCtx}
    (hvalid : spec.StateValid before)
    (hcapture : scope.Captures before)
    (hctx : CtxRecon world.venv uvars world.nameOf trProj before Delta)
    (hrun : TcM.whnfKey source before = .ok key after) :
    (scopedOperationalWhnfContextKeys spec scope).Represents
      source.lbr key.2 Delta := by
  exact ⟨before, after, hvalid, hctx, TcM.whnfKey_ctx hrun,
    hcapture hctx (TcM.whnfKey_ctx hrun)⟩

/-- Direct captured context-key execution, used by DefEq. -/
theorem representsCtx {before after : TcState .anon} {lbr : UInt64}
    {ctxAddr : Address} {Delta : KVLCtx}
    (hvalid : spec.StateValid before)
    (hcapture : scope.Captures before)
    (hctx : CtxRecon world.venv uvars world.nameOf trProj before Delta)
    (hrun : TcM.ctxAddrForLbr lbr before = .ok ctxAddr after) :
    (scopedOperationalWhnfContextKeys spec scope).Represents
      lbr ctxAddr Delta :=
  ⟨before, after, hvalid, hctx, hrun, hcapture hctx hrun⟩

/-- Scoped representation exposes the exact digest equation supplied by the
implementation specification. -/
theorem digest_eq {lbr : UInt64} {ctxAddr : Address} {Delta : KVLCtx}
    (hrep : (scopedOperationalWhnfContextKeys spec scope).Represents
      lbr ctxAddr Delta) :
    spec.digest (spec.inputOf lbr Delta) = ctxAddr := by
  obtain ⟨before, after, hvalid, hctx, hrun, _⟩ := hrep
  exact spec.execution hvalid hctx hrun

/-- Scoped representation also exposes finite-list membership independently
of its operational witness. -/
theorem mem {lbr : UInt64} {ctxAddr : Address} {Delta : KVLCtx}
    (hrep : (scopedOperationalWhnfContextKeys spec scope).Represents
      lbr ctxAddr Delta) :
    scope.Contains (spec.inputOf lbr Delta) := by
  obtain ⟨_, _, _, _, _, hmem⟩ := hrep
  exact hmem

end scopedOperationalWhnfContextKeys

/-- Sound interpretation of the production suffix-context address. -/
structure WhnfSuffixModel (trProj : RawProjRel) (world : VerifyWorld) where
  keys : WhnfContextKeys
  represents : ∀ {before after : TcState .anon} {key : Address × Address}
      {Delta : KVLCtx} {source : KExpr .anon},
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta →
    TcM.whnfKey source before = .ok key after →
    keys.Represents source.lbr key.2 Delta
  transport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source result : KExpr .anon},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    WhnfMeaning trProj world keys.uvars Delta source result →
    WhnfMeaning trProj world keys.uvars Delta' source result

namespace WhnfSuffixModel

/-- Construct the operational model once the actual semantic sufficiency
theorem for equal emitted suffix addresses is available.  This removes the
former representation oracle entirely: only semantic transport remains K2
proof debt. -/
def operational {trProj : RawProjRel} {world : VerifyWorld} (uvars : Nat)
    (htransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source result : KExpr .anon},
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta →
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta' →
      WhnfMeaning trProj world uvars Delta source result →
      WhnfMeaning trProj world uvars Delta' source result) :
    WhnfSuffixModel trProj world where
  keys := operationalWhnfContextKeys trProj world uvars
  represents hctx hrun :=
    operationalWhnfContextKeys.represents hctx hrun
  transport hDelta hDelta' hmeaning :=
    htransport hDelta hDelta' hmeaning

/-- The operational model directly supplies the repaired per-call key
representation premise used by the WHNF shells. -/
theorem keyRepresents {trProj : RawProjRel} {world : VerifyWorld}
    (model : WhnfSuffixModel trProj world) {source : KExpr .anon}
    {Delta : KVLCtx} :
    RecM.WhnfKey.Represents model.keys trProj world source Delta := by
  intro before key after hctx hrun
  exact model.represents hctx hrun

/-- Suffix transport plus finite expression-address collision freedom turns
one executed reduction into validity for every supported cache lookup sharing
the key.  Direct-reference authorization stays separate because it is a
property of the generated expression graph, not of context hashing. -/
theorem cacheWriteOracle {trProj : RawProjRel} {fallback : CacheSemantics}
    {world : VerifyWorld} {support : RunSupport}
    (model : WhnfSuffixModel trProj world)
    (hcollision : support.CollisionFree)
    (hreferences : ∀ {kind key source result},
      (kind = .whnfNoDelta ∨ kind = .whnfNoDeltaCheap ∨ kind = .whnf) →
      support source → support result → source.addr = key.1 →
      (CacheEntry.expr kind key result).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    RecM.WhnfCacheWriteOracle model.keys trProj fallback world support := by
  have build : ∀ {kind : ExprCacheKind} {Delta source key result s},
      (kind = .whnfNoDelta ∨ kind = .whnfNoDeltaCheap ∨ kind = .whnf) →
      support source →
      support result →
      model.keys.Matches trProj world s Delta source key →
      WhnfMeaning trProj world model.keys.uvars Delta source result →
      CacheProvenance
        (whnfCacheSemantics model.keys trProj fallback)
        (CacheAuthority.stable world) support (.expr kind key result) := by
    intro kind Delta source key result s hkind hsource hresult hmatch hmeaning
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
    have hvalid : ∀ other, support other → other.addr = key.1 →
        ∀ Delta', model.keys.Represents other.lbr key.2 Delta' →
          WhnfMeaning trProj world model.keys.uvars Delta' other result := by
      intro other hother haddr Delta' hrepresented
      have heq : source = other := by
        have herase := hcollision.expr hsource hother
          (hmatch.sourceAddr.trans haddr.symm)
        simpa only [KExpr.eraseMeta_anon] using herase
      subst other
      exact model.transport hmatch.2.1 hrepresented hmeaning
    cases his <;> exact hvalid
  refine ⟨?_, ?_, ?_⟩
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inl rfl) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr (.inl rfl)) hsource hresult hmatch hmeaning
  · intro Delta source key result s hsource hresult hmatch hmeaning
    exact build (.inr (.inr rfl)) hsource hresult hmatch hmeaning

end WhnfSuffixModel

end Ix.Tc
