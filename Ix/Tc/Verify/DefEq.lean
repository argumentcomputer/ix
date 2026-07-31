import Ix.Tc.Verify.Infer
import Batteries.Data.UInt

/-!
# K2 definitional-equality cache semantics

For checker soundness, a cached `true` must denote Theory definitional
equality.  A cached `false` (including the narrow failure set) can only reject
an otherwise valid declaration, so it carries no acceptance claim here.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

private theorem uint64_max_comm (a b : UInt64) : max a b = max b a := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_max, Nat.max_comm]

/-- A represented context address tied to the actual DefEq key computation.
The expression-address pair is canonicalized separately after this run. -/
def DefEqContextKeys.Matches (keys : WhnfContextKeys)
    (trProj : RawProjRel) (world : VerifyWorld) (s : TcState .anon)
    (Delta : KVLCtx) (a b : KExpr .anon) (ctxAddr : Address) : Prop :=
  CtxRecon world.venv keys.uvars world.nameOf trProj s Delta ∧
    keys.Represents (max a.lbr b.lbr) ctxAddr Delta ∧
    exists s', TcM.defEqCtxKey a b s = .ok ctxAddr s'

namespace TcM

/-- `withEquiv` is state-pure outside the union-find manager.  Naming its
exact result keeps path-halving updates from being treated as semantic cache
or context changes. -/
theorem withEquiv_eq (f : EquivManager → α × EquivManager)
    (s : TcState .anon) :
    TcM.withEquiv f s = .ok (f s.equivManager).1
      {s with equivManager := (f s.equivManager).2} := by
  unfold TcM.withEquiv
  rcases hresult : f s.equivManager with ⟨a, em⟩
  change EStateM.bind
    (fun st : TcState .anon =>
      .ok st.equivManager {st with equivManager := {}}) _ s = _
  unfold EStateM.bind
  simp only
  rw [hresult]
  rfl

/-- Union-find queries and path compression preserve every component of the
fixed-world checker invariant. -/
theorem withEquiv_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (f : EquivManager → α × EquivManager) (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.withEquiv f) (fun _ _ => True) := by
  intro hI
  rw [TcM.withEquiv_eq]
  exact ⟨hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl, trivial⟩

/-- DefEq's shared context key permits only the suffix-memo state frame. -/
theorem defEqCtxKey_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {a b : KExpr .anon}
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.defEqCtxKey a b) (fun _ s' => ContextKeyFrame s s') := by
  unfold TcM.defEqCtxKey
  exact TcM.ctxAddrForLbr_wf
    (fun hI hframe => hframe.whnfStateInv hI) (max a.lbr b.lbr) s

/-- The canonical operational interpretation constructs DefEq context
membership directly from the real `ctxAddrForLbr (max a.lbr b.lbr)` run. -/
theorem defEqCtxKey_operational_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {a b : KExpr .anon}
    {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.defEqCtxKey a b)
      (fun ctxAddr s' =>
        DefEqContextKeys.Matches
          (operationalWhnfContextKeys trProj world uvars) trProj world s
          Delta a b ctxAddr ∧ ContextKeyFrame s s') := by
  intro hI
  have hwf := TcM.defEqCtxKey_wf (layer := layer)
    (semantics := semantics) (trProj := trProj) (world := world)
    (support := support) (uvars := uvars) (Delta := Delta)
    (a := a) (b := b) (s := s) hI
  match hrun : TcM.defEqCtxKey a b s with
  | .ok ctxAddr s' =>
      rw [hrun] at hwf
      exact ⟨hwf.1,
        ⟨⟨hI.2.1,
          operationalWhnfContextKeys.representsCtx hI.2.1 hrun,
          ⟨s', hrun⟩⟩, hwf.2⟩⟩
  | .error err s' =>
      rw [hrun] at hwf
      exact hwf

end TcM

/-- Soundness meaning of one concrete boolean def-eq result. -/
def DefEqMeaning (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (a b : KExpr .anon)
    (answer : Bool) : Prop :=
  answer = true →
    ∃ va vb,
      TrKExprS world.venv uvars world.nameOf trProj Delta a va ∧
      TrKExprS world.venv uvars world.nameOf trProj Delta b vb ∧
      world.venv.IsDefEqU uvars Delta.toCtx va vb

namespace DefEqMeaning

theorem false {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {a b : KExpr .anon} :
    DefEqMeaning trProj world uvars Delta a b false := by
  intro h
  contradiction

/-- The production address-equality fast path is sound on the finite run
support.  In anonymous mode collision freedom turns equal Blake3 addresses
into literal expression equality; Theory reflexivity then supplies the
semantic result. -/
theorem of_addr_beq {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {a b : KExpr .anon} {va : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hctx : CtxRecon world.venv uvars world.nameOf trProj s Delta)
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (haddr : (a.addr == b.addr) = true) :
    DefEqMeaning trProj world uvars Delta a b true := by
  have herase := hcollision.expr haSupport hbSupport (eq_of_beq haddr)
  have hab : a = b := by
    simpa only [KExpr.eraseMeta_anon] using herase
  subst b
  intro _
  exact ⟨va, va, ha, ha,
    Lean4Lean.VEnv.IsDefEqU.refl (theory.exprWF hctx ha)⟩

theorem symm {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {a b : KExpr .anon} {answer : Bool}
    (h : DefEqMeaning trProj world uvars Delta a b answer) :
    DefEqMeaning trProj world uvars Delta b a answer := by
  intro htrue
  obtain ⟨va, vb, ha, hb, hab⟩ := h htrue
  exact ⟨vb, va, hb, ha, hab.symm⟩

theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after) {uvars : Nat} {Delta : KVLCtx}
    {a b : KExpr .anon} {answer : Bool}
    (h : DefEqMeaning trProj before uvars Delta a b answer) :
    DefEqMeaning trProj after uvars Delta a b answer := by
  intro htrue
  obtain ⟨va, vb, ha, hb, hab⟩ := h htrue
  refine ⟨va, vb, ?_, ?_, hab.mono hle.venv⟩
  · simpa only [← hle.nameOf] using ha.mono hle.venv
  · simpa only [← hle.nameOf] using hb.mono hle.venv

/-- Convert cache meaning to the exact caller translations used by
`Methods.WF.isDefEq`. -/
theorem of_translations {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {a b : KExpr .anon} {va vb : VExpr} {answer : Bool}
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb)
    (h : DefEqMeaning trProj world uvars Delta a b answer)
    (htrue : answer = true) :
    world.venv.IsDefEqU uvars Delta.toCtx va vb := by
  obtain ⟨cachedA, cachedB, hcachedA, hcachedB, hcached⟩ := h htrue
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have haEq := hcachedA.uniq world.venvWF theory.literalWF
    theory.projections hctx ha
  have hbEq := hcachedB.uniq world.venvWF theory.literalWF
    theory.projections hctx hb
  exact haEq.symm.trans world.venvWF hDelta <|
    hcached.trans world.venvWF hDelta hbEq

end DefEqMeaning

/-! ## Joint suffix semantics

The production context key is itself a Blake3 digest.  Expression-address
collision freedom does not imply injectivity of this second, composite hash.
Consequently the three semantic transports below remain an explicit boundary:
they may later be proved from a finite context-digest collision hypothesis and
the declarative suffix-closure theorem, but must not be inferred from a bare
address equality. -/

/-- One context-key interpretation sufficient for every K1/K2 semantic cache
family.  Operational representation is shared, while WHNF, inference, and
DefEq each state their own context-transport consequence. -/
structure KernelSuffixModel (trProj : RawProjRel) (world : VerifyWorld) where
  keys : WhnfContextKeys
  represents : ∀ {before after : TcState .anon} {key : Address × Address}
      {Delta : KVLCtx} {source : KExpr .anon},
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta →
    TcM.whnfKey source before = .ok key after →
    keys.Represents source.lbr key.2 Delta
  whnfTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source result : KExpr .anon},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    WhnfMeaning trProj world keys.uvars Delta source result →
    WhnfMeaning trProj world keys.uvars Delta' source result
  inferTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source ty : KExpr .anon},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    InferMeaning trProj world keys.uvars Delta source ty →
    InferMeaning trProj world keys.uvars Delta' source ty
  defEqTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {a b : KExpr .anon} {answer : Bool},
    keys.Represents (max a.lbr b.lbr) ctxAddr Delta →
    keys.Represents (max a.lbr b.lbr) ctxAddr Delta' →
    DefEqMeaning trProj world keys.uvars Delta a b answer →
    DefEqMeaning trProj world keys.uvars Delta' a b answer

/-- Declarative sufficiency of one normalized context-digest input.  This is
the semantic half of K2's suffix theorem: equality of the exact input—not
equality of its Blake3 output—must preserve each judgment family at the
radius that production requested. -/
structure ContextSuffixSemantics {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (spec : ContextDigestSpec trProj world uvars) : Prop where
  whnf : ∀ {Delta Delta' : KVLCtx} {source result : KExpr .anon},
    spec.inputOf source.lbr Delta = spec.inputOf source.lbr Delta' →
    WhnfMeaning trProj world uvars Delta source result →
    WhnfMeaning trProj world uvars Delta' source result
  infer : ∀ {Delta Delta' : KVLCtx} {source ty : KExpr .anon},
    spec.inputOf source.lbr Delta = spec.inputOf source.lbr Delta' →
    InferMeaning trProj world uvars Delta source ty →
    InferMeaning trProj world uvars Delta' source ty
  defEq : ∀ {Delta Delta' : KVLCtx} {a b : KExpr .anon} {answer : Bool},
    spec.inputOf (max a.lbr b.lbr) Delta =
        spec.inputOf (max a.lbr b.lbr) Delta' →
    DefEqMeaning trProj world uvars Delta a b answer →
    DefEqMeaning trProj world uvars Delta' a b answer

/-- Joint suffix model whose representation theorem is restricted to states
in one explicit domain.  This is the correct shape for a finite execution
scope: unlike `KernelSuffixModel`, it does not quantify key construction over
every context-reconciled state in existence. -/
structure ScopedKernelSuffixModel (trProj : RawProjRel)
    (world : VerifyWorld) where
  keys : WhnfContextKeys
  StateInScope : TcState .anon → Prop
  represents : ∀ {before after : TcState .anon} {key : Address × Address}
      {Delta : KVLCtx} {source : KExpr .anon},
    StateInScope before →
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta →
    TcM.whnfKey source before = .ok key after →
    keys.Represents source.lbr key.2 Delta
  whnfTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source result : KExpr .anon},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    WhnfMeaning trProj world keys.uvars Delta source result →
    WhnfMeaning trProj world keys.uvars Delta' source result
  inferTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source ty : KExpr .anon},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    InferMeaning trProj world keys.uvars Delta source ty →
    InferMeaning trProj world keys.uvars Delta' source ty
  defEqTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {a b : KExpr .anon} {answer : Bool},
    keys.Represents (max a.lbr b.lbr) ctxAddr Delta →
    keys.Represents (max a.lbr b.lbr) ctxAddr Delta' →
    DefEqMeaning trProj world keys.uvars Delta a b answer →
    DefEqMeaning trProj world keys.uvars Delta' a b answer

namespace ScopedKernelSuffixModel

/-- Construct the genuinely run-scoped joint model.  State membership is
exactly finite-scope capture for that state; no universal reachability claim
is smuggled into the constructor. -/
def finiteOperational {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (spec : ContextDigestSpec trProj world uvars)
    (scope : ContextDigestScope spec) (hcollision : scope.CollisionFree)
    (hsemantics : ContextSuffixSemantics spec) :
    ScopedKernelSuffixModel trProj world where
  keys := scopedOperationalWhnfContextKeys spec scope
  StateInScope before := spec.StateValid before ∧ scope.Captures before
  represents hscope hctx hrun :=
    scopedOperationalWhnfContextKeys.represents hscope.1 hscope.2 hctx hrun
  whnfTransport hDelta hDelta' hmeaning := by
    apply hsemantics.whnf _ hmeaning
    apply hcollision
    · exact scopedOperationalWhnfContextKeys.mem hDelta
    · exact scopedOperationalWhnfContextKeys.mem hDelta'
    · exact (scopedOperationalWhnfContextKeys.digest_eq hDelta).trans
        (scopedOperationalWhnfContextKeys.digest_eq hDelta').symm
  inferTransport hDelta hDelta' hmeaning := by
    apply hsemantics.infer _ hmeaning
    apply hcollision
    · exact scopedOperationalWhnfContextKeys.mem hDelta
    · exact scopedOperationalWhnfContextKeys.mem hDelta'
    · exact (scopedOperationalWhnfContextKeys.digest_eq hDelta).trans
        (scopedOperationalWhnfContextKeys.digest_eq hDelta').symm
  defEqTransport hDelta hDelta' hmeaning := by
    apply hsemantics.defEq _ hmeaning
    apply hcollision
    · exact scopedOperationalWhnfContextKeys.mem hDelta
    · exact scopedOperationalWhnfContextKeys.mem hDelta'
    · exact (scopedOperationalWhnfContextKeys.digest_eq hDelta).trans
        (scopedOperationalWhnfContextKeys.digest_eq hDelta').symm

/-- Forget the state domain only after proving that it contains every state
quantified by the legacy universal interface.  Finite run proofs should use
the scoped model directly; this conversion is intentionally stronger. -/
def toKernelSuffixModel {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (hcomplete : ∀ before, model.StateInScope before) :
    KernelSuffixModel trProj world where
  keys := model.keys
  represents hctx hrun := model.represents (hcomplete _) hctx hrun
  whnfTransport := model.whnfTransport
  inferTransport := model.inferTransport
  defEqTransport := model.defEqTransport

end ScopedKernelSuffixModel

namespace KernelSuffixModel

/-- Forget the K2 transports and recover exactly the K1 suffix model. -/
def toWhnfSuffixModel {trProj : RawProjRel} {world : VerifyWorld}
    (model : KernelSuffixModel trProj world) :
    WhnfSuffixModel trProj world where
  keys := model.keys
  represents := model.represents
  transport := model.whnfTransport

/-- Build the joint model over the canonical operational representation.
Only the three semantic same-digest transports remain as assumptions; actual
key membership is derived from production executions. -/
def operational {trProj : RawProjRel} {world : VerifyWorld} (uvars : Nat)
    (hwhnf : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source result : KExpr .anon},
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta →
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta' →
      WhnfMeaning trProj world uvars Delta source result →
      WhnfMeaning trProj world uvars Delta' source result)
    (hinfer : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source ty : KExpr .anon},
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta →
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta' →
      InferMeaning trProj world uvars Delta source ty →
      InferMeaning trProj world uvars Delta' source ty)
    (hdefeq : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {a b : KExpr .anon} {answer : Bool},
      (operationalWhnfContextKeys trProj world uvars).Represents
        (max a.lbr b.lbr) ctxAddr Delta →
      (operationalWhnfContextKeys trProj world uvars).Represents
        (max a.lbr b.lbr) ctxAddr Delta' →
      DefEqMeaning trProj world uvars Delta a b answer →
      DefEqMeaning trProj world uvars Delta' a b answer) :
    KernelSuffixModel trProj world where
  keys := operationalWhnfContextKeys trProj world uvars
  represents hctx hrun :=
    operationalWhnfContextKeys.represents hctx hrun
  whnfTransport hDelta hDelta' hmeaning :=
    hwhnf hDelta hDelta' hmeaning
  inferTransport hDelta hDelta' hmeaning :=
    hinfer hDelta hDelta' hmeaning
  defEqTransport hDelta hDelta' hmeaning :=
    hdefeq hDelta hDelta' hmeaning

/-- Universal corollary of the finite scoped construction.  It is available
only when every state quantified by `KernelSuffixModel` satisfies both the
digest state invariant and finite-scope capture.  The proof uses separately
named facts:

* `ContextDigestSpec.StateValid` and `execution` connect real key computation
  (including memo hits) to the exact normalized digest input;
* `ContextDigestScope.Captures` keeps every admitted execution inside the
  finite list;
* `ContextDigestScope.CollisionFree` turns equal composite digests into
  equal normalized inputs only on that list; and
* `ContextSuffixSemantics` transports the three declarative meanings across
  equal inputs.

No expression-address collision theorem appears in this construction. -/
def finiteOperational {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (spec : ContextDigestSpec trProj world uvars)
    (scope : ContextDigestScope spec)
    (hstates : ∀ before, spec.StateValid before ∧ scope.Captures before)
    (hcollision : scope.CollisionFree)
    (hsemantics : ContextSuffixSemantics spec) :
    KernelSuffixModel trProj world :=
  (ScopedKernelSuffixModel.finiteOperational
    spec scope hcollision hsemantics).toKernelSuffixModel hstates

end KernelSuffixModel

/-- Exact validity for full/cheap def-eq maps and the negative failure set. -/
def DefEqCacheValid (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .defEq _ key answer =>
      ∀ a, support a → a.addr = key.1 →
        ∀ b, support b → b.addr = key.2.1 →
          ∀ Delta, keys.Represents (max a.lbr b.lbr) key.2.2 Delta →
            DefEqMeaning trProj authority.world keys.uvars Delta a b answer
  | .defEqFailure _ => True
  | entry => fallback.Valid authority support entry

namespace DefEqCacheValid

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {before after : CacheAuthority}
    {support : RunSupport} {entry : CacheEntry} (hle : before ≤ after)
    (h : DefEqCacheValid keys trProj fallback before support entry) :
    DefEqCacheValid keys trProj fallback after support entry := by
  cases entry with
  | defEq kind key answer =>
      intro a ha haddrA b hb haddrB Delta hctx
      exact (h a ha haddrA b hb haddrB Delta hctx).mono hle.world
  | defEqFailure => trivial
  | expr | unfold | natSuccStuck | isProp | isRec | recursor | recMajors |
      blockPeer | blockResult =>
      exact fallback.mono hle h

theorem result {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {key : Address × Address × Address} {answer : Bool}
    {a b : KExpr .anon}
    (h : DefEqCacheValid keys trProj fallback authority support
      (.defEq kind key answer))
    (ha : support a) (haddrA : a.addr = key.1)
    (hb : support b) (haddrB : b.addr = key.2.1)
    {Delta : KVLCtx}
    (hctx : keys.Represents (max a.lbr b.lbr) key.2.2 Delta) :
    DefEqMeaning trProj authority.world keys.uvars Delta a b answer :=
  h a ha haddrA b hb haddrB Delta hctx

end DefEqCacheValid

/-- Overlay K2 def-eq meanings on K1+inference cache semantics. -/
def defEqCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := DefEqCacheValid keys trProj fallback
  mono := DefEqCacheValid.mono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err

/-- Canonical K1+K2 semantic stack.  WHNF stays outermost so all K1 driver
theorems apply unchanged; inference and def-eq occupy precisely the fallback
families they own. -/
def kernelCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel) :
    CacheSemantics :=
  whnfCacheSemantics keys trProj <|
    inferCacheSemantics keys trProj <|
      defEqCacheSemantics keys trProj <|
        isRecCacheSemantics CacheSemantics.blockErrorsOnly

/-- The canonical cache stack owns both final and conservative/provisional
recursion-classifier entries for every trusted anonymous identifier. -/
theorem kernelCacheSemantics_isRec_valid
    {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport}
    {ind : KId .anon} {value : Bool}
    (htrusted : authority.world.trusted ind) :
    (kernelCacheSemantics keys trProj).Valid authority support
      (.isRec ind.addr value) := by
  change IsRecCacheValid CacheSemantics.blockErrorsOnly authority support
    (.isRec ind.addr value)
  exact IsRecCacheValid.trusted
    (fallback := CacheSemantics.blockErrorsOnly) (support := support)
    (value := value) htrusted

namespace CacheProvenance

theorem kernelWhnfMeaningOfMatches {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {value source : KExpr .anon}
    {s : TcState .anon} {Delta : KVLCtx}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.expr kind key value))
    (hkind : kind.IsWhnf) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Delta source key) :
    WhnfMeaning trProj authority.world keys.uvars Delta source value :=
  WhnfCacheValid.expr hkind h.valid hsource hmatch.sourceAddr hmatch.2.1

theorem kernelInferMeaningOfMatches {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : ExprCacheKind}
    {key : Address × Address} {ty source : KExpr .anon}
    {s : TcState .anon} {Delta : KVLCtx}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.expr kind key ty))
    (hkind : kind.IsInfer) (hsource : support source)
    (hmatch : keys.Matches trProj authority.world s Delta source key) :
    InferMeaning trProj authority.world keys.uvars Delta source ty := by
  cases hkind with
  | infer =>
      apply InferCacheValid.expr
        (fallback := defEqCacheSemantics keys trProj
          CacheSemantics.blockErrorsOnly) .infer (hsource := hsource)
        (haddr := hmatch.sourceAddr) (hctx := hmatch.2.1)
      simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid] using
        h.valid
  | inferOnly =>
      apply InferCacheValid.expr
        (fallback := defEqCacheSemantics keys trProj
          CacheSemantics.blockErrorsOnly) .inferOnly (hsource := hsource)
        (haddr := hmatch.sourceAddr) (hctx := hmatch.2.1)
      simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid] using
        h.valid

theorem kernelDefEqMeaning {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {key : Address × Address × Address} {answer : Bool}
    {a b : KExpr .anon}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.defEq kind key answer))
    (ha : support a) (haddrA : a.addr = key.1)
    (hb : support b) (haddrB : b.addr = key.2.1)
    {Delta : KVLCtx}
    (hctx : keys.Represents (max a.lbr b.lbr) key.2.2 Delta) :
    DefEqMeaning trProj authority.world keys.uvars Delta a b answer := by
  apply DefEqCacheValid.result (keys := keys) (trProj := trProj)
    (fallback := CacheSemantics.blockErrorsOnly) (kind := kind)
    (ha := ha) (haddrA := haddrA) (hb := hb) (haddrB := haddrB)
    (hctx := hctx)
  simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid,
    inferCacheSemantics, InferCacheValid] using h.valid

/-- Eliminate a physical DefEq cache entry in the caller's original order.
The production key stores the canonical address order, so the swapped branch
uses semantic symmetry explicitly rather than silently identifying operands. -/
theorem kernelDefEqMeaningCanonical {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {ctxAddr : Address} {answer : Bool} {a b : KExpr .anon}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support
      (.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer))
    (ha : support a) (hb : support b)
    {Delta : KVLCtx}
    (hctx : keys.Represents (max a.lbr b.lbr) ctxAddr Delta) :
    DefEqMeaning trProj authority.world keys.uvars Delta a b answer := by
  by_cases horder : a.addr.cmpBytes b.addr != .gt
  · have hpair : canonicalPair a.addr b.addr = (a.addr, b.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at h
    exact h.kernelDefEqMeaning ha rfl hb rfl hctx
  · have hpair : canonicalPair a.addr b.addr = (b.addr, a.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at h
    have hctx' : keys.Represents (max b.lbr a.lbr) ctxAddr Delta := by
      simpa [uint64_max_comm] using hctx
    exact (h.kernelDefEqMeaning hb rfl ha rfl hctx').symm

theorem defEqMeaning {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {key : Address × Address × Address} {answer : Bool}
    {a b : KExpr .anon}
    (h : CacheProvenance (defEqCacheSemantics keys trProj fallback)
      authority support (.defEq kind key answer))
    (ha : support a) (haddrA : a.addr = key.1)
    (hb : support b) (haddrB : b.addr = key.2.1)
    {Delta : KVLCtx}
    (hctx : keys.Represents (max a.lbr b.lbr) key.2.2 Delta) :
    DefEqMeaning trProj authority.world keys.uvars Delta a b answer :=
  DefEqCacheValid.result (keys := keys) (trProj := trProj)
    (fallback := fallback) (kind := kind) h.valid ha haddrA hb haddrB hctx

end CacheProvenance

namespace KernelSuffixModel

/-- Turn one executed inference result into collision-robust provenance for
either inference cache.  Validity quantifies over every supported expression
sharing the source address and every context sharing the suffix digest. -/
theorem inferProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (hcollision : support.CollisionFree)
    {kind : ExprCacheKind} (hkind : kind.IsInfer)
    {Delta : KVLCtx} {source ty : KExpr .anon}
    {key : Address × Address} {s : TcState .anon}
    (hsource : support source) (hty : support ty)
    (hmatch : model.keys.Matches trProj world s Delta source key)
    (hmeaning : InferMeaning trProj world model.keys.uvars Delta source ty)
    (hreferences : (CacheEntry.expr kind key ty).ReferencesAuthorized
      (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support (.expr kind key ty) := by
  have hall : ∀ other, support other → other.addr = key.1 →
      ∀ Delta', model.keys.Represents other.lbr key.2 Delta' →
        InferMeaning trProj world model.keys.uvars Delta' other ty := by
    intro other hother haddr Delta' hrepresented
    have heq : source = other := by
      have herase := hcollision.expr hsource hother
        (hmatch.sourceAddr.trans haddr.symm)
      simpa only [KExpr.eraseMeta_anon] using herase
    subst other
    exact model.inferTransport hmatch.2.1 hrepresented hmeaning
  refine ⟨⟨⟨source, hsource, hmatch.sourceAddr⟩, hty⟩,
    hreferences, ?_⟩
  cases hkind with
  | infer =>
      have hvalid : InferCacheValid model.keys trProj
          (defEqCacheSemantics model.keys trProj
            CacheSemantics.blockErrorsOnly)
          (CacheAuthority.stable world) support
          (.expr .infer key ty) := hall
      simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid] using
        hvalid
  | inferOnly =>
      have hvalid : InferCacheValid model.keys trProj
          (defEqCacheSemantics model.keys trProj
            CacheSemantics.blockErrorsOnly)
          (CacheAuthority.stable world) support
          (.expr .inferOnly key ty) := hall
      simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid] using
        hvalid

/-- Turn one executed DefEq result into collision-robust provenance for the
canonicalized production key.  The swapped canonical-pair branch transports
the semantic result through symmetry explicitly. -/
theorem defEqProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (hcollision : support.CollisionFree) (kind : DefEqCacheKind)
    {Delta : KVLCtx} {a b : KExpr .anon} {answer : Bool}
    {ctxAddr : Address}
    (ha : support a) (hb : support b)
    (hctx : model.keys.Represents (max a.lbr b.lbr) ctxAddr Delta)
    (hmeaning : DefEqMeaning trProj world model.keys.uvars Delta a b answer)
    (hreferences :
      (CacheEntry.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) answer) := by
  by_cases horder : a.addr.cmpBytes b.addr != .gt
  · have hpair : canonicalPair a.addr b.addr = (a.addr, b.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at hreferences ⊢
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hreferences, ?_⟩
    have hvalid : DefEqCacheValid model.keys trProj
        CacheSemantics.blockErrorsOnly (CacheAuthority.stable world) support
        (.defEq kind (a.addr, b.addr, ctxAddr) answer) := by
      intro otherA hotherA haddrA otherB hotherB haddrB Delta' hrepresented
      have heqA : a = otherA := by
        have herase := hcollision.expr ha hotherA haddrA.symm
        simpa only [KExpr.eraseMeta_anon] using herase
      have heqB : b = otherB := by
        have herase := hcollision.expr hb hotherB haddrB.symm
        simpa only [KExpr.eraseMeta_anon] using herase
      subst otherA
      subst otherB
      exact model.defEqTransport hctx hrepresented hmeaning
    simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid
  · have hpair : canonicalPair a.addr b.addr = (b.addr, a.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at hreferences ⊢
    refine ⟨⟨⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩⟩, hreferences, ?_⟩
    have hvalid : DefEqCacheValid model.keys trProj
        CacheSemantics.blockErrorsOnly (CacheAuthority.stable world) support
        (.defEq kind (b.addr, a.addr, ctxAddr) answer) := by
      intro otherA hotherA haddrA otherB hotherB haddrB Delta' hrepresented
      have heqA : b = otherA := by
        have herase := hcollision.expr hb hotherA haddrA.symm
        simpa only [KExpr.eraseMeta_anon] using herase
      have heqB : a = otherB := by
        have herase := hcollision.expr ha hotherB haddrB.symm
        simpa only [KExpr.eraseMeta_anon] using herase
      subst otherA
      subst otherB
      have hctx' : model.keys.Represents
          (max b.lbr a.lbr) ctxAddr Delta := by
        simpa [uint64_max_comm] using hctx
      exact model.defEqTransport hctx' hrepresented hmeaning.symm
    simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid

/-- A narrow same-head failure marker is rejection-only, so it needs no
semantic transport.  It still records finite source witnesses and explicit
reference authorization for the canonical operand pair. -/
theorem defEqFailureProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    {a b : KExpr .anon} {ctxAddr : Address}
    (ha : support a) (hb : support b)
    (hreferences :
      (CacheEntry.defEqFailure
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr)).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.defEqFailure
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr)) := by
  by_cases horder : a.addr.cmpBytes b.addr != .gt
  · have hpair : canonicalPair a.addr b.addr = (a.addr, b.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at hreferences ⊢
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hreferences, ?_⟩
    have hvalid : DefEqCacheValid model.keys trProj
        CacheSemantics.blockErrorsOnly (CacheAuthority.stable world) support
        (.defEqFailure (a.addr, b.addr, ctxAddr)) := trivial
    simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid
  · have hpair : canonicalPair a.addr b.addr = (b.addr, a.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at hreferences ⊢
    refine ⟨⟨⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩⟩, hreferences, ?_⟩
    have hvalid : DefEqCacheValid model.keys trProj
        CacheSemantics.blockErrorsOnly (CacheAuthority.stable world) support
        (.defEqFailure (b.addr, a.addr, ctxAddr)) := trivial
    simpa [kernelCacheSemantics, whnfCacheSemantics, WhnfCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid

end KernelSuffixModel

namespace RecM

namespace DefEqCacheUpdate

/-- Installing a certified full DefEq answer changes only the full result
partition and preserves the complete checker invariant. -/
theorem full_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address × Address} {answer : Bool}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.defEq .full key answer)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        defEqCache := s.env.defEqCache.insert key answer}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEq hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Installing a certified cheap DefEq answer preserves partition separation;
promotion of a sound `true` into the full map is a distinct update. -/
theorem cheap_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address × Address} {answer : Bool}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.defEq .cheap key answer)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        defEqCheapCache := s.env.defEqCheapCache.insert key answer}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEqCheap hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Recording a certified narrow failure marker preserves the checker
invariant.  This write cannot contribute to an acceptance proof. -/
theorem failure_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address × Address}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.defEqFailure key)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        defEqFailure := s.env.defEqFailure.insert key}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEqFailure hnew
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end DefEqCacheUpdate

/-- Exact production execution for the first positive full DefEq cache hit in
non-cheap mode.  The only post-hit mutation is union-find insertion; the
semantic cache maps are unchanged. -/
theorem isDefEq_fullHit_true
    {methods : Methods .anon} {a b : KExpr .anon}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv (a.addr, ctxAddr) (b.addr, ctxAddr)) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hhit : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true) :
    (isDefEq a b).run methods s = .ok true
      {s4 with equivManager := (s4.equivManager.addEquiv
        (a.addr, ctxAddr) (b.addr, ctxAddr))} := by
  unfold isDefEq
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}")) _ s = _
  unfold EStateM.bind
  rw [htrace]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}))
      _ s1 = _
  unfold EStateM.bind
  rw [hstats]
  simp only [haddr, Bool.false_eq_true, if_false]
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.defEqCtxKey a b) _ s2 = _
  unfold EStateM.bind
  rw [hctx]
  simp only
  change ReaderT.run
    ((liftM (TcM.withEquiv
      (·.isEquiv (a.addr, ctxAddr) (b.addr, ctxAddr))) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv (a.addr, ctxAddr) (b.addr, ctxAddr))) _ s3 = _
  unfold EStateM.bind
  rw [hequiv]
  simp only [Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hcheap]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hhit, if_true]
  rfl

/-- A positive non-cheap full-cache hit is accepted by the real DefEq entry
point.  Context membership comes from the executed `defEqCtxKey`; canonical
operand ordering is eliminated through cache provenance, and the union-find
write is proved semantically inert. -/
theorem isDefEq_fullHit_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {a b : KExpr .anon} {va vb : VExpr}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv (a.addr, ctxAddr) (b.addr, ctxAddr)) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hhit : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true)
    (hI : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb) :
    let final := {s4 with equivManager := (s4.equivManager.addEquiv
      (a.addr, ctxAddr) (b.addr, ctxAddr))}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer
        (kernelCacheSemantics
          (operationalWhnfContextKeys trProj world uvars) trProj)
        trProj world support uvars Delta final ∧
      world.venv.IsDefEqU uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hI1 := htraceWf.1
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1) hI1
  rw [hstats] at hstatsWf
  have hI2 := hstatsWf.1
  have hctxWf :=
    (TcM.defEqCtxKey_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) (a := a) (b := b) (s := s2)) hI2
  rw [hctx] at hctxWf
  have hI3 := hctxWf.1
  have hequivWf :=
    (TcM.withEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta)
      (·.isEquiv (a.addr, ctxAddr) (b.addr, ctxAddr)) s3) hI3
  rw [hequiv] at hequivWf
  have hI4 := hequivWf.1
  have hctxRun :
      TcM.ctxAddrForLbr (max a.lbr b.lbr) s2 = .ok ctxAddr s3 := by
    simpa [TcM.defEqCtxKey] using hctx
  have hrepresented := operationalWhnfContextKeys.representsCtx
    hI2.2.1 hctxRun
  have hprovenance := hI4.1.caches.hit (.defEq hhit)
  have hmeaning := hprovenance.kernelDefEqMeaningCanonical
    haSupport hbSupport hrepresented
  have hsemantic := DefEqMeaning.of_translations theory hI4.2.1.wf
    ha hb hmeaning rfl
  have hfinal : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta
      {s4 with equivManager := (s4.equivManager.addEquiv
        (a.addr, ctxAddr) (b.addr, ctxAddr))} :=
    hI4.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl
  exact ⟨isDefEq_fullHit_true htrace hstats haddr hctx hequiv hcheap hhit,
    hfinal, hsemantic⟩

/-- The first production DefEq branch is sound under the run-scoped collision
hypothesis.  Trace and statistics instrumentation preserve the semantic
state, and an address hit is discharged by `DefEqMeaning.of_addr_beq`. -/
theorem isDefEq_addrEq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {va vb : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb)
    (haddr : (a.addr == b.addr) = true) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isDefEq a b)
      (fun answer _ => answer = true ->
        world.venv.IsDefEqU uvars Delta.toCtx va vb) := by
  unfold isDefEq
  apply RecM.WF.bind
  · apply RecM.WF.liftTcM
    exact TcM.stepTrace_whnf_wf "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s
  · intro _ s1 _
    apply RecM.WF.bind
    · apply RecM.WF.liftTcM
      exact TcM.bumpStats_whnf_wf
        (fun st => {st with deqCalls := st.deqCalls + 1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1
    · intro _ s2 _
      simp only [haddr, if_true]
      apply RecM.WF.pure
      intro hI htrue
      exact DefEqMeaning.of_translations theory hI.2.1.wf ha hb
        (DefEqMeaning.of_addr_beq theory hI.2.1 hcollision
          haSupport hbSupport ha haddr) htrue

/-- A production full inference-cache hit is semantically accepted from the
canonical operational context-key interpretation.  Provenance is read from
the post-key invariant, while the actual key run supplies context membership. -/
theorem inferWith_fullHit_acceptance
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source cached : KExpr .anon}
    {sourceV : VExpr} {key : Address × Address}
    {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (hkey : TcM.inferKey source s = .ok key s')
    (hhit : s'.env.inferCache[key]? = some cached)
    (hI : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta s)
    (hsupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    (inferWith inferRec source).run methods s = .ok cached s' ∧
      WhnfStateInv layer
        (kernelCacheSemantics
          (operationalWhnfContextKeys trProj world uvars) trProj)
        trProj world support uvars Delta s' ∧
      support cached ∧
        InferPost trProj world uvars Delta sourceV cached := by
  have hwf :=
    (TcM.inferKey_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) (source := source) (s := s)) hI
  rw [hkey] at hwf
  have hrun : TcM.whnfKey source s = .ok key s' := by
    simpa using hkey
  have hmatch :
      (operationalWhnfContextKeys trProj world uvars).Matches trProj world
        s Delta source key :=
    ⟨hI.2.1,
      operationalWhnfContextKeys.represents hI.2.1 hrun,
      ⟨s', hrun⟩⟩
  have hprovenance := hwf.1.1.caches.hit (.infer hhit)
  have hmeaning := hprovenance.kernelInferMeaningOfMatches
    .infer hsupport hmatch
  exact ⟨inferWith_fullHit hkey hhit, hwf.1,
    hprovenance.supported.2,
    hmeaning.post theory hI.2.1.wf hsource⟩

/-- The infer-only partition has the same semantic acceptance theorem.  Its
policy guard is captured before key computation; the key frame cannot alter
that guard. -/
theorem inferWith_inferOnlyHit_acceptance
    {inferRec : KExpr .anon -> RecM .anon (KExpr .anon)}
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {source cached : KExpr .anon}
    {sourceV : VExpr} {key : Address × Address}
    {s s' : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (hpolicy : s.inferOnly = true)
    (hkey : TcM.inferKey source s = .ok key s')
    (hfullMiss : s'.env.inferCache[key]? = none)
    (hhit : s'.env.inferOnlyCache[key]? = some cached)
    (hI : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta s)
    (hsupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    (inferWith inferRec source).run methods s = .ok cached s' ∧
      WhnfStateInv layer
        (kernelCacheSemantics
          (operationalWhnfContextKeys trProj world uvars) trProj)
        trProj world support uvars Delta s' ∧
      support cached ∧
        InferPost trProj world uvars Delta sourceV cached := by
  have hwf :=
    (TcM.inferKey_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) (source := source) (s := s)) hI
  rw [hkey] at hwf
  have hrun : TcM.whnfKey source s = .ok key s' := by
    simpa using hkey
  have hmatch :
      (operationalWhnfContextKeys trProj world uvars).Matches trProj world
        s Delta source key :=
    ⟨hI.2.1,
      operationalWhnfContextKeys.represents hI.2.1 hrun,
      ⟨s', hrun⟩⟩
  have hprovenance := hwf.1.1.caches.hit (.inferOnly hhit)
  have hmeaning := hprovenance.kernelInferMeaningOfMatches
    .inferOnly hsupport hmatch
  exact ⟨inferWith_inferOnlyHit hpolicy hkey hfullMiss hhit, hwf.1,
    hprovenance.supported.2,
    hmeaning.post theory hI.2.1.wf hsource⟩

end RecM

end Ix.Tc
