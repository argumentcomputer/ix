import Ix.Tc.Verify.Infer
import Ix.Tc.Verify.Whnf.Closure
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

namespace EqKey

/-- Propositional contract for the runtime guard on root-derived DefEq cache
lookups.  This is the exact scope information consumed by the semantic branch
proof below. -/
theorem rootCacheScopeMatches_iff (left right : EqKey)
    (ctxAddr : Address) (lbr : UInt64) :
    left.rootCacheScopeMatches right ctxAddr lbr = true ↔
      left.ctxAddr = ctxAddr ∧ right.ctxAddr = ctxAddr ∧
      left.lbr = lbr ∧ right.lbr = lbr ∧
      max left.exprLbr right.exprLbr = lbr := by
  simp [EqKey.rootCacheScopeMatches, and_assoc]

end EqKey

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

/-- A union-find operation preserves the fixed-world checker invariant once
its updated manager has been proved valid.  The preservation premise is
deliberately explicit: arbitrary mutation of the manager is not semantic
bookkeeping. -/
theorem withEquiv_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (f : EquivManager → α × EquivManager)
    (hf : ∀ em, EquivManager.WF
        (semantics.Equiv (CacheAuthority.stable world) support) em →
      EquivManager.WF
        (semantics.Equiv (CacheAuthority.stable world) support) (f em).2)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.withEquiv f) (fun _ _ => True) := by
  intro hI
  rw [TcM.withEquiv_eq]
  exact ⟨hI.setEquivManager _ (hf _ hI.1.equivalences), trivial⟩

/-- The production equivalence query performs only verified path compression;
a positive Boolean additionally exposes the semantic relation represented by
the manager. -/
theorem withEquiv_isEquiv_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} (left right : EqKey)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.withEquiv (·.isEquiv left right))
      (fun answer _ => answer = true →
        semantics.Equiv (CacheAuthority.stable world) support left right) := by
  intro hI
  rw [TcM.withEquiv_eq]
  have hquery := hI.1.equivalences.isEquiv
    (semantics.equivEquivalence (CacheAuthority.stable world) support)
    left right
  rcases hresult : s.equivManager.isEquiv left right with ⟨answer, manager⟩
  rw [hresult] at hquery
  exact ⟨hI.setEquivManager manager hquery.1, hquery.2⟩

/-- DefEq's two-root second-chance query preserves the manager and returns a
semantic relation from each original key to any representative it exposes. -/
theorem withEquiv_findRootKeys_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} (left right : EqKey)
    (s : TcState .anon) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.withEquiv fun em =>
        let (leftRoot, em) := em.findRootKey left
        let (rightRoot, em) := em.findRootKey right
        ((leftRoot, rightRoot), em))
      (fun roots _ =>
        (∀ root, roots.1 = some root →
          semantics.Equiv (CacheAuthority.stable world) support left root) ∧
        (∀ root, roots.2 = some root →
          semantics.Equiv (CacheAuthority.stable world) support right root)) := by
  intro hI
  rw [TcM.withEquiv_eq]
  have hroots := hI.1.equivalences.findRootKeys
    (semantics.equivEquivalence (CacheAuthority.stable world) support)
    left right
  rcases hleft : s.equivManager.findRootKey left with ⟨leftRoot, manager₁⟩
  rcases hright : manager₁.findRootKey right with ⟨rightRoot, manager₂⟩
  simp only [hleft, hright] at hroots ⊢
  exact ⟨hI.setEquivManager manager₂ hroots.1, hroots.2⟩

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

namespace WhnfStateInv

/-- Record one already-proved semantic equality in the concrete manager. -/
theorem addEquiv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {left right : EqKey}
    (h : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hrel : semantics.Equiv (CacheAuthority.stable world) support left right) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with equivManager := s.equivManager.addEquiv left right} :=
  h.setEquivManager _ <|
    h.1.equivalences.addEquiv
      (semantics.equivEquivalence (CacheAuthority.stable world) support) hrel

end WhnfStateInv

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

/-- Soundness meaning of one memoized proposition classifier result.  The
classifier is conservative on `false`; a `true` result retains a structural
translation of the concrete type with type `Sort 0`. -/
def IsPropMeaning (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (source : KExpr .anon)
    (answer : Bool) : Prop :=
  answer = true →
    ∃ sourceV,
      TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV ∧
      world.venv.HasType uvars Delta.toCtx sourceV (.sort .zero)

namespace IsPropMeaning

theorem false {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon} :
    IsPropMeaning trProj world uvars Delta source false := by
  intro htrue
  contradiction

theorem mono {trProj : RawProjRel} {before after : VerifyWorld}
    (hle : before ≤ after) {uvars : Nat} {Delta : KVLCtx}
    {source : KExpr .anon} {answer : Bool}
    (h : IsPropMeaning trProj before uvars Delta source answer) :
    IsPropMeaning trProj after uvars Delta source answer := by
  intro htrue
  obtain ⟨sourceV, hsource, htype⟩ := h htrue
  refine ⟨sourceV, ?_, htype.mono hle.venv⟩
  simpa only [← hle.nameOf] using hsource.mono hle.venv

/-- Reconcile cached proposition meaning with the caller's particular
structural translation. -/
theorem of_translation {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source : KExpr .anon} {sourceV : VExpr} {answer : Bool}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (h : IsPropMeaning trProj world uvars Delta source answer)
    (htrue : answer = true) :
    world.venv.HasType uvars Delta.toCtx sourceV (.sort .zero) := by
  obtain ⟨cachedV, hcached, htype⟩ := h htrue
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have heq := hcached.uniq world.venvWF theory.literalWF
    theory.projections hctx hsource
  exact htype.defeqU_l world.venvWF hDelta heq

end IsPropMeaning

/-! ## Semantic relation represented by the equivalence manager -/

/-- One directed, semantically justified union-find edge.  Besides the
context/radius agreement, both endpoint keys retain concrete finite-support
witnesses.  That witness retention is what makes a chain of manager edges
semantically composable: the intermediate address is never interpreted as an
expression merely because a hash happens to exist. -/
structure DefEqKeyEdge (keys : WhnfContextKeys) (trProj : RawProjRel)
    (authority : CacheAuthority) (support : RunSupport)
    (left right : EqKey) : Prop where
  context_eq : left.ctxAddr = right.ctxAddr
  radius_eq : left.lbr = right.lbr
  leftWitness : ∃ a, support a ∧ a.addr = left.exprAddr ∧
    a.lbr = left.exprLbr
  rightWitness : ∃ b, support b ∧ b.addr = right.exprAddr ∧
    b.lbr = right.exprLbr
  meaning : ∀ a, support a → a.addr = left.exprAddr →
    ∀ b, support b → b.addr = right.exprAddr →
      ∀ Delta, keys.Represents left.lbr left.ctxAddr Delta →
        DefEqMeaning trProj authority.world keys.uvars Delta a b true

namespace DefEqKeyEdge

/-- Edge validity is monotone in the trusted Theory world. -/
theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {before after : CacheAuthority} {support : RunSupport}
    {left right : EqKey} (hle : before ≤ after)
    (h : DefEqKeyEdge keys trProj before support left right) :
    DefEqKeyEdge keys trProj after support left right where
  context_eq := h.context_eq
  radius_eq := h.radius_eq
  leftWitness := h.leftWitness
  rightWitness := h.rightWitness
  meaning a ha haddrA b hb haddrB Delta hrepresented :=
    (h.meaning a ha haddrA b hb haddrB Delta hrepresented).mono hle.world

end DefEqKeyEdge

/-- One undirected semantic step.  Union-find parent edges may choose either
orientation, so symmetry belongs at this structural layer rather than being
silently assumed of a raw insertion certificate. -/
inductive DefEqKeyStep (keys : WhnfContextKeys) (trProj : RawProjRel)
    (authority : CacheAuthority) (support : RunSupport) :
    EqKey → EqKey → Prop where
  | forward : DefEqKeyEdge keys trProj authority support left right →
      DefEqKeyStep keys trProj authority support left right
  | backward : DefEqKeyEdge keys trProj authority support right left →
      DefEqKeyStep keys trProj authority support left right

namespace DefEqKeyStep

theorem symm {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyStep keys trProj authority support left right) :
    DefEqKeyStep keys trProj authority support right left := by
  cases h with
  | forward hedge => exact .backward hedge
  | backward hedge => exact .forward hedge

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {before after : CacheAuthority} {support : RunSupport}
    {left right : EqKey} (hle : before ≤ after)
    (h : DefEqKeyStep keys trProj before support left right) :
    DefEqKeyStep keys trProj after support left right := by
  cases h with
  | forward hedge => exact .forward (hedge.mono hle)
  | backward hedge => exact .backward (hedge.mono hle)

theorem context_eq {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyStep keys trProj authority support left right) :
    left.ctxAddr = right.ctxAddr := by
  cases h with
  | forward hedge => exact hedge.context_eq
  | backward hedge => exact hedge.context_eq.symm

theorem radius_eq {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyStep keys trProj authority support left right) :
    left.lbr = right.lbr := by
  cases h with
  | forward hedge => exact hedge.radius_eq
  | backward hedge => exact hedge.radius_eq.symm

/-- Every step provides a supported expression for its target key. -/
theorem targetWitness {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyStep keys trProj authority support left right) :
    ∃ b, support b ∧ b.addr = right.exprAddr ∧ b.lbr = right.exprLbr := by
  cases h with
  | forward hedge => exact hedge.rightWitness
  | backward hedge => exact hedge.leftWitness

/-- Interpret one undirected step at a represented source context. -/
theorem meaning {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyStep keys trProj authority support left right)
    {a b : KExpr .anon} (ha : support a) (haddrA : a.addr = left.exprAddr)
    (hb : support b) (haddrB : b.addr = right.exprAddr)
    {Delta : KVLCtx} (hrepresented :
      keys.Represents left.lbr left.ctxAddr Delta) :
    DefEqMeaning trProj authority.world keys.uvars Delta a b true := by
  cases h with
  | forward hedge =>
      exact hedge.meaning a ha haddrA b hb haddrB Delta hrepresented
  | backward hedge =>
      have hrepresented' :
          keys.Represents right.lbr right.ctxAddr Delta := by
        simpa only [hedge.radius_eq, hedge.context_eq] using hrepresented
      exact (hedge.meaning b hb haddrB a ha haddrA Delta hrepresented').symm

end DefEqKeyStep

/-- A finite path of justified manager edges.  Its constructors make
reflexivity and transitivity structural; no unproved transitivity of context
digests or expression addresses enters the relation. -/
inductive DefEqKeyEquiv (keys : WhnfContextKeys) (trProj : RawProjRel)
    (authority : CacheAuthority) (support : RunSupport) :
    EqKey → EqKey → Prop where
  | refl (key : EqKey) : DefEqKeyEquiv keys trProj authority support key key
  | cons : DefEqKeyStep keys trProj authority support left middle →
      DefEqKeyEquiv keys trProj authority support middle right →
      DefEqKeyEquiv keys trProj authority support left right

namespace DefEqKeyEquiv

theorem trans {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left middle right : EqKey}
    (h₁ : DefEqKeyEquiv keys trProj authority support left middle)
    (h₂ : DefEqKeyEquiv keys trProj authority support middle right) :
    DefEqKeyEquiv keys trProj authority support left right := by
  induction h₁ with
  | refl => exact h₂
  | cons hstep htail ih => exact .cons hstep (ih h₂)

theorem symm {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyEquiv keys trProj authority support left right) :
    DefEqKeyEquiv keys trProj authority support right left := by
  induction h with
  | refl => exact .refl _
  | @cons left middle right hstep htail ih =>
      exact trans ih (.cons hstep.symm (.refl _))

theorem equivalence (keys : WhnfContextKeys) (trProj : RawProjRel)
    (authority : CacheAuthority) (support : RunSupport) :
    Equivalence (DefEqKeyEquiv keys trProj authority support) :=
  ⟨.refl, symm, trans⟩

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {before after : CacheAuthority} {support : RunSupport}
    {left right : EqKey} (hle : before ≤ after)
    (h : DefEqKeyEquiv keys trProj before support left right) :
    DefEqKeyEquiv keys trProj after support left right := by
  induction h with
  | refl => exact .refl _
  | cons hstep htail ih => exact .cons (hstep.mono hle) ih

theorem context_eq {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyEquiv keys trProj authority support left right) :
    left.ctxAddr = right.ctxAddr := by
  induction h with
  | refl => rfl
  | cons hstep htail ih => exact hstep.context_eq.trans ih

theorem radius_eq {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyEquiv keys trProj authority support left right) :
    left.lbr = right.lbr := by
  induction h with
  | refl => rfl
  | cons hstep htail ih => exact hstep.radius_eq.trans ih

/-- A manager path exposes a concrete supported witness for its target once
the queried source key has one.  The intrinsic-radius equality is retained so
root-derived cache probes can reconstruct the exact context radius used by
their expression pair. -/
theorem targetWitness {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport} {left right : EqKey}
    (h : DefEqKeyEquiv keys trProj authority support left right)
    {a : KExpr .anon} (ha : support a) (haddr : a.addr = left.exprAddr)
    (hlbr : a.lbr = left.exprLbr) :
    ∃ b, support b ∧ b.addr = right.exprAddr ∧ b.lbr = right.exprLbr := by
  induction h generalizing a with
  | refl => exact ⟨a, ha, haddr, hlbr⟩
  | cons hstep htail ih =>
      obtain ⟨middle, hmiddle, hmiddleAddr, hmiddleLbr⟩ :=
        hstep.targetWitness
      exact ih hmiddle hmiddleAddr hmiddleLbr

/-- A manager path is sound for concrete translated endpoints.  Intermediate
expressions and translations come from the edge certificates themselves;
they are never reconstructed from hashes. -/
theorem sound {keys : WhnfContextKeys} {trProj : RawProjRel}
    {authority : CacheAuthority} {support : RunSupport}
    (theory : WhnfTheory trProj authority.world keys.uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF authority.world.venv keys.uvars Delta)
    (hcollision : support.CollisionFree)
    {left right : EqKey}
    (h : DefEqKeyEquiv keys trProj authority support left right)
    {a b : KExpr .anon} {va vb : VExpr}
    (haSupport : support a) (haddrA : a.addr = left.exprAddr)
    (hbSupport : support b) (haddrB : b.addr = right.exprAddr)
    (hrepresented : keys.Represents left.lbr left.ctxAddr Delta)
    (ha : TrKExprS authority.world.venv keys.uvars authority.world.nameOf
      trProj Delta a va)
    (hb : TrKExprS authority.world.venv keys.uvars authority.world.nameOf
      trProj Delta b vb) :
    authority.world.venv.IsDefEqU keys.uvars Delta.toCtx va vb := by
  induction h generalizing a va with
  | refl =>
      have habAddr : a.addr = b.addr := haddrA.trans haddrB.symm
      have hab : a = b := by
        have herase := hcollision.expr haSupport hbSupport habAddr
        simpa only [KExpr.eraseMeta_anon] using herase
      subst b
      exact ha.uniq authority.world.venvWF theory.literalWF
        theory.projections (KVLCtx.IsDefEq.refl authority.world.venvWF hDelta) hb
  | @cons left middle right hstep htail ih =>
      obtain ⟨mid, hmidSupport, hmidAddr, _hmidLbr⟩ := hstep.targetWitness
      have hstepMeaning := hstep.meaning haSupport haddrA hmidSupport hmidAddr
        hrepresented
      obtain ⟨stepA, midV, hstepA, hmid, hstepEq⟩ := hstepMeaning rfl
      have hleftMid : authority.world.venv.IsDefEqU keys.uvars Delta.toCtx
          va midV :=
        DefEqMeaning.of_translations theory hDelta ha hmid hstepMeaning rfl
      have hrepresentedTail :
          keys.Represents middle.lbr middle.ctxAddr Delta := by
        simpa only [hstep.radius_eq, hstep.context_eq] using hrepresented
      have hmidRight := ih hmidSupport hmidAddr haddrB
        hrepresentedTail hmid
      exact hleftMid.trans authority.world.venvWF hDelta hmidRight

end DefEqKeyEquiv

/-! ## Joint suffix semantics

The production context key is itself a Blake3 digest.  Expression-address
collision freedom does not imply injectivity of this second, composite hash.
Consequently the four semantic transports below remain an explicit boundary:
they may later be proved from a finite context-digest collision hypothesis and
the declarative suffix-closure theorem, but must not be inferred from a bare
address equality. -/

/-- One context-key interpretation sufficient for every K1/K2 semantic cache
family.  Operational representation is shared, while WHNF, inference, DefEq,
and the auxiliary proposition classifier each state their own
context-transport consequence. -/
structure KernelSuffixModel (trProj : RawProjRel) (world : VerifyWorld) where
  keys : WhnfContextKeys
  representsCtx : ∀ {before after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address} {Delta : KVLCtx},
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    keys.Represents lbr ctxAddr Delta
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
  isPropTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source : KExpr .anon} {answer : Bool},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    IsPropMeaning trProj world keys.uvars Delta source answer →
    IsPropMeaning trProj world keys.uvars Delta' source answer

namespace TcM

/-- A joint suffix model interprets a direct context-address execution at an
arbitrary expression's local-binding radius. -/
theorem ctxAddrForLbr_model_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {source : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support model.keys.uvars
        Delta) s
      (TcM.ctxAddrForLbr source.lbr)
      (fun ctxAddr s' =>
        model.keys.Represents source.lbr ctxAddr Delta ∧
          ContextKeyFrame s s') := by
  intro hI
  have hwf :=
    (TcM.ctxAddrForLbr_wf
      (fun hInv hframe => hframe.whnfStateInv hInv) source.lbr s) hI
  match hrun : TcM.ctxAddrForLbr source.lbr s with
  | .ok ctxAddr s' =>
      rw [hrun] at hwf
      exact ⟨hwf.1, model.representsCtx hI.2.1 hrun, hwf.2⟩
  | .error err s' =>
      rw [hrun] at hwf
      exact hwf

/-- A joint suffix model supplies the same direct representation theorem for
DefEq's bare context-key execution that it supplies for WHNF/inference keys.
Keeping this field explicit prevents a model of expression-key runs from
being silently assumed to cover `ctxAddrForLbr` in isolation. -/
theorem defEqCtxKey_model_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support model.keys.uvars
        Delta) s
      (TcM.defEqCtxKey a b)
      (fun ctxAddr s' =>
        DefEqContextKeys.Matches model.keys trProj world s Delta a b
          ctxAddr /\ ContextKeyFrame s s') := by
  intro hI
  have hwf :=
    (TcM.defEqCtxKey_wf
      (layer := layer) (semantics := semantics)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) (a := a) (b := b)
      (s := s)) hI
  match hrun : TcM.defEqCtxKey a b s with
  | .ok ctxAddr s' =>
      rw [hrun] at hwf
      have hctxRun : TcM.ctxAddrForLbr (max a.lbr b.lbr) s =
          .ok ctxAddr s' := by
        simpa [TcM.defEqCtxKey] using hrun
      exact ⟨hwf.1,
        ⟨⟨hI.2.1, model.representsCtx hI.2.1 hctxRun, ⟨s', hrun⟩⟩,
          hwf.2⟩⟩
  | .error err s' =>
      rw [hrun] at hwf
      exact hwf

end TcM

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
  isProp : ∀ {Delta Delta' : KVLCtx} {source : KExpr .anon}
      {answer : Bool},
    spec.inputOf source.lbr Delta = spec.inputOf source.lbr Delta' →
    IsPropMeaning trProj world uvars Delta source answer →
    IsPropMeaning trProj world uvars Delta' source answer

/-- Joint suffix model whose representation theorem is restricted to states
in one explicit domain.  This is the correct shape for a finite execution
scope: unlike `KernelSuffixModel`, it does not quantify key construction over
every context-reconciled state in existence. -/
structure ScopedKernelSuffixModel (trProj : RawProjRel)
    (world : VerifyWorld) where
  keys : WhnfContextKeys
  StateInScope : TcState .anon → Prop
  /-- A real suffix-key execution keeps the next checker state inside the
  same finite run domain.  This field is needed independently of semantic
  representation: subsequent key operations run from the memo-updated
  state, including after partial computations. -/
  preservesCtx : ∀ {before after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address},
    StateInScope before →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    StateInScope after
  /-- Ordinary cache, intern, and bookkeeping updates preserve scope when
  they fix the complete digest-relevant state projection. -/
  preservesFrame : ∀ {before after : TcState .anon},
    StateInScope before → ContextDigestFrame before after →
    StateInScope after
  representsCtx : ∀ {before after : TcState .anon} {lbr : UInt64}
      {ctxAddr : Address} {Delta : KVLCtx},
    StateInScope before →
    CtxRecon world.venv keys.uvars world.nameOf trProj before Delta →
    TcM.ctxAddrForLbr lbr before = .ok ctxAddr after →
    keys.Represents lbr ctxAddr Delta
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
  isPropTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source : KExpr .anon} {answer : Bool},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    IsPropMeaning trProj world keys.uvars Delta source answer →
    IsPropMeaning trProj world keys.uvars Delta' source answer

/-- The state-independent semantic half shared by the legacy global model
and the run-scoped model.  Cache provenance needs only these transports;
key construction is kept in the separate global/scoped operational fields so
it cannot accidentally erase the run domain. -/
structure KernelSuffixTransports (trProj : RawProjRel)
    (world : VerifyWorld) where
  keys : WhnfContextKeys
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
  isPropTransport : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source : KExpr .anon} {answer : Bool},
    keys.Represents source.lbr ctxAddr Delta →
    keys.Represents source.lbr ctxAddr Delta' →
    IsPropMeaning trProj world keys.uvars Delta source answer →
    IsPropMeaning trProj world keys.uvars Delta' source answer

namespace KernelSuffixModel

def transports {trProj : RawProjRel} {world : VerifyWorld}
    (model : KernelSuffixModel trProj world) :
    KernelSuffixTransports trProj world where
  keys := model.keys
  whnfTransport := model.whnfTransport
  inferTransport := model.inferTransport
  defEqTransport := model.defEqTransport
  isPropTransport := model.isPropTransport

end KernelSuffixModel

namespace ScopedKernelSuffixModel

/-- A production reset returns to the finite suffix model's state domain.
This is an operational obligation because an arbitrary scoped model may
choose any predicate for `StateInScope`. -/
def ResetPreservesScope
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world) : Prop :=
  ∀ {before after : TcState .anon},
    model.StateInScope before →
    TcM.reset before = .ok () after →
    model.StateInScope after

def transports {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world) :
    KernelSuffixTransports trProj world where
  keys := model.keys
  whnfTransport := model.whnfTransport
  inferTransport := model.inferTransport
  defEqTransport := model.defEqTransport
  isPropTransport := model.isPropTransport

end ScopedKernelSuffixModel

/-- The ordinary checker invariant refined by membership in one explicit
suffix-model state domain.  K2S uses this predicate at every model-dependent
key boundary; the unscoped invariant remains available for model-independent
helpers and legacy compatibility theorems. -/
def ScopedWhnfStateInv {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics) (support : RunSupport)
    (Delta : KVLCtx) (s : TcState .anon) : Prop :=
  WhnfStateInv layer semantics trProj world support model.keys.uvars Delta s ∧
    model.StateInScope s

namespace ScopedWhnfStateInv

theorem base
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics} {support : RunSupport}
    {Delta : KVLCtx} {s : TcState .anon}
    (h : ScopedWhnfStateInv model layer semantics support Delta s) :
    WhnfStateInv layer semantics trProj world support model.keys.uvars Delta
      s :=
  h.1

theorem inScope
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics} {support : RunSupport}
    {Delta : KVLCtx} {s : TcState .anon}
    (h : ScopedWhnfStateInv model layer semantics support Delta s) :
    model.StateInScope s :=
  h.2

end ScopedWhnfStateInv

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
  preservesCtx hscope hrun :=
    ⟨spec.preserves hscope.1 hrun,
      ContextDigestScope.Captures.contextKeyFrame hscope.2
        (TcM.ctxAddrForLbr_frame hrun)⟩
  preservesFrame hscope hframe :=
    ⟨spec.framePreserves hscope.1 hframe,
      ContextDigestScope.Captures.contextDigestFrame hscope.2 hframe⟩
  representsCtx hscope hctx hrun :=
    scopedOperationalWhnfContextKeys.representsCtx hscope.1 hscope.2 hctx hrun
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
  isPropTransport hDelta hDelta' hmeaning := by
    apply hsemantics.isProp _ hmeaning
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
  representsCtx hctx hrun := model.representsCtx (hcomplete _) hctx hrun
  represents hctx hrun := model.represents (hcomplete _) hctx hrun
  whnfTransport := model.whnfTransport
  inferTransport := model.inferTransport
  defEqTransport := model.defEqTransport
  isPropTransport := model.isPropTransport

end ScopedKernelSuffixModel

namespace TcM

/-- A scoped suffix model interprets and preserves one direct context-key
execution from a state already admitted by the finite run domain. -/
theorem ctxAddrForLbr_scoped_model_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : ScopedKernelSuffixModel trProj world)
    {Delta : KVLCtx} {source : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.ctxAddrForLbr source.lbr)
      (fun ctxAddr s' =>
        model.keys.Represents source.lbr ctxAddr Delta ∧
          ContextKeyFrame s s') := by
  intro hI
  have hwf :=
    (TcM.ctxAddrForLbr_wf
      (fun hInv hframe => hframe.whnfStateInv hInv) source.lbr s) hI.1
  match hrun : TcM.ctxAddrForLbr source.lbr s with
  | .ok ctxAddr s' =>
      rw [hrun] at hwf
      exact ⟨⟨hwf.1, model.preservesCtx hI.2 hrun⟩,
        model.representsCtx hI.2 hI.1.2.1 hrun, hwf.2⟩
  | .error err s' =>
      obtain ⟨ctxAddr, after, htotal⟩ :=
        TcM.ctxAddrForLbr_total source.lbr s
      rw [htotal] at hrun
      contradiction

/-- Scoped operational matching for the WHNF-shaped key shared by WHNF and
inference. -/
theorem whnfKey_scoped_model_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : ScopedKernelSuffixModel trProj world)
    {Delta : KVLCtx} {source : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.whnfKey source)
      (fun key s' =>
        model.keys.Matches trProj world s Delta source key ∧
          ContextKeyFrame s s') := by
  intro hI
  have hwf := TcM.whnfKey_wf
    (layer := layer) (semantics := semantics) (trProj := trProj)
    (world := world) (support := support) (uvars := model.keys.uvars)
    (Δ := Delta) (source := source) (s := s) hI.1
  match hrun : TcM.whnfKey source s with
  | .ok key s' =>
      rw [hrun] at hwf
      have hctxRun := TcM.whnfKey_ctx hrun
      exact ⟨⟨hwf.1, model.preservesCtx hI.2 hctxRun⟩,
        ⟨⟨hI.1.2.1, model.represents hI.2 hI.1.2.1 hrun, ⟨s', hrun⟩⟩,
          hwf.2.2⟩⟩
  | .error err s' =>
      obtain ⟨ctxAddr, after, htotal⟩ :=
        TcM.ctxAddrForLbr_total source.lbr s
      have hkeyTotal : TcM.whnfKey source s =
          .ok (source.addr, ctxAddr) after := by
        unfold TcM.whnfKey
        change EStateM.bind (TcM.ctxAddrForLbr source.lbr)
          (fun addr => pure (source.addr, addr)) s = _
        unfold EStateM.bind
        rw [htotal]
        rfl
      rw [hkeyTotal] at hrun
      contradiction

/-- Scoped operational matching for DefEq's bare context key. -/
theorem defEqCtxKey_scoped_model_matches_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : ScopedKernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (ScopedWhnfStateInv model layer semantics support Delta) s
      (TcM.defEqCtxKey a b)
      (fun ctxAddr s' =>
        DefEqContextKeys.Matches model.keys trProj world s Delta a b
          ctxAddr ∧ ContextKeyFrame s s') := by
  intro hI
  have hwf := TcM.defEqCtxKey_wf
    (layer := layer) (semantics := semantics) (trProj := trProj)
    (world := world) (support := support) (uvars := model.keys.uvars)
    (Delta := Delta) (a := a) (b := b) (s := s) hI.1
  match hrun : TcM.defEqCtxKey a b s with
  | .ok ctxAddr s' =>
      rw [hrun] at hwf
      have hctxRun : TcM.ctxAddrForLbr (max a.lbr b.lbr) s =
          .ok ctxAddr s' := by
        simpa [TcM.defEqCtxKey] using hrun
      exact ⟨⟨hwf.1, model.preservesCtx hI.2 hctxRun⟩,
        ⟨⟨hI.1.2.1, model.representsCtx hI.2 hI.1.2.1 hctxRun,
          ⟨s', hrun⟩⟩, hwf.2⟩⟩
  | .error err s' =>
      obtain ⟨ctxAddr, after, htotal⟩ :=
        TcM.ctxAddrForLbr_total (max a.lbr b.lbr) s
      have hkeyTotal : TcM.defEqCtxKey a b s = .ok ctxAddr after := by
        simpa [TcM.defEqCtxKey] using htotal
      rw [hkeyTotal] at hrun
      contradiction

end TcM

namespace KernelSuffixModel

/-- Forget the K2 transports and recover exactly the K1 suffix model. -/
def toWhnfSuffixModel {trProj : RawProjRel} {world : VerifyWorld}
    (model : KernelSuffixModel trProj world) :
    WhnfSuffixModel trProj world where
  keys := model.keys
  represents := model.represents
  transport := model.whnfTransport

/-- Build the joint model over the canonical operational representation.
Only the four semantic same-digest transports remain as assumptions; actual
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
      DefEqMeaning trProj world uvars Delta' a b answer)
    (hisProp : ∀ {ctxAddr : Address} {Delta Delta' : KVLCtx}
      {source : KExpr .anon} {answer : Bool},
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta →
      (operationalWhnfContextKeys trProj world uvars).Represents
        source.lbr ctxAddr Delta' →
      IsPropMeaning trProj world uvars Delta source answer →
      IsPropMeaning trProj world uvars Delta' source answer) :
    KernelSuffixModel trProj world where
  keys := operationalWhnfContextKeys trProj world uvars
  representsCtx hctx hrun :=
    operationalWhnfContextKeys.representsCtx hctx hrun
  represents hctx hrun :=
    operationalWhnfContextKeys.represents hctx hrun
  whnfTransport hDelta hDelta' hmeaning :=
    hwhnf hDelta hDelta' hmeaning
  inferTransport hDelta hDelta' hmeaning :=
    hinfer hDelta hDelta' hmeaning
  defEqTransport hDelta hDelta' hmeaning :=
    hdefeq hDelta hDelta' hmeaning
  isPropTransport hDelta hDelta' hmeaning :=
    hisProp hDelta hDelta' hmeaning

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
* `ContextSuffixSemantics` transports the four declarative meanings across
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

/-- Exact validity of the memoized proposition classifier.  A key is
interpreted only through a finite-support expression witness and a represented
suffix context; the fallback owns every other cache family. -/
def IsPropCacheValid (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) : CacheEntry → Prop
  | .isProp key answer =>
      ∀ source, support source → source.addr = key.1 →
        ∀ Delta, keys.Represents source.lbr key.2 Delta →
          IsPropMeaning trProj authority.world keys.uvars Delta source answer
  | entry => fallback.Valid authority support entry

namespace IsPropCacheValid

theorem mono {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {before after : CacheAuthority}
    {support : RunSupport} {entry : CacheEntry} (hle : before ≤ after)
    (h : IsPropCacheValid keys trProj fallback before support entry) :
    IsPropCacheValid keys trProj fallback after support entry := by
  cases entry with
  | isProp key answer =>
      intro source hsource haddr Delta hrepresented
      exact (h source hsource haddr Delta hrepresented).mono hle.world
  | expr | defEq | defEqFailure | unfold | natSuccStuck | isRec |
      recursor | recMajors | blockPeer | blockResult =>
      exact fallback.mono hle h

theorem result {keys : WhnfContextKeys} {trProj : RawProjRel}
    {fallback : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {key : Address × Address} {answer : Bool}
    {source : KExpr .anon}
    (h : IsPropCacheValid keys trProj fallback authority support
      (.isProp key answer))
    (hsource : support source) (haddr : source.addr = key.1)
    {Delta : KVLCtx}
    (hrepresented : keys.Represents source.lbr key.2 Delta) :
    IsPropMeaning trProj authority.world keys.uvars Delta source answer :=
  h source hsource haddr Delta hrepresented

end IsPropCacheValid

/-- Overlay the proposition-classifier meaning on an arbitrary fallback
cache semantics. -/
def isPropCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel)
    (fallback : CacheSemantics) : CacheSemantics where
  Valid := IsPropCacheValid keys trProj fallback
  mono := IsPropCacheValid.mono
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
  Equiv := DefEqKeyEquiv keys trProj
  equivEquivalence := DefEqKeyEquiv.equivalence keys trProj
  equivMono := DefEqKeyEquiv.mono
  blockError := by
    intro authority support block err
    exact fallback.blockError authority support block err
  blockSuccess := by
    intro authority support block h
    exact fallback.blockSuccess authority support block h
  blockSuccessSound := by
    intro authority support block h
    exact fallback.blockSuccessSound authority support block h

/-- Canonical K1+K2 semantic stack.  K1's WHNF and fixed-universe unfold
layers stay outermost; inference and def-eq occupy precisely the fallback
families they own. -/
def kernelCacheSemantics (keys : WhnfContextKeys) (trProj : RawProjRel) :
    CacheSemantics :=
  k1CacheSemantics keys trProj <|
    inferCacheSemantics keys trProj <|
      defEqCacheSemantics keys trProj <|
        isPropCacheSemantics keys trProj <|
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

/-- Read one proposition-classifier entry from the canonical cache stack. -/
theorem kernelIsPropMeaning {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {key : Address × Address} {answer : Bool}
    {source : KExpr .anon}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.isProp key answer))
    (hsource : support source) (haddr : source.addr = key.1)
    {Delta : KVLCtx}
    (hrepresented : keys.Represents source.lbr key.2 Delta) :
    IsPropMeaning trProj authority.world keys.uvars Delta source answer :=
  IsPropCacheValid.result
    (fallback := isRecCacheSemantics CacheSemantics.blockErrorsOnly)
    h.valid hsource haddr hrepresented

/-- Full and cheap DefEq partitions have identical semantic validity; only
their lookup policy differs.  A certified entry can therefore be copied
between partitions without re-proving its witnesses, references, or result. -/
theorem kernelDefEqRekind {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {source target : DefEqCacheKind}
    {key : Address × Address × Address} {answer : Bool}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.defEq source key answer)) :
    CacheProvenance (kernelCacheSemantics keys trProj)
      authority support (.defEq target key answer) := by
  refine ⟨h.supported, h.references, ?_⟩
  simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
    WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
    inferCacheSemantics, InferCacheValid, defEqCacheSemantics,
    DefEqCacheValid] using h.valid

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
      simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
        WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid] using
        h.valid
  | inferOnly =>
      apply InferCacheValid.expr
        (fallback := defEqCacheSemantics keys trProj
          CacheSemantics.blockErrorsOnly) .inferOnly (hsource := hsource)
        (haddr := hmatch.sourceAddr) (hctx := hmatch.2.1)
      simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
        WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid] using
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
  simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
    WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
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

/-- A positive canonical cache entry is also a justified manager edge in the
caller's original operand order.  Collision freedom is used only to recover
the concrete supported expressions quantified by the edge contract. -/
theorem kernelDefEqEdgeCanonical {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {ctxAddr : Address} {a b : KExpr .anon}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support
      (.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true))
    (hcollision : support.CollisionFree)
    (ha : support a) (hb : support b) :
    DefEqKeyEdge keys trProj authority support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ where
  context_eq := rfl
  radius_eq := rfl
  leftWitness := ⟨a, ha, rfl, rfl⟩
  rightWitness := ⟨b, hb, rfl, rfl⟩
  meaning otherA hotherA haddrA otherB hotherB haddrB Delta hrepresented := by
    have heqA : a = otherA := by
      have herase := hcollision.expr ha hotherA haddrA.symm
      simpa only [KExpr.eraseMeta_anon] using herase
    have heqB : b = otherB := by
      have herase := hcollision.expr hb hotherB haddrB.symm
      simpa only [KExpr.eraseMeta_anon] using herase
    subst otherA
    subst otherB
    exact h.kernelDefEqMeaningCanonical ha hb hrepresented

/-- Package a positive canonical cache entry as the equivalence relation
consumed by `EquivManager.WF.addEquiv`. -/
theorem kernelDefEqEquivCanonical {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {ctxAddr : Address} {a b : KExpr .anon}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support
      (.defEq kind
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true))
    (hcollision : support.CollisionFree)
    (ha : support a) (hb : support b) :
    DefEqKeyEquiv keys trProj authority support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
  .cons (.forward (h.kernelDefEqEdgeCanonical hcollision ha hb)) (.refl _)

/-- Interpret a positive root-derived cache hit without treating a root
address as an expression.  Each manager path supplies a supported endpoint
witness; the runtime scope guard proves that those endpoints reconstruct the
same represented suffix radius as the caller.  The result is the composition
`a ≃ root(a) ≃ root(b) ≃ b`. -/
theorem kernelDefEqRootAcceptance {keys : WhnfContextKeys}
    {trProj : RawProjRel} {authority : CacheAuthority}
    {support : RunSupport} {kind : DefEqCacheKind}
    {ctxAddr : Address} {lbr : UInt64}
    {a b : KExpr .anon} {aRoot bRoot : EqKey}
    {Delta : KVLCtx} {va vb : VExpr}
    (h : CacheProvenance (kernelCacheSemantics keys trProj)
      authority support
      (.defEq kind
        ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
          (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr) true))
    (theory : WhnfTheory trProj authority.world keys.uvars)
    (hDelta : KVLCtx.WF authority.world.venv keys.uvars Delta)
    (hcollision : support.CollisionFree)
    (haPath : DefEqKeyEquiv keys trProj authority support
      ⟨a.addr, ctxAddr, lbr, a.lbr⟩ aRoot)
    (hbPath : DefEqKeyEquiv keys trProj authority support
      ⟨b.addr, ctxAddr, lbr, b.lbr⟩ bRoot)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr lbr = true)
    (hrepresented : keys.Represents lbr ctxAddr Delta)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS authority.world.venv keys.uvars authority.world.nameOf
      trProj Delta a va)
    (hb : TrKExprS authority.world.venv keys.uvars authority.world.nameOf
      trProj Delta b vb) :
    authority.world.venv.IsDefEqU keys.uvars Delta.toCtx va vb := by
  obtain ⟨rootA, hrootASupport, hrootAAddr, hrootALbr⟩ :=
    haPath.targetWitness haSupport rfl rfl
  obtain ⟨rootB, hrootBSupport, hrootBAddr, hrootBLbr⟩ :=
    hbPath.targetWitness hbSupport rfl rfl
  have hscopeFields :=
    (EqKey.rootCacheScopeMatches_iff aRoot bRoot ctxAddr lbr).mp hscope
  have hrootRepresented :
      keys.Represents (max rootA.lbr rootB.lbr) ctxAddr Delta := by
    rw [hrootALbr, hrootBLbr, hscopeFields.2.2.2.2]
    exact hrepresented
  have hrootCache :
      CacheProvenance (kernelCacheSemantics keys trProj) authority support
        (.defEq kind
          ((canonicalPair rootA.addr rootB.addr).1,
            (canonicalPair rootA.addr rootB.addr).2, ctxAddr) true) := by
    simpa only [hrootAAddr, hrootBAddr] using h
  have hrootMeaning :
      DefEqMeaning trProj authority.world keys.uvars Delta rootA rootB true :=
    hrootCache.kernelDefEqMeaningCanonical
      hrootASupport hrootBSupport hrootRepresented
  obtain ⟨rootVA, rootVB, hrootATr, hrootBTr, hrootEq⟩ := hrootMeaning rfl
  have haRootEq : authority.world.venv.IsDefEqU keys.uvars Delta.toCtx
      va rootVA :=
    haPath.sound theory hDelta hcollision
      haSupport rfl hrootASupport hrootAAddr hrepresented ha hrootATr
  have hbRootEq : authority.world.venv.IsDefEqU keys.uvars Delta.toCtx
      vb rootVB :=
    hbPath.sound theory hDelta hcollision
      hbSupport rfl hrootBSupport hrootBAddr hrepresented hb hrootBTr
  exact (haRootEq.trans authority.world.venvWF hDelta hrootEq).trans
    authority.world.venvWF hDelta hbRootEq.symm

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

namespace KernelSuffixTransports

/-- Turn one executed proposition-classifier result into collision-robust
provenance for the memo table. -/
theorem isPropProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixTransports trProj world)
    (hcollision : support.CollisionFree)
    {Delta : KVLCtx} {source : KExpr .anon} {answer : Bool}
    {ctxAddr : Address}
    (hsource : support source)
    (hctx : model.keys.Represents source.lbr ctxAddr Delta)
    (hmeaning : IsPropMeaning trProj world model.keys.uvars Delta source
      answer)
    (hreferences :
      (CacheEntry.isProp (source.addr, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.isProp (source.addr, ctxAddr) answer) := by
  refine ⟨⟨source, hsource, rfl⟩, hreferences, ?_⟩
  have hvalid : IsPropCacheValid model.keys trProj
      (isRecCacheSemantics CacheSemantics.blockErrorsOnly)
      (CacheAuthority.stable world) support
      (.isProp (source.addr, ctxAddr) answer) := by
    intro other hother haddr Delta' hrepresented
    have heq : source = other := by
      have herase := hcollision.expr hsource hother haddr.symm
      simpa only [KExpr.eraseMeta_anon] using herase
    subst other
    exact model.isPropTransport hctx hrepresented hmeaning
  simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
    WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
    inferCacheSemantics, InferCacheValid, defEqCacheSemantics,
    DefEqCacheValid, isPropCacheSemantics] using hvalid

/-- Turn one executed inference result into collision-robust provenance for
either inference cache.  Validity quantifies over every supported expression
sharing the source address and every context sharing the suffix digest. -/
theorem inferProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixTransports trProj world)
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
      simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
        WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid] using
        hvalid
  | inferOnly =>
      have hvalid : InferCacheValid model.keys trProj
          (defEqCacheSemantics model.keys trProj
            CacheSemantics.blockErrorsOnly)
          (CacheAuthority.stable world) support
          (.expr .inferOnly key ty) := hall
      simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
        WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid] using
        hvalid

/-- Turn one executed DefEq result into collision-robust provenance for the
canonicalized production key.  The swapped canonical-pair branch transports
the semantic result through symmetry explicitly. -/
theorem defEqProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixTransports trProj world)
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
    simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
      WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
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
    simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
      WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid

/-- A narrow same-head failure marker is rejection-only, so it needs no
semantic transport.  It still records finite source witnesses and explicit
reference authorization for the canonical operand pair. -/
theorem defEqFailureProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixTransports trProj world)
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
    simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
      WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid
  · have hpair : canonicalPair a.addr b.addr = (b.addr, a.addr) := by
      simp [canonicalPair, horder]
    rw [hpair] at hreferences ⊢
    refine ⟨⟨⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩⟩, hreferences, ?_⟩
    have hvalid : DefEqCacheValid model.keys trProj
        CacheSemantics.blockErrorsOnly (CacheAuthority.stable world) support
        (.defEqFailure (b.addr, a.addr, ctxAddr)) := trivial
    simpa [kernelCacheSemantics, k1CacheSemantics, whnfCacheSemantics,
      WhnfCacheValid, unfoldCacheSemantics, UnfoldCacheValid,
      inferCacheSemantics, InferCacheValid] using hvalid

end KernelSuffixTransports

namespace KernelSuffixModel

/-- Legacy global-model spelling retained as a compatibility wrapper around
the state-independent transport proof. -/
theorem isPropProvenance {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} (model : KernelSuffixModel trProj world)
    (hcollision : support.CollisionFree)
    {Delta : KVLCtx} {source : KExpr .anon} {answer : Bool}
    {ctxAddr : Address}
    (hsource : support source)
    (hctx : model.keys.Represents source.lbr ctxAddr Delta)
    (hmeaning : IsPropMeaning trProj world model.keys.uvars Delta source
      answer)
    (hreferences :
      (CacheEntry.isProp (source.addr, ctxAddr) answer).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    CacheProvenance (kernelCacheSemantics model.keys trProj)
      (CacheAuthority.stable world) support
      (.isProp (source.addr, ctxAddr) answer) :=
  model.transports.isPropProvenance hcollision hsource hctx hmeaning
    hreferences

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
      (CacheAuthority.stable world) support (.expr kind key ty) :=
  model.transports.inferProvenance hcollision hkind hsource hty hmatch
    hmeaning hreferences

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
          (canonicalPair a.addr b.addr).2, ctxAddr) answer) :=
  model.transports.defEqProvenance hcollision kind ha hb hctx hmeaning
    hreferences

theorem defEqFailureProvenance
    {trProj : RawProjRel} {world : VerifyWorld}
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
          (canonicalPair a.addr b.addr).2, ctxAddr)) :=
  model.transports.defEqFailureProvenance ha hb hreferences

end KernelSuffixModel

namespace RecM

namespace IsPropCacheUpdate

/-- Installing one certified proposition classification changes only its
dedicated memo map and preserves the complete checker invariant. -/
theorem whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {key : Address × Address} {answer : Bool}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.isProp key answer)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        isPropCache := s.env.isPropCache.insert key answer}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertIsProp hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end IsPropCacheUpdate

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
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEq hnew
    · exact hkernel.equivalences
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
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEqCheap hnew
    · exact hkernel.equivalences
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
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertDefEqFailure hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end DefEqCacheUpdate

/-- Exact production execution for a positive equivalence-manager hit.  The
query may path-compress the manager, but no semantic cache is consulted or
written on this branch. -/
theorem isDefEq_equivHit_true
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok true s4) :
    (isDefEq a b).run methods s = .ok true s4 := by
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
  unfold EStateM.bind
  rw [hequiv]
  simp

/-- A positive manager hit is a Theory equality, not merely an optimization
claim.  The manager path is interpreted through its supported edge chain at
the exact executed context/radius key. -/
theorem isDefEq_equivHit_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {a b : KExpr .anon} {va vb : VExpr}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok true s4)
    (hI : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b vb) :
    (isDefEq a b).run methods s = .ok true s4 ∧
      WhnfStateInv layer
        (kernelCacheSemantics
          (operationalWhnfContextKeys trProj world uvars) trProj)
        trProj world support uvars Delta s4 ∧
      world.venv.IsDefEqU uvars Delta.toCtx va vb := by
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1)
      htraceWf.1
  rw [hstats] at hstatsWf
  have hctxWf :=
    (TcM.defEqCtxKey_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta) (a := a) (b := b) (s := s2))
      hstatsWf.1
  rw [hctx] at hctxWf
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hctxWf.1
  rw [hequiv] at hequivWf
  have hctxRun :
      TcM.ctxAddrForLbr (max a.lbr b.lbr) s2 = .ok ctxAddr s3 := by
    simpa [TcM.defEqCtxKey] using hctx
  have hrepresented := operationalWhnfContextKeys.representsCtx
    hstatsWf.1.2.1 hctxRun
  have hrel := hequivWf.2 rfl
  change DefEqKeyEquiv (operationalWhnfContextKeys trProj world uvars)
    trProj (CacheAuthority.stable world) support
    ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ at hrel
  have hsemantic := hrel.sound theory hequivWf.1.2.1.wf hcollision
    haSupport rfl hbSupport rfl hrepresented ha hb
  exact ⟨isDefEq_equivHit_true htrace hstats haddr hctx hequiv,
    hequivWf.1, hsemantic⟩

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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hhit : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true) :
    (isDefEq a b).run methods s = .ok true
      {s4 with equivManager := (s4.equivManager.addEquiv
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)} := by
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
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
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
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
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)}
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
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1) hI1
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
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hI3
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
  have hrel :
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj).Equiv
        (CacheAuthority.stable world) support
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ := by
    change DefEqKeyEquiv (operationalWhnfContextKeys trProj world uvars)
      trProj (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    exact hprovenance.kernelDefEqEquivCanonical hcollision
      haSupport hbSupport
  have hfinal : WhnfStateInv layer
      (kernelCacheSemantics
        (operationalWhnfContextKeys trProj world uvars) trProj)
      trProj world support uvars Delta
      {s4 with equivManager := (s4.equivManager.addEquiv
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)} :=
    hI4.addEquiv hrel
  exact ⟨isDefEq_fullHit_true htrace hstats haddr hctx hequiv hcheap hhit,
    hfinal, hsemantic⟩

/-- Exact production execution for a positive non-cheap full-cache hit found
through the guarded equivalence-root second chance.  The hit is copied to the
original pair and the original keys are then joined in the manager. -/
theorem isDefEq_rootFullHit_true
    {methods : Methods .anon} {a b : KExpr .anon}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hmiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hhit : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? = some true) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final := by
  dsimp only
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
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
  simp only [hmiss]
  change ReaderT.run
    ((liftM (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) :
        RecM .anon (Option EqKey × Option EqKey)) >>= _)
      methods s4 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em))) _ s4 = _
  unfold EStateM.bind
  rw [hroots]
  simp only [hchanged, hscope, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s5 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s5 = .ok s5 s5 from rfl]
  simp only [hhit]
  rfl

/-- Semantic acceptance and invariant preservation for the guarded positive
root/full-cache branch.  The copied original-pair entry receives fresh
provenance from the joint suffix model; the final union is justified by that
same positive entry rather than treated as bookkeeping. -/
theorem isDefEq_rootFullHit_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {va vb : VExpr}
    {ctxAddr : Address} {aRoot bRoot : EqKey}
    {s s1 s2 s3 s4 s5 : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = false)
    (hmiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hroots : TcM.withEquiv (fun em =>
      let (aRoot?, em) := em.findRootKey
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      let (bRoot?, em) := em.findRootKey
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
      ((aRoot?, bRoot?), em)) s4 = .ok (some aRoot, some bRoot) s5)
    (hchanged : (aRoot !=
        ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ ||
      bRoot != ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) = true)
    (hscope : aRoot.rootCacheScopeMatches bRoot ctxAddr
      (max a.lbr b.lbr) = true)
    (hhit : s5.env.defEqCache[
      ((canonicalPair aRoot.exprAddr bRoot.exprAddr).1,
        (canonicalPair aRoot.exprAddr bRoot.exprAddr).2, ctxAddr)]? = some true)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb)
    (hreferences :
      (CacheEntry.defEq .full
        ((canonicalPair a.addr b.addr).1,
          (canonicalPair a.addr b.addr).2, ctxAddr) true).ReferencesAuthorized
        (CacheAuthority.stable world) support) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let cachedState := {s5 with env := {s5.env with
      defEqCache := s5.env.defEqCache.insert cacheKey true}}
    let final := {cachedState with
      equivManager := cachedState.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hI1 := htraceWf.1
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1) hI1
  rw [hstats] at hstatsWf
  have hI2 := hstatsWf.1
  have hctxWf :=
    (TcM.defEqCtxKey_model_matches_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (support := support) model (Delta := Delta) (a := a) (b := b)
      (s := s2)) hI2
  rw [hctx] at hctxWf
  have hI3 := hctxWf.1
  have hrepresented := hctxWf.2.1.2.1
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hI3
  rw [hequiv] at hequivWf
  have hI4 := hequivWf.1
  have hrootsWf :=
    (TcM.withEquiv_findRootKeys_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s4) hI4
  rw [hroots] at hrootsWf
  have hI5 := hrootsWf.1
  have haPath := hrootsWf.2.1 aRoot rfl
  have hbPath := hrootsWf.2.2 bRoot rfl
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩ aRoot at haPath
  change DefEqKeyEquiv model.keys trProj (CacheAuthority.stable world) support
    ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ bRoot at hbPath
  have hrootProvenance := hI5.1.caches.hit (.defEq hhit)
  have hsemantic := hrootProvenance.kernelDefEqRootAcceptance
    theory hI5.2.1.wf hcollision haPath hbPath hscope hrepresented
      haSupport hbSupport ha hb
  have horiginalMeaning :
      DefEqMeaning trProj world model.keys.uvars Delta a b true := by
    intro _
    exact ⟨va, vb, ha, hb, hsemantic⟩
  have hnew := model.defEqProvenance hcollision .full
    haSupport hbSupport hrepresented horiginalMeaning hreferences
  have hcached : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta
      {s5 with env := {s5.env with
        defEqCache := s5.env.defEqCache.insert
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true}} :=
    DefEqCacheUpdate.full_whnfStateInv hI5 hnew
  have hrel : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
    hnew.kernelDefEqEquivCanonical hcollision haSupport hbSupport
  have hfinal := hcached.addEquiv hrel
  exact ⟨isDefEq_rootFullHit_true htrace hstats haddr hctx hequiv hcheap
    hmiss hroots hchanged hscope hhit, hfinal, hsemantic⟩

/-- Exact production execution for a positive direct cheap-cache hit.  Cheap
`true` is promoted to the full partition and recorded in the manager before
returning. -/
theorem isDefEq_cheapHit_true
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hhit : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let final := {s4 with
      env := {s4.env with
        defEqCache := s4.env.defEqCache.insert cacheKey true}
      equivManager := s4.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final := by
  dsimp only
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
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) :
        RecM .anon Bool) >>= _)
      methods s3 = _
  rw [ReaderT.run_bind]
  change EStateM.bind
    (TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩)) _ s3 = _
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
  simp only [hfullMiss, if_true]
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s4 = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s4 = .ok s4 s4 from rfl]
  simp only [hhit, if_true]
  rfl

/-- A positive cheap hit is semantically accepted, promoted with the same
provenance into the full partition, and safely joined in the manager. -/
theorem isDefEq_cheapHit_true_acceptance
    {methods : Methods .anon} {layer : WhnfLayer}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (model : KernelSuffixModel trProj world)
    {Delta : KVLCtx} {a b : KExpr .anon} {va vb : VExpr}
    {ctxAddr : Address} {s s1 s2 s3 s4 : TcState .anon}
    (theory : WhnfTheory trProj world model.keys.uvars)
    (hcollision : support.CollisionFree)
    (htrace : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s = .ok () s1)
    (hstats : TcM.bumpStats
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1}) s1 =
        .ok () s2)
    (haddr : (a.addr == b.addr) = false)
    (hctx : TcM.defEqCtxKey a b s2 = .ok ctxAddr s3)
    (hequiv : TcM.withEquiv
      (·.isEquiv ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
        ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩) s3 = .ok false s4)
    (hcheap : (s4.cheapRecursionDepth > 0) = true)
    (hfullMiss : s4.env.defEqCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = none)
    (hhit : s4.env.defEqCheapCache[
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)]? = some true)
    (hI : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta s)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta a va)
    (hb : TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta b vb) :
    let cacheKey :=
      ((canonicalPair a.addr b.addr).1,
        (canonicalPair a.addr b.addr).2, ctxAddr)
    let aKey : EqKey :=
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
    let bKey : EqKey :=
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩
    let final := {s4 with
      env := {s4.env with
        defEqCache := s4.env.defEqCache.insert cacheKey true}
      equivManager := s4.equivManager.addEquiv aKey bKey}
    (isDefEq a b).run methods s = .ok true final ∧
      WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
        trProj world support model.keys.uvars Delta final ∧
      world.venv.IsDefEqU model.keys.uvars Delta.toCtx va vb := by
  dsimp only
  have htraceWf :=
    (TcM.stepTrace_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta) "deq"
      (fun _ => s!"{TcM.addr8 a.addr} ~ {TcM.addr8 b.addr}") s) hI
  rw [htrace] at htraceWf
  have hstatsWf :=
    (TcM.bumpStats_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      (fun st : TcState .anon => {st with deqCalls := st.deqCalls + 1})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1)
      htraceWf.1
  rw [hstats] at hstatsWf
  have hctxWf :=
    (TcM.defEqCtxKey_model_matches_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (support := support) model (Delta := Delta) (a := a) (b := b)
      (s := s2)) hstatsWf.1
  rw [hctx] at hctxWf
  have hrepresented := hctxWf.2.1.2.1
  have hequivWf :=
    (TcM.withEquiv_isEquiv_whnf_wf (layer := layer)
      (semantics := kernelCacheSemantics model.keys trProj)
      (trProj := trProj) (world := world) (support := support)
      (uvars := model.keys.uvars) (Delta := Delta)
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ s3) hctxWf.1
  rw [hequiv] at hequivWf
  have hcheapProvenance := hequivWf.1.1.caches.hit (.defEqCheap hhit)
  have hmeaning := hcheapProvenance.kernelDefEqMeaningCanonical
    haSupport hbSupport hrepresented
  have hsemantic := DefEqMeaning.of_translations theory hequivWf.1.2.1.wf
    ha hb hmeaning rfl
  have hfullProvenance :
      CacheProvenance (kernelCacheSemantics model.keys trProj)
        (CacheAuthority.stable world) support
        (.defEq .full
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true) :=
    hcheapProvenance.kernelDefEqRekind
  have hcached : WhnfStateInv layer (kernelCacheSemantics model.keys trProj)
      trProj world support model.keys.uvars Delta
      {s4 with env := {s4.env with
        defEqCache := s4.env.defEqCache.insert
          ((canonicalPair a.addr b.addr).1,
            (canonicalPair a.addr b.addr).2, ctxAddr) true}} :=
    DefEqCacheUpdate.full_whnfStateInv hequivWf.1 hfullProvenance
  have hrel : DefEqKeyEquiv model.keys trProj
      (CacheAuthority.stable world) support
      ⟨a.addr, ctxAddr, max a.lbr b.lbr, a.lbr⟩
      ⟨b.addr, ctxAddr, max a.lbr b.lbr, b.lbr⟩ :=
    hfullProvenance.kernelDefEqEquivCanonical hcollision
      haSupport hbSupport
  have hfinal := hcached.addEquiv hrel
  exact ⟨isDefEq_cheapHit_true htrace hstats haddr hctx hequiv hcheap
    hfullMiss hhit, hfinal, hsemantic⟩

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
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) s1
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
