/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Contracts
import Batteries.Data.UInt

/-!
# DefEq memo semantics under the checker invariant

The conversion entry consults three memos before any reduction: the
equivalence manager, the full DefEq cache, and the cheap DefEq cache. This
module states what each positive answer certifies in the invariant's terms, a
chain of justified union-find edges between the two operand keys, and proves
that every memo update production performs preserves the invariant: path
halving during a query, insertion of a proved answer into either cache, and
union of the two keys after a positive answer.

A chain is recorded existentially at the registration where it was proved.
Reading it back at the caller's registration is the conversion instance of
the context-digest boundary and is stated once as `DefEqMemoTransport`; the
tier proofs consume that premise and supply nothing weaker.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-! ### Exact run equations of the entry's non-recursive operations -/

theorem stepTrace_eq (tag : String) (payload : Unit → String) (state : TcState .anon) :
    TcM.stepTrace tag payload state = .ok () state := by
  unfold TcM.stepTrace
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) state = .ok state state from rfl]
  dsimp only
  split <;> rfl

theorem bumpStats_eq (update : TcState .anon → TcState .anon) (state : TcState .anon) :
    TcM.bumpStats update state = .ok () (if state.stats then update state else state) := by
  unfold TcM.bumpStats
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) state = .ok state state from rfl]
  dsimp only
  by_cases enabled : state.stats = true
  · rw [if_pos enabled, if_pos enabled]; rfl
  · rw [if_neg enabled, if_neg enabled]; rfl

theorem tick_eq (state : TcState .anon) :
    TcM.tick state = if state.recFuel == 0 then .error .maxRecFuel state
      else .ok () {state with recFuel := state.recFuel - 1} := by
  unfold TcM.tick
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) state = .ok state state from rfl]
  dsimp only
  split <;> rfl

/-- The manager operation is state-pure outside the union-find field. -/
theorem withEquiv_eq {α : Type} (update : EquivManager → α × EquivManager) (state : TcState .anon) :
    TcM.withEquiv update state = .ok (update state.equivManager).1
      {state with equivManager := (update state.equivManager).2} := by
  unfold TcM.withEquiv
  rcases result : update state.equivManager with ⟨value, manager⟩
  change EStateM.bind (fun current : TcState .anon =>
    .ok current.equivManager {current with equivManager := {}}) _ state = _
  unfold EStateM.bind
  simp only
  rw [result]
  rfl

/-- Context-digest computation never fails. -/
theorem ctxAddrForLbr_ok (lbr : UInt64) (state : TcState .anon) :
    ∃ addr after, TcM.ctxAddrForLbr lbr state = .ok addr after := by
  unfold TcM.ctxAddrForLbr
  change ∃ addr after, EStateM.bind (get : TcM .anon (TcState .anon)) _ state = .ok addr after
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) state = .ok state state from rfl]
  dsimp only
  by_cases fast : (lbr == 0 || state.ctx.isEmpty) = true
  · rw [if_pos fast]
    exact ⟨_, _, rfl⟩
  · rw [if_neg fast]
    cases state.ctxAddrCache[(state.ctxId, lbr)]? <;> exact ⟨_, _, rfl⟩

theorem defEqCtxKey_def (left right : KExpr .anon) :
    TcM.defEqCtxKey left right = TcM.ctxAddrForLbr (max left.lbr right.lbr) := rfl

theorem canonicalPair_cases (left right : Address) :
    canonicalPair left right = (left, right) ∨ canonicalPair left right = (right, left) := by
  unfold canonicalPair
  split
  · exact .inl rfl
  · exact .inr rfl

private theorem max_comm_uint64 (left right : UInt64) : max left right = max right left :=
  UInt64.toNat_inj.mp (by simp only [UInt64.toNat_max, Nat.max_comm])

/-- The runtime guard of a root-derived cache probe, decoded. -/
theorem EqKey.rootCacheScopeMatches_eq {left right : EqKey} {ctxAddr : Address} {lbr : UInt64}
    (guard : left.rootCacheScopeMatches right ctxAddr lbr = true) :
    left.ctxAddr = ctxAddr ∧ right.ctxAddr = ctxAddr ∧ left.lbr = lbr ∧ right.lbr = lbr := by
  simp only [EqKey.rootCacheScopeMatches, Bool.and_eq_true, beq_iff_eq] at guard
  exact ⟨guard.1.1.1.1, guard.1.1.1.2, guard.1.1.2, guard.1.2⟩

/-! ### Invariant preservation through memo updates -/

namespace CheckerInvariant

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
  {context : Model.Context β} {bounds : List VLevel}

/-- Operations that retain every map except the DefEq memos and the
equivalence manager preserve the invariant once the updated memos are proved
sound. -/
theorem ofDefEqMemos {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (frame : LocalStateFrame before after)
    (constants : after.env.consts = before.env.consts)
    (blocks : after.env.blocks = before.env.blocks)
    (coherent : after.env.intern.WF)
    (full : after.env.inferCache = before.env.inferCache)
    (only : after.env.inferOnlyCache = before.env.inferOnlyCache)
    (whnf : ∀ partition : WhnfCachePartition, partition.cache after = partition.cache before)
    (defEq : DefEqCacheSemantics.{u,v} resolve entries after)
    (manager : EquivManagerSemantics.{u,v} resolve entries after.equivManager)
    (unfold : after.env.unfoldCache = before.env.unfoldCache)
    (isProp : after.env.isPropCache = before.env.isPropCache) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after where
  sourceCache := ⟨valid.sourceState.ofMaps frame.loader constants blocks coherent,
    valid.cache.ofMaps full only constants⟩
  synthesis := valid.synthesis.elim fun history => ⟨history.ofMaps full only⟩
  whnf := valid.whnf.elim fun history => ⟨history.ofMaps whnf⟩
  structural := frame.invariant valid.structural
  reading := valid.reading.congr frame.context.symm
  origin := valid.origin
  semantics := ⟨valid.semantics.whnf.ofMaps whnf, defEq, manager,
    valid.semantics.unfold.ofMap unfold, valid.semantics.isProp.ofMap isProp⟩

/-- A state that differs from a valid one only in the two DefEq memos, the
equivalence manager, and fields outside the environment and local context
satisfies the invariant once the memos and manager are proved sound. -/
theorem ofDefEqUpdate {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (env : ∃ full cheap, after.env =
      {before.env with defEqCache := full, defEqCheapCache := cheap})
    (lctx : after.lctx = before.lctx)
    (loader : after.lazyFault = before.lazyFault)
    (defEq : DefEqCacheSemantics.{u,v} resolve entries after)
    (manager : EquivManagerSemantics.{u,v} resolve entries after.equivManager) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after := by
  obtain ⟨full, cheap, env⟩ := env
  exact valid.ofDefEqMemos ⟨by rw [env]; exact Nat.le_refl _, by rw [lctx]; exact .refl _, loader⟩
    (by rw [env]) (by rw [env]) (by rw [env]; exact valid.coherent) (by rw [env]) (by rw [env])
    (fun partition => by cases partition <;> simp only [WhnfCachePartition.cache, env])
    defEq manager (by rw [env]) (by rw [env])

/-- A state that differs only outside the environment maps, the manager, and
the local context; both memos keep their semantics. -/
theorem ofDefEqScalars {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (env : after.env = before.env) (lctx : after.lctx = before.lctx)
    (loader : after.lazyFault = before.lazyFault)
    (manager : after.equivManager = before.equivManager) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds after :=
  valid.ofDefEqUpdate ⟨before.env.defEqCache, before.env.defEqCheapCache, by rw [env]⟩ lctx loader
    (valid.semantics.defEq.ofMaps fun partition => by
      cases partition <;> simp only [DefEqCachePartition.cache, env])
    (by rw [manager]; exact valid.semantics.equivalence)

end CheckerInvariant

/-! ### What the memos certify -/

section Semantics

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}

theorem AddressConversion.symm {left right ctxAddr : Address}
    (recorded : AddressConversion.{u,v} resolve entries left right ctxAddr) :
    AddressConversion.{u,v} resolve entries right left ctxAddr := by
  obtain ⟨state, locals, context, a, b, ta, tb, aAddr, bAddr, structural, reading, digest, aReads,
    bReads, aTyped, bTyped, claim⟩ := recorded
  exact ⟨state, locals, context, b, a, tb, ta, bAddr, aAddr, structural, reading,
    by rw [max_comm_uint64]; exact digest, bReads, aReads, bTyped, aTyped, claim.symm⟩

/-- A positive equivalence query certifies a chain between the two keys, and
its path halving keeps the manager valid. -/
theorem EquivManagerSemantics.isEquiv {manager : EquivManager}
    (valid : EquivManagerSemantics.{u,v} resolve entries manager) (left right : EqKey) :
    EquivManagerSemantics.{u,v} resolve entries (manager.isEquiv left right).2 ∧
      ((manager.isEquiv left right).1 = true → EqKeyChain.{u,v} resolve entries left right) :=
  EquivManager.WF.isEquiv (EqKeyChain.equivalence resolve entries) valid left right

/-- Both representative lookups keep the manager valid and relate each
returned representative to its query by a chain. -/
theorem EquivManagerSemantics.findRootKeys {manager : EquivManager}
    (valid : EquivManagerSemantics.{u,v} resolve entries manager) (left right : EqKey) :
    let result :=
      let (leftRoot, manager) := manager.findRootKey left
      let (rightRoot, manager) := manager.findRootKey right
      ((leftRoot, rightRoot), manager)
    EquivManagerSemantics.{u,v} resolve entries result.2 ∧
      (∀ root, result.1.1 = some root → EqKeyChain.{u,v} resolve entries left root) ∧
      (∀ root, result.1.2 = some root → EqKeyChain.{u,v} resolve entries right root) :=
  EquivManager.WF.findRootKeys (EqKeyChain.equivalence resolve entries) valid left right

/-- Recording a certified chain keeps the manager valid. -/
theorem EquivManagerSemantics.addEquiv {manager : EquivManager}
    (valid : EquivManagerSemantics.{u,v} resolve entries manager) {left right : EqKey}
    (chain : EqKeyChain.{u,v} resolve entries left right) :
    EquivManagerSemantics.{u,v} resolve entries (manager.addEquiv left right) :=
  EquivManager.WF.addEquiv (EqKeyChain.equivalence resolve entries) valid chain

/-- Replacing the manager leaves both cache partitions unchanged. -/
theorem DefEqCacheSemantics.setManager {state : TcState .anon}
    (valid : DefEqCacheSemantics.{u,v} resolve entries state) (manager : EquivManager) :
    DefEqCacheSemantics.{u,v} resolve entries {state with equivManager := manager} :=
  valid.ofMaps fun partition => by cases partition <;> rfl

/-- Inserting an answer at one key into either partition preserves the cache
semantics once a positive answer is recorded at that key. -/
theorem DefEqCacheSemantics.ofInsert {before after : TcState .anon}
    (valid : DefEqCacheSemantics.{u,v} resolve entries before)
    (key : Address × Address × Address) (value : Bool)
    (full : after.env.defEqCache = before.env.defEqCache ∨
      after.env.defEqCache = before.env.defEqCache.insert key value)
    (cheap : after.env.defEqCheapCache = before.env.defEqCheapCache ∨
      after.env.defEqCheapCache = before.env.defEqCheapCache.insert key value)
    (justified : value = true → AddressConversion.{u,v} resolve entries key.1 key.2.1 key.2.2) :
    DefEqCacheSemantics.{u,v} resolve entries after := by
  intro partition stored hit
  have inserted : ∀ (map : Std.HashMap (Address × Address × Address) Bool),
      (∀ stored : Address × Address × Address, map[stored]? = some true →
        AddressConversion.{u,v} resolve entries stored.1 stored.2.1 stored.2.2) →
      (map.insert key value)[stored]? = some true →
      AddressConversion.{u,v} resolve entries stored.1 stored.2.1 stored.2.2 := by
    intro map old found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · next same =>
      rw [← eq_of_beq same]
      exact justified (Option.some.inj found)
    · exact old stored found
  cases partition with
  | full =>
      rcases full with same | written
      · exact valid .full stored (by simpa only [DefEqCachePartition.cache, same] using hit)
      · exact inserted _ (valid .full) (by simpa only [DefEqCachePartition.cache, written] using hit)
  | cheap =>
      rcases cheap with same | written
      · exact valid .cheap stored (by simpa only [DefEqCachePartition.cache, same] using hit)
      · exact inserted _ (valid .cheap) (by simpa only [DefEqCachePartition.cache, written] using hit)
/-- A positive direct-cache hit at the canonical key of a pair is a justified
edge between the pair's keys. -/
theorem DefEqCacheSemantics.hitEdge {state : TcState .anon}
    (valid : DefEqCacheSemantics.{u,v} resolve entries state) (partition : DefEqCachePartition)
    {left right : KExpr .anon} {lo hi ctxAddr : Address}
    (canonical : canonicalPair left.addr right.addr = (lo, hi))
    (hit : (partition.cache state)[(lo, hi, ctxAddr)]? = some true) :
    EqKeyConversion.{u,v} resolve entries ⟨left.addr, ctxAddr, max left.lbr right.lbr, left.lbr⟩
      ⟨right.addr, ctxAddr, max left.lbr right.lbr, right.lbr⟩ := by
  have recorded := valid partition _ hit
  refine ⟨rfl, rfl, ?_⟩
  rcases canonicalPair_cases left.addr right.addr with same | swapped
  · rw [canonical] at same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact recorded
  · rw [canonical] at swapped
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj swapped
    exact recorded.symm

/-- A positive cache hit at the canonical key of two representatives that
pass the scope guard is a justified edge between the representatives. -/
theorem DefEqCacheSemantics.rootEdge {state : TcState .anon}
    (valid : DefEqCacheSemantics.{u,v} resolve entries state) (partition : DefEqCachePartition)
    {leftRoot rightRoot : EqKey} {lo hi ctxAddr : Address} {lbr : UInt64}
    (scope : leftRoot.rootCacheScopeMatches rightRoot ctxAddr lbr = true)
    (canonical : canonicalPair leftRoot.exprAddr rightRoot.exprAddr = (lo, hi))
    (hit : (partition.cache state)[(lo, hi, ctxAddr)]? = some true) :
    EqKeyConversion.{u,v} resolve entries leftRoot rightRoot := by
  obtain ⟨leftCtx, rightCtx, leftLbr, rightLbr⟩ := EqKey.rootCacheScopeMatches_eq scope
  have recorded := valid partition _ hit
  refine ⟨leftCtx.trans rightCtx.symm, leftLbr.trans rightLbr.symm, ?_⟩
  rw [leftCtx]
  rcases canonicalPair_cases leftRoot.exprAddr rightRoot.exprAddr with same | swapped
  · rw [canonical] at same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact recorded
  · rw [canonical] at swapped
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj swapped
    exact recorded.symm

end Semantics

/-- Recording a certified chain in the manager preserves the invariant. -/
theorem CheckerInvariant.addEquiv {β : Type u} {resolve : Address → Option (ConstRef β)}
    {anchor entries : Model.Environment β} {source : Ixon.Env}
    {catalog : List (SourceCacheRequest source)} {locals : List FVarId}
    {context : Model.Context β} {bounds : List VLevel} {state : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state)
    {left right : EqKey} (chain : EqKeyChain.{u,v} resolve entries left right) :
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds
      {state with equivManager := state.equivManager.addEquiv left right} :=
  valid.ofDefEqUpdate ⟨_, _, rfl⟩ rfl rfl (valid.semantics.defEq.setManager _)
    (valid.semantics.equivalence.addEquiv chain)

/-! ### Recording a proved conversion -/

section Recording

variable {β : Type u} (resolve : Address → Option (ConstRef β))
  (anchor entries : Model.Environment β) (source : Ixon.Env)
  (catalog : List (SourceCacheRequest source))

/-- Where a comparison's context key was computed: an invariant state at the
caller's registration whose actual digest at the pair's joint radius is the
key. -/
def DefEqKeyOrigin (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (left right : KExpr .anon) (ctxAddr : Address) : Prop :=
  ∃ (state after : TcState .anon),
    CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds state ∧
    TcM.ctxAddrForLbr (max left.lbr right.lbr) state = .ok ctxAddr after

/-- Transport of a certified chain between the keys of two operands to the
caller's registration. A chain is recorded existentially at the registrations
where its edges were proved; identifying those sources, annotated readings,
and local contexts with the caller's is the conversion instance of the
context-digest boundary and is not derivable from the state maps. The memo
tiers consume exactly this premise. -/
def DefEqMemoTransport : Prop :=
  ∀ (locals : List FVarId) (context : Model.Context β) (bounds : List VLevel)
    (left right : KExpr .anon) (a b : AExpr β) (ctxAddr : Address),
    DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds
      left right ctxAddr →
    readScopedExpr? resolve locals left = some a.erase →
    (∃ type, TypingClaim.{u,v} entries context a type) →
    readScopedExpr? resolve locals right = some b.erase →
    (∃ type, TypingClaim.{u,v} entries context b type) →
    EqKeyChain.{u,v} resolve entries ⟨left.addr, ctxAddr, max left.lbr right.lbr, left.lbr⟩
      ⟨right.addr, ctxAddr, max left.lbr right.lbr, right.lbr⟩ →
    ConversionClaim.{u,v} entries context a b

end Recording

section RecordingLemmas

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {source : Ixon.Env}
  {catalog : List (SourceCacheRequest source)}

/-- Key computation from an invariant state establishes its own origin. -/
theorem DefEqKeyOrigin.ofRun {locals : List FVarId} {context : Model.Context β} {bounds : List VLevel}
    {left right : KExpr .anon} {ctxAddr : Address} {before after : TcState .anon}
    (valid : CheckerInvariant.{u,v} resolve anchor entries source catalog locals context bounds before)
    (run : TcM.defEqCtxKey left right before = .ok ctxAddr after) :
    DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds left right ctxAddr :=
  ⟨before, after, valid, run⟩

/-- A conversion proved at the registration where the key was computed is a
recorded conversion of the pair's addresses at that key. -/
theorem AddressConversion.ofClaim {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {left right : KExpr .anon} {ctxAddr : Address} {a b : AExpr β}
    (origin : DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds
      left right ctxAddr)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type)
    (claim : ConversionClaim.{u,v} entries context a b) :
    AddressConversion.{u,v} resolve entries left.addr right.addr ctxAddr := by
  obtain ⟨state, after, valid, digest⟩ := origin
  exact ⟨state, locals, context, left, right, a, b, rfl, rfl, valid.structural, valid.reading,
    ⟨after, digest⟩, leftReads, rightReads, leftTyped, rightTyped, claim⟩

/-- The same conversion as a justified edge between the pair's keys. -/
theorem EqKeyConversion.ofClaim {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {left right : KExpr .anon} {ctxAddr : Address} {a b : AExpr β}
    (origin : DefEqKeyOrigin.{u,v} resolve anchor entries source catalog locals context bounds
      left right ctxAddr)
    (leftReads : readScopedExpr? resolve locals left = some a.erase)
    (rightReads : readScopedExpr? resolve locals right = some b.erase)
    (leftTyped : ∃ type, TypingClaim.{u,v} entries context a type)
    (rightTyped : ∃ type, TypingClaim.{u,v} entries context b type)
    (claim : ConversionClaim.{u,v} entries context a b) :
    EqKeyConversion.{u,v} resolve entries ⟨left.addr, ctxAddr, max left.lbr right.lbr, left.lbr⟩
      ⟨right.addr, ctxAddr, max left.lbr right.lbr, right.lbr⟩ :=
  ⟨rfl, rfl, AddressConversion.ofClaim origin leftReads rightReads leftTyped rightTyped claim⟩

end RecordingLemmas

end Ix.Kernel.Consistency
