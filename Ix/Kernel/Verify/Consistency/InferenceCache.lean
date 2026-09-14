/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderOpening

/-!
# Structural inference-cache invariants

Agreement records concrete types in both cache partitions. Frame lemmas
preserve the entries at a fixed key and the loaded constants through actual
checker operations. Scope changes and unrelated cache writes do not require
a new semantic typing premise for each cached answer.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

/-- Closed source expressions use one key in every local context. Computing
that key leaves the entire checker state unchanged. -/
theorem inferKey_closed {term : KExpr .anon} (closed : term.lbr = 0)
    (before : TcState .anon) :
    TcM.inferKey term before = .ok (term.addr, emptyCtxAddr) before := by
  unfold TcM.inferKey
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _
  rw [closed]
  rfl

/-- Computing the production inference key always succeeds, including
context-address cache misses. -/
theorem inferKey_total (term : KExpr .anon) (before : TcState .anon) :
    ∃ key after, TcM.inferKey term before = .ok key after := by
  unfold TcM.inferKey TcM.ctxAddrForLbr
  change ∃ key after, EStateM.bind (fun state =>
    EStateM.bind (get : TcM .anon (TcState .anon)) _ state) _ before = .ok key after
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl]
  by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast]
    exact ⟨_, _, rfl⟩
  · rw [if_neg fast]
    cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? <;> exact ⟨_, _, rfl⟩

/-- The exact cache entry eligible at production's computed inference key.
An inference-only result cannot override a full result or serve full mode. -/
structure InferenceCacheHit (before : TcState .anon) (term : KExpr .anon) where
  key : Address × Address
  keyed : TcState .anon
  cached : KExpr .anon
  keyRun : TcM.inferKey term before = .ok key keyed
  selected : keyed.env.inferCache[key]? = some cached ∨
    (keyed.env.inferCache[key]? = none ∧ before.inferOnly = true ∧
      keyed.env.inferOnlyCache[key]? = some cached)

/-- Cache selection determines both the returned type and state. -/
theorem InferenceCacheHit.run {before : TcState .anon} {term : KExpr .anon}
    (hit : InferenceCacheHit before term) (methods : Methods .anon) :
    RecM.infer term methods before = .ok hit.cached hit.keyed := by
  change (RecM.infer term).run methods before = _
  unfold RecM.infer RecM.inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.inferKey term) _ before = _
  rw [EStateM.bind, hit.keyRun]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ hit.keyed = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) hit.keyed =
    .ok hit.keyed hit.keyed from rfl]
  rcases hit.selected with full | ⟨full, policy, only⟩
  · simp only [full]; rfl
  · simp only [full, policy, if_true, ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ hit.keyed = _
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) hit.keyed =
      .ok hit.keyed hit.keyed from rfl]
    simp only [only]
    rfl

theorem InferenceCacheHit.key_closed {before : TcState .anon} {term : KExpr .anon}
    (hit : InferenceCacheHit before term) (closed : term.lbr = 0) :
    hit.key = (term.addr, emptyCtxAddr) ∧ hit.keyed = before := by
  have run := hit.keyRun
  rw [inferKey_closed closed] at run
  exact ⟨(EStateM.Result.ok.inj run).1.symm, (EStateM.Result.ok.inj run).2.symm⟩

/-- Inspect the two concrete maps under production's policy and construct
the corresponding hit or miss witness at the supplied actual key. -/
def observeInferenceCache {before keyed : TcState .anon} {term : KExpr .anon}
    {key : Address × Address} (keyRun : TcM.inferKey term before = .ok key keyed) :
    {hit : InferenceCacheHit before term // hit.key = key ∧ hit.keyed = keyed} ⊕
      {miss : UncachedInference before term // miss.key = key ∧ miss.keyed = keyed} := by
  cases full : keyed.env.inferCache[key]? with
  | some cached =>
      exact .inl ⟨⟨key, keyed, cached, keyRun, .inl full⟩, rfl, rfl⟩
  | none =>
      by_cases policy : before.inferOnly = true
      · cases only : keyed.env.inferOnlyCache[key]? with
        | some cached =>
            exact .inl ⟨⟨key, keyed, cached, keyRun, .inr ⟨full, policy, only⟩⟩, rfl, rfl⟩
        | none => exact .inr ⟨⟨key, keyed, keyRun, full, fun _ => only⟩, rfl, rfl⟩
      · exact .inr ⟨⟨key, keyed, keyRun, full, fun active => False.elim (policy active)⟩, rfl, rfl⟩

/-- Any populated entry at this key is the specified concrete type. Both
partitions are covered so agreement survives a change in checking policy. -/
structure InferenceCacheAgreement (before : TcState .anon)
    (key : Address × Address) (type : KExpr .anon) : Prop where
  full : ∀ cached, before.env.inferCache[key]? = some cached → cached = type
  only : ∀ cached, before.env.inferOnlyCache[key]? = some cached → cached = type

/-- Relevant data retained by an operation: the two entries at one key and
every previously loaded declaration. New declarations may be loaded; other
keys and checker fields may change. -/
structure InferenceCacheFrame (key : Address × Address)
    (before after : TcState .anon) : Prop where
  full : after.env.inferCache[key]? = before.env.inferCache[key]?
  only : after.env.inferOnlyCache[key]? = before.env.inferOnlyCache[key]?
  constants : ∀ id concrete, before.env.get? id = some concrete →
    after.env.get? id = some concrete

/-- The existing exact-map transitions are also declaration extensions. -/
theorem InferenceCacheFrame.of_eq {key : Address × Address}
    {before after : TcState .anon}
    (full : after.env.inferCache[key]? = before.env.inferCache[key]?)
    (only : after.env.inferOnlyCache[key]? = before.env.inferOnlyCache[key]?)
    (constants : after.env.consts = before.env.consts) :
    InferenceCacheFrame key before after := by
  refine ⟨full, only, ?_⟩
  intro id concrete loaded
  simpa only [KEnv.get?, constants] using loaded

theorem InferenceCacheFrame.refl (key : Address × Address) (state : TcState .anon) :
    InferenceCacheFrame key state state := .of_eq rfl rfl rfl

theorem InferenceCacheFrame.trans {key : Address × Address}
    {before middle after : TcState .anon}
    (first : InferenceCacheFrame key before middle)
    (second : InferenceCacheFrame key middle after) :
    InferenceCacheFrame key before after :=
  ⟨second.full.trans first.full, second.only.trans first.only,
    fun id concrete loaded => second.constants id concrete (first.constants id concrete loaded)⟩

theorem InferenceCacheAgreement.frame {key : Address × Address} {type : KExpr .anon}
    {before after : TcState .anon} (agreement : InferenceCacheAgreement before key type)
    (frame : InferenceCacheFrame key before after) : InferenceCacheAgreement after key type := by
  refine ⟨?_, ?_⟩
  · intro cached found; exact agreement.full cached (frame.full.symm.trans found)
  · intro cached found; exact agreement.only cached (frame.only.symm.trans found)

theorem InferenceCacheAgreement.selected {before : TcState .anon} {term : KExpr .anon}
    {type : KExpr .anon} (hit : InferenceCacheHit before term)
    (agreement : InferenceCacheAgreement hit.keyed hit.key type) : hit.cached = type := by
  rcases hit.selected with full | ⟨_, _, only⟩
  · exact agreement.full _ full
  · exact agreement.only _ only

/-- Reuse a closed expression's selected hit after an operation preserving
its entries and checking policy. Its key and result are derived, not supplied
as another observation of inference. -/
def InferenceCacheHit.transport {before after : TcState .anon} {term : KExpr .anon}
    (hit : InferenceCacheHit before term) (closed : term.lbr = 0)
    (frame : InferenceCacheFrame (term.addr, emptyCtxAddr) before after)
    (policy : after.inferOnly = before.inferOnly) : InferenceCacheHit after term := {
  key := (term.addr, emptyCtxAddr), keyed := after, cached := hit.cached
  keyRun := inferKey_closed closed after
  selected := by
    obtain ⟨key, state⟩ := hit.key_closed closed
    have selected := hit.selected
    rw [key, state] at selected
    rcases selected with full | ⟨full, onlyPolicy, only⟩
    · exact .inl (frame.full.trans full)
    · exact .inr ⟨frame.full.trans full, policy.trans onlyPolicy, frame.only.trans only⟩
}

/-- The final write is an exact state update, with the policy captured at
entry rather than inferred from any intervening recursive call. -/
theorem cacheInferResult_eq (policy : Bool) (key : Address × Address)
    (type : KExpr .anon) (methods : Methods .anon) (before : TcState .anon) :
    RecM.cacheInferResult policy key type methods before = .ok ()
      (if policy then {before with env := {before.env with
        inferOnlyCache := before.env.inferOnlyCache.insert key type}}
      else {before with env := {before.env with
        inferCache := before.env.inferCache.insert key type}}) := by
  cases policy <;> rfl

/-- Writing a matching result preserves agreement at the written key. -/
theorem InferenceCacheAgreement.write {before after : TcState .anon}
    {key : Address × Address} {type : KExpr .anon} {policy : Bool} {methods : Methods .anon}
    (agreement : InferenceCacheAgreement before key type)
    (run : RecM.cacheInferResult policy key type methods before = .ok () after) :
    InferenceCacheAgreement after key type := by
  rw [cacheInferResult_eq] at run
  cases policy <;> cases run
  · refine ⟨?_, agreement.only⟩
    intro cached found
    simpa using found.symm
  · refine ⟨agreement.full, ?_⟩
    intro cached found
    simpa using found.symm

/-- Every outcome preserves the observed entries, including failure. -/
def PreservesInferenceCache (key : Address × Address) (action : TcM .anon α) : Prop :=
  ∀ before, match action before with
    | .ok _ after | .error _ after => InferenceCacheFrame key before after

theorem PreservesInferenceCache.pure (key : Address × Address) (value : α) :
    PreservesInferenceCache key (pure value) := fun before => .refl key before

theorem PreservesInferenceCache.bind {key : Address × Address}
    {action : TcM .anon α} {next : α → TcM .anon γ}
    (first : PreservesInferenceCache key action)
    (rest : ∀ value, PreservesInferenceCache key (next value)) :
    PreservesInferenceCache key (action >>= next) := by
  intro before
  change (match EStateM.bind action next before with
    | .ok _ after | .error _ after => InferenceCacheFrame key before after)
  have initial := first before
  cases run : action before with
  | error err after =>
      rw [EStateM.bind, run]
      simpa only [run] using initial
  | ok value middle =>
      rw [run] at initial
      rw [EStateM.bind, run]
      simp only
      have final := rest value middle
      cases result : next value middle <;> rw [result] at final <;> exact initial.trans final

theorem PreservesInferenceCache.runIntern (key : Address × Address) (action : InternM .anon α) :
    PreservesInferenceCache key (TcM.runIntern action) := fun _ => .of_eq rfl rfl rfl

theorem PreservesInferenceCache.inferKey (key : Address × Address) (term : KExpr .anon) :
    PreservesInferenceCache key (TcM.inferKey term) := by
  intro before
  cases run : TcM.inferKey term before
  all_goals
    unfold TcM.inferKey at run
    change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
    unfold TcM.ctxAddrForLbr at run
    change EStateM.bind (fun state => EStateM.bind (get : TcM .anon (TcState .anon))
      _ state) _ before = _ at run
    simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
      .ok before before from rfl] at run
    by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
    · rw [if_pos fast] at run
      cases run <;> exact .of_eq rfl rfl rfl
    · rw [if_neg fast] at run
      cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? <;>
        rw [cached] at run <;> cases run <;> exact .of_eq rfl rfl rfl

theorem PreservesInferenceCache.openBinder (key : Address × Address)
    (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo) (type body : KExpr .anon) :
    PreservesInferenceCache key (TcM.openBinder name bi type body) := by
  intro before
  rw [openBinder_eq]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [room, if_true]; exact .of_eq rfl rfl rfl
  · simp only [room, if_false]; exact .of_eq rfl rfl rfl

/-- An actual insertion at another key leaves this key's entries and loaded
declarations unchanged, for either validation policy. -/
theorem PreservesInferenceCache.write_other {key other : Address × Address}
    (different : other ≠ key) (policy : Bool) (type : KExpr .anon) (methods : Methods .anon) :
    PreservesInferenceCache key (RecM.cacheInferResult policy other type methods) := by
  intro before
  rw [cacheInferResult_eq]
  cases policy <;> apply InferenceCacheFrame.of_eq <;>
    simp [Std.HashMap.getElem?_insert, different]

/-- Exact scope cleanup on either outcome, retaining the body's other state
updates. Shared by inference inversion and cache-preservation proofs. -/
theorem withLctxScope_eq (action : RecM .anon α)
    (methods : Methods .anon) (before : TcState .anon) :
    (RecM.withLctxScope action).run methods before =
      match action.run methods before with
      | .ok value after =>
          .ok value {after with lctx := after.lctx.truncate before.lctx.size}
      | .error err after =>
          .error err {after with lctx := after.lctx.truncate before.lctx.size} := by
  unfold RecM.withLctxScope
  rw [ReaderT.run_bind]
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  simp only
  unfold tryFinally
  change EStateM.map (fun pair : α × PUnit => pair.1)
    (tryFinally' (action.run methods) (fun _ =>
      (modify (fun after : TcState .anon =>
        {after with lctx := after.lctx.truncate before.lctx.size}) :
        TcM .anon PUnit))) before = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases run : action.run methods before <;> simp only [run] <;> rfl

theorem PreservesInferenceCache.withLctxScope {key : Address × Address}
    {action : RecM .anon α} {methods : Methods .anon}
    (preserved : PreservesInferenceCache key (action.run methods)) :
    PreservesInferenceCache key ((RecM.withLctxScope action).run methods) := by
  intro before
  rw [withLctxScope_eq]
  have frame := preserved before
  cases run : action.run methods before <;> rw [run] at frame <;>
    exact ⟨frame.full, frame.only, frame.constants⟩

/-- Changing only local declarations never changes closed cache data. -/
theorem InferenceCacheFrame.localContext (key : Address × Address)
    (before : TcState .anon) (context : LocalContext .anon) :
    InferenceCacheFrame key before {before with lctx := context} := .of_eq rfl rfl rfl

/-- Agreement itself is independent of the currently selected policy. -/
theorem InferenceCacheAgreement.policy {before : TcState .anon}
    {key : Address × Address} {type : KExpr .anon}
    (agreement : InferenceCacheAgreement before key type) (policy : Bool) :
    InferenceCacheAgreement {before with inferOnly := policy} key type :=
  ⟨agreement.full, agreement.only⟩

/-- Cache clearing establishes agreement vacuously, while retaining loaded
declarations for subsequent misses. -/
theorem InferenceCacheAgreement.clearReductionCaches (before : TcState .anon)
    (key : Address × Address) (type : KExpr .anon) :
    InferenceCacheAgreement {before with env := before.env.clearReductionCaches} key type := by
  constructor <;> intro cached found <;> simp [KEnv.clearReductionCaches] at found

/-- Exact policy restoration, including after an error from the body. -/
theorem withInferOnly_eq (action : TcM .anon α) (before : TcState .anon) :
    TcM.withInferOnly action before =
      match action {before with inferOnly := true} with
      | .ok value after => .ok value {after with inferOnly := before.inferOnly}
      | .error err after => .error err {after with inferOnly := before.inferOnly} := by
  unfold TcM.withInferOnly
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl]
  unfold tryFinally
  change EStateM.map (fun pair : α × PUnit => pair.1)
    (tryFinally' action (fun _ =>
      (modify (fun after : TcState .anon =>
        {after with inferOnly := before.inferOnly}) : TcM .anon PUnit)))
        {before with inferOnly := true} = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases run : action {before with inferOnly := true} <;> simp only [run] <;> rfl

theorem PreservesInferenceCache.withInferOnly {key : Address × Address} {action : TcM .anon α}
    (preserved : PreservesInferenceCache key action) :
    PreservesInferenceCache key (TcM.withInferOnly action) := by
  intro before
  rw [withInferOnly_eq]
  have frame := preserved {before with inferOnly := true}
  cases run : action {before with inferOnly := true} <;> rw [run] at frame <;>
    exact ⟨frame.full, frame.only, frame.constants⟩

/-- A successful full inference leaves its exact result in the full cache,
whether the call reused an entry or executed the uncached branch. -/
theorem infer_full_success_cache {source result : KExpr .anon} {methods : Methods .anon}
    {before keyed after : TcState .anon} {key : Address × Address}
    (full : before.inferOnly = false)
    (keyRun : TcM.inferKey source before = .ok key keyed)
    (accepted : RecM.infer source methods before = .ok result after) :
    after.env.inferCache[key]? = some result := by
  rcases observeInferenceCache keyRun with ⟨hit, keyEq, _⟩ | ⟨miss, keyEq, _⟩
  · rw [hit.run] at accepted
    cases accepted
    rcases hit.selected with found | ⟨_, only, _⟩
    · simpa only [keyEq] using found
    · rw [full] at only
      cases only
  · obtain ⟨middle, _, written⟩ := infer_uncached_success_state miss accepted
    rw [written, full]
    simp only [Bool.false_eq_true, if_false, keyEq, Std.HashMap.getElem?_insert_self]

/-- Actual full inference and a proved frame construct the later cache hit.
The later policy is unrestricted because the full cache has priority. -/
def InferenceCacheHit.fromFullRun {source result : KExpr .anon} {methods : Methods .anon}
    {before keyed after current currentKeyed : TcState .anon} {key : Address × Address}
    (full : before.inferOnly = false)
    (keyRun : TcM.inferKey source before = .ok key keyed)
    (accepted : RecM.infer source methods before = .ok result after)
    (frame : InferenceCacheFrame key after current)
    (currentKeyRun : TcM.inferKey source current = .ok key currentKeyed) :
    InferenceCacheHit current source := by
  have keyFrame := PreservesInferenceCache.inferKey key source current
  rw [currentKeyRun] at keyFrame
  exact ⟨key, currentKeyed, result, currentKeyRun,
    .inl (keyFrame.full.trans (frame.full.trans (infer_full_success_cache full keyRun accepted)))⟩

end Ix.Kernel.Consistency
