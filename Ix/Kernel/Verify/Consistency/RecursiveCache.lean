/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.LazyCache

/-!
# Cache preservation through recursive inference

Finite operational trees follow the actual smaller method table, recording
the keys written by successful misses. An entry outside those writes and its
loaded declaration survive the entire inference, so a closed cached witness
can be reused afterward. No semantic typing or per-call cache frame is an input.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Key computation may memoize a context digest but cannot change policy. -/
theorem inferKey_policy {term : KExpr .anon} {before after : TcState .anon}
    {key : Address × Address} (run : TcM.inferKey term before = .ok key after) :
    after.inferOnly = before.inferOnly := by
  unfold TcM.inferKey at run
  change EStateM.bind (TcM.ctxAddrForLbr term.lbr) _ before = _ at run
  unfold TcM.ctxAddrForLbr at run
  change EStateM.bind (fun state => EStateM.bind (get : TcM .anon (TcState .anon))
    _ state) _ before = _ at run
  simp only [EStateM.bind, show (get : TcM .anon (TcState .anon)) before =
    .ok before before from rfl] at run
  by_cases fast : (term.lbr == 0 || before.ctx.isEmpty) = true
  · rw [if_pos fast] at run
    cases run; rfl
  · rw [if_neg fast] at run
    cases cached : before.ctxAddrCache[(before.ctxId, term.lbr)]? <;>
      rw [cached] at run <;> cases run <;> rfl

/-- Hash conversion executes only tracing and its optional statistics update.
The exact state includes that counter update; it is not assumed unchanged. -/
theorem isDefEq_hash_state {left right : KExpr .anon}
    (equal : (left.addr == right.addr) = true)
    (methods : Methods .anon) (before : TcState .anon) :
    RecM.isDefEq left right methods before = .ok true
      (if before.stats then {before with deqCalls := before.deqCalls + 1} else before) := by
  have traced : TcM.stepTrace "deq"
      (fun _ => s!"{TcM.addr8 left.addr} ~ {TcM.addr8 right.addr}") before = .ok () before := by
    unfold TcM.stepTrace
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
    dsimp only
    split <;> rfl
  have bumped : TcM.bumpStats
      (fun state : TcState .anon => {state with deqCalls := state.deqCalls + 1}) before =
      .ok () (if before.stats then {before with deqCalls := before.deqCalls + 1} else before) := by
    unfold TcM.bumpStats
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
    rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
    dsimp only
    by_cases enabled : before.stats = true
    · rw [if_pos enabled, if_pos enabled]; rfl
    · rw [if_neg enabled, if_neg enabled]; rfl
  change (RecM.isDefEq left right).run methods before = _
  unfold RecM.isDefEq
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.stepTrace "deq"
    (fun _ => s!"{TcM.addr8 left.addr} ~ {TcM.addr8 right.addr}")) _ before = _
  rw [EStateM.bind, traced]
  simp only [ReaderT.run_bind]
  change EStateM.bind (TcM.bumpStats
    (fun state : TcState .anon => {state with deqCalls := state.deqCalls + 1})) _ before = _
  rw [EStateM.bind, bumped]
  simp only [equal, if_true]
  rfl

/-- The supported conversion path retains inference caches, loaded sources,
and the caller's checking policy even when statistics are enabled. -/
theorem isDefEq_hash_frame {left right : KExpr .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (equal : (left.addr == right.addr) = true)
    (run : RecM.isDefEq left right methods before = .ok true after)
    (key : Address × Address) :
    InferenceCacheFrame key before after ∧ after.inferOnly = before.inferOnly := by
  rw [isDefEq_hash_state equal] at run
  split at run <;> cases run <;> exact ⟨(.of_eq rfl rfl rfl), rfl⟩

private theorem openBinder_policy {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body opened : KExpr .anon}
    {fresh : FVarId} {before after : TcState .anon}
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    after.inferOnly = before.inferOnly := by
  rw [openBinder_eq] at run
  split at run
  · cases run; rfl
  · contradiction

private theorem openBinder_frame {name : Mode.anon.F Name}
    {bi : Mode.anon.F Lean.BinderInfo} {domain body opened : KExpr .anon}
    {fresh : FVarId} {before after : TcState .anon} (key : Address × Address)
    (run : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    InferenceCacheFrame key before after := by
  have frame := PreservesInferenceCache.openBinder key name bi domain body before
  rw [run] at frame
  exact frame

private theorem infer_miss_frame {term result : KExpr .anon}
    {methods : Methods .anon} {before after : TcState .anon} {key : Address × Address}
    (miss : UncachedInference before term) (different : miss.key ≠ key)
    (accepted : RecM.infer term methods before = .ok result after)
    (uncached : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly term methods miss.keyed = .ok result middle →
      InferenceCacheFrame key miss.keyed middle ∧ middle.inferOnly = miss.keyed.inferOnly) :
    InferenceCacheFrame key before after ∧ after.inferOnly = before.inferOnly := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  obtain ⟨bodyFrame, bodyPolicy⟩ := uncached middle run
  have keyFrame := PreservesInferenceCache.inferKey key term before
  rw [miss.keyRun] at keyFrame
  have writeRun : RecM.cacheInferResult before.inferOnly miss.key result methods middle =
      .ok () after := by
    rw [cacheInferResult_eq, written]
  have tail := PreservesInferenceCache.write_other different before.inferOnly result methods middle
  rw [writeRun] at tail
  have policy : after.inferOnly = middle.inferOnly := by
    rw [written]
    cases before.inferOnly <;> rfl
  exact ⟨keyFrame.trans (bodyFrame.trans tail),
    policy.trans (bodyPolicy.trans (inferKey_policy miss.keyRun))⟩

/-- Operational support for the successful recursive fragment. Hits write
nothing, including repeated uses of the watched entry. Misses record their
actual key; constant misses use a loaded source or verified standalone lazy
loading, with finite walker resources at the actual post-lookup state.
The lambda domain call is included even though semantic checking can omit its
typing subtree once the declared type's formation has been established. -/
inductive InferenceCacheTrace : Nat → TcState .anon → KExpr .anon → Type
  | hit {fuel before term} (hit : InferenceCacheHit before term) :
      InferenceCacheTrace fuel before term
  | sort {fuel before level info} (miss : UncachedInference before (.sort level info)) :
      InferenceCacheTrace fuel before (.sort level info)
  | fvar {fuel before id name info} (miss : UncachedInference before (.fvar id name info)) :
      InferenceCacheTrace fuel before (.fvar id name info)
  | const {fuel before id arguments info}
      (miss : UncachedInference before (.const id arguments info))
      (concrete : KConst .anon) (loaded : miss.keyed.env.get? id = some concrete)
      (resources : UniverseInstantiationSupport miss.keyed concrete.ty arguments) :
      InferenceCacheTrace fuel before (.const id arguments info)
  | lazyConst {fuel before id arguments info}
      (miss : UncachedInference before (.const id arguments info))
      (loader : StandaloneLazySupport miss.keyed id.addr)
      (resources : ∀ concrete loaded, TcM.getConst id miss.keyed = .ok concrete loaded →
        UniverseInstantiationSupport loaded concrete.ty arguments) :
      InferenceCacheTrace fuel before (.const id arguments info)
  | app {fuel before fn arg info} (full : before.inferOnly = false)
      (miss : UncachedInference before (.app fn arg info))
      (trace : ApplicationInferenceTrace fuel miss.keyed fn arg)
      (hashPath : (trace.argumentType.addr == trace.domain.addr) = true)
      (functionTree : InferenceCacheTrace fuel miss.keyed fn)
      (argumentTree : InferenceCacheTrace fuel trace.functionState arg) :
      InferenceCacheTrace (fuel + 1) before (.app fn arg info)
  | forallE {fuel before name bi domain body info}
      (miss : UncachedInference before (.all name bi domain body info))
      (trace : ForallInferenceTrace fuel miss.keyed name bi domain body)
      (domainTree : InferenceCacheTrace fuel miss.keyed domain)
      (bodyTree : InferenceCacheTrace fuel trace.openedState trace.opened) :
      InferenceCacheTrace (fuel + 1) before (.all name bi domain body info)
  | lam {fuel before name bi domain body info} (full : before.inferOnly = false)
      (miss : UncachedInference before (.lam name bi domain body info))
      (trace : LambdaInferenceTrace fuel miss.keyed name bi domain body)
      (domainTree : InferenceCacheTrace fuel miss.keyed domain)
      (bodyTree : InferenceCacheTrace fuel trace.openedState trace.opened) :
      InferenceCacheTrace (fuel + 1) before (.lam name bi domain body info)

/-- The finite write footprint is computed from the operational tree. Cache
hits contribute no key; recursive calls and each outer insertion are included. -/
def InferenceCacheTrace.writes {fuel : Nat} {before : TcState .anon} {term : KExpr .anon} :
    InferenceCacheTrace fuel before term → List (Address × Address)
  | .hit _ => []
  | .sort miss | .fvar miss | .const miss .. | .lazyConst miss .. => [miss.key]
  | .app _ miss _ _ first second | .forallE miss _ first second | .lam _ miss _ first second =>
      miss.key :: (first.writes ++ second.writes)

/-- Leaf construction inspects the real cache policy; callers need not
provide a separate hit/miss observation for a sort. -/
def InferenceCacheTrace.sortOfKey {fuel : Nat} {before keyed : TcState .anon}
    {level : KUniv .anon} {info : ExprInfo .anon} {key : Address × Address}
    (keyRun : TcM.inferKey (.sort level info) before = .ok key keyed) :
    InferenceCacheTrace fuel before (.sort level info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · exact .hit hit
  · exact .sort miss

def InferenceCacheTrace.fvarOfKey {fuel : Nat} {before keyed : TcState .anon}
    {id : FVarId} {name : Mode.anon.F Name} {info : ExprInfo .anon} {key : Address × Address}
    (keyRun : TcM.inferKey (.fvar id name info) before = .ok key keyed) :
    InferenceCacheTrace fuel before (.fvar id name info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, _⟩
  · exact .hit hit
  · exact .fvar miss

def InferenceCacheTrace.constOfKey {fuel : Nat} {before keyed : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key : Address × Address} {concrete : KConst .anon}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (loaded : keyed.env.get? id = some concrete)
    (resources : UniverseInstantiationSupport keyed concrete.ty arguments) :
    InferenceCacheTrace fuel before (.const id arguments info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
  · exact .hit hit
  · exact .const miss concrete (by simpa only [stateEq] using loaded)
      (by simpa only [stateEq] using resources)

/-- Construct a constant leaf that may load its declaration. Cache selection
comes from the actual maps; walker resources concern the returned lookup state. -/
def InferenceCacheTrace.lazyConstOfKey {fuel : Nat} {before keyed : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key : Address × Address}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (loader : StandaloneLazySupport keyed id.addr)
    (resources : ∀ concrete loaded, TcM.getConst id keyed = .ok concrete loaded →
      UniverseInstantiationSupport loaded concrete.ty arguments) :
    InferenceCacheTrace fuel before (.const id arguments info) := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, _, stateEq⟩
  · exact .hit hit
  · exact .lazyConst miss (by simpa only [stateEq] using loader)
      (by simpa only [stateEq] using resources)

/-- Every successful call in the finite tree preserves entries outside its
computed write footprint and retains the loaded declarations and policy.
The proof follows the recursive calls, then their real outer cache insertion. -/
theorem InferenceCacheTrace.frame {fuel : Nat} {before after : TcState .anon}
    {term result : KExpr .anon} (tree : InferenceCacheTrace fuel before term)
    {key : Address × Address} (outside : key ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceCacheFrame key before after ∧ after.inferOnly = before.inferOnly := by
  induction tree generalizing result after with
  | @hit fuel before term hit =>
      rw [hit.run] at accepted
      cases accepted
      have frame := PreservesInferenceCache.inferKey key term before
      rw [hit.keyRun] at frame
      exact ⟨frame, inferKey_policy hit.keyRun⟩
  | @sort fuel before level info miss =>
      simp only [writes, List.mem_singleton] at outside
      apply infer_miss_frame miss (Ne.symm outside) accepted
      intro middle run
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} =
        .ok result middle at run
      cases run
      exact ⟨(.of_eq rfl rfl rfl), rfl⟩
  | lazyConst miss loader resources =>
      simp only [writes, List.mem_singleton] at outside
      apply infer_miss_frame miss (Ne.symm outside) accepted
      intro middle run
      obtain ⟨concrete, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have lookup := getConst_standalone_cache loader
      rw [got] at lookup
      have resource := resources concrete foundState got
      have post := TcM.instantiateUnivParams_wf resource.faithful
        (fun _ h => Or.inr h) ⟨resource.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact ⟨(lookup.cache key).trans (.of_eq rfl rfl rfl), lookup.policy⟩
  | @fvar fuel before id name info miss =>
      simp only [writes, List.mem_singleton] at outside
      apply infer_miss_frame miss (Ne.symm outside) accepted
      intro middle run
      change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run
        (methodsN fuel) miss.keyed = _ at run
      unfold RecM.inferUncached at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed =
        .ok miss.keyed miss.keyed from rfl] at run
      dsimp only at run
      split at run
      · cases run; exact ⟨.refl key _, rfl⟩
      · contradiction
  | const miss concrete loaded resources =>
      simp only [writes, List.mem_singleton] at outside
      apply infer_miss_frame miss (Ne.symm outside) accepted
      intro middle run
      obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      rw [getConst_loaded loaded] at got
      cases got
      have post := TcM.instantiateUnivParams_wf resources.faithful
        (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact ⟨(.of_eq rfl rfl rfl), rfl⟩
  | app full miss trace hashPath functionTree argumentTree functionIH argumentIH =>
      simp only [writes, List.mem_cons, List.mem_append, not_or] at outside
      apply infer_miss_frame miss (Ne.symm outside.1) accepted
      intro middle run
      rw [full] at run
      obtain ⟨functionFrame, functionPolicy⟩ := functionIH outside.2.1 trace.functionRun
      obtain ⟨argumentFrame, argumentPolicy⟩ := argumentIH outside.2.2 trace.argumentRun
      obtain ⟨comparisonFrame, comparisonPolicy⟩ := isDefEq_hash_frame hashPath trace.compareRun key
      have state := (trace.output_state run).2
      rw [state]
      exact ⟨(functionFrame.trans (argumentFrame.trans comparisonFrame)).trans (.of_eq rfl rfl rfl),
        comparisonPolicy.trans (argumentPolicy.trans functionPolicy)⟩
  | forallE miss trace domainTree bodyTree domainIH bodyIH =>
      simp only [writes, List.mem_cons, List.mem_append, not_or] at outside
      apply infer_miss_frame miss (Ne.symm outside.1) accepted
      intro middle run
      obtain ⟨domainFrame, domainPolicy⟩ := domainIH outside.2.1 trace.domainRun
      obtain ⟨bodyFrame, bodyPolicy⟩ := bodyIH outside.2.2 trace.bodyRun
      have opening := openBinder_frame key trace.openRun
      have state := (trace.output_state run).2
      rw [state]
      exact ⟨(domainFrame.trans (opening.trans bodyFrame)).trans (.of_eq rfl rfl rfl),
        bodyPolicy.trans ((openBinder_policy trace.openRun).trans domainPolicy)⟩
  | lam full miss trace domainTree bodyTree domainIH bodyIH =>
      simp only [writes, List.mem_cons, List.mem_append, not_or] at outside
      apply infer_miss_frame miss (Ne.symm outside.1) accepted
      intro middle run
      rw [full] at run
      obtain ⟨domainFrame, domainPolicy⟩ := domainIH outside.2.1 trace.domainRun
      obtain ⟨bodyFrame, bodyPolicy⟩ := bodyIH outside.2.2 trace.bodyRun
      have opening := openBinder_frame key trace.openRun
      have state := (trace.output_state run).2
      rw [state]
      exact ⟨(domainFrame.trans (opening.trans bodyFrame)).trans (.of_eq rfl rfl rfl),
        bodyPolicy.trans ((openBinder_policy trace.openRun).trans domainPolicy)⟩

/-- A standalone constant call needs no separately constructed operational
tree: the real key and cache selection build its hit or lazy-miss leaf. -/
theorem infer_lazyConst_cache_frame {fuel : Nat} {before keyed after : TcState .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {key watched : Address × Address} {result : KExpr .anon}
    (keyRun : TcM.inferKey (.const id arguments info) before = .ok key keyed)
    (different : key ≠ watched) (loader : StandaloneLazySupport keyed id.addr)
    (resources : ∀ concrete loaded, TcM.getConst id keyed = .ok concrete loaded →
      UniverseInstantiationSupport loaded concrete.ty arguments)
    (accepted : RecM.infer (.const id arguments info) (methodsN fuel) before = .ok result after) :
    InferenceCacheFrame watched before after ∧ after.inferOnly = before.inferOnly := by
  rcases observeInferenceCache keyRun with ⟨hit, _, _⟩ | ⟨miss, keyEq, stateEq⟩
  · exact (InferenceCacheTrace.hit (fuel := fuel) hit).frame (by simp [InferenceCacheTrace.writes]) accepted
  · let tree : InferenceCacheTrace fuel before (.const id arguments info) :=
      .lazyConst miss (by simpa only [stateEq] using loader)
        (by simpa only [stateEq] using resources)
    apply tree.frame _ accepted
    simpa only [tree, InferenceCacheTrace.writes, List.mem_singleton, keyEq] using Ne.symm different

/-- Concrete agreement at an unwritten key is retained by the entire tree. -/
theorem InferenceCacheTrace.agreement {fuel : Nat} {before after : TcState .anon}
    {term result expected : KExpr .anon} (tree : InferenceCacheTrace fuel before term)
    {key : Address × Address} (outside : key ∉ tree.writes)
    (agreement : InferenceCacheAgreement before key expected)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceCacheAgreement after key expected :=
  agreement.frame (tree.frame outside accepted).1

/-- Reconstruct the later selected hit from the earlier closed hit and the
whole recursive call, with no additional cache or policy observation. -/
def InferenceCacheHit.afterInference {fuel : Nat} {before after : TcState .anon}
    {cachedTerm term result : KExpr .anon} (hit : InferenceCacheHit before cachedTerm)
    (closed : cachedTerm.lbr = 0) (tree : InferenceCacheTrace fuel before term)
    (outside : (cachedTerm.addr, emptyCtxAddr) ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    InferenceCacheHit after cachedTerm :=
  hit.transport closed (tree.frame outside accepted).1 (tree.frame outside accepted).2

/-- Carry the admitted declaration, substitution prediction, and selected
constant hit through inference of an entire supported function body. -/
def CachedConstantInferenceSupport.afterInference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {fuel : Nat} {before after : TcState .anon} {term result : KExpr .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (tree : InferenceCacheTrace fuel before term)
    (outside : ((KExpr.const id arguments info).addr, emptyCtxAddr) ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type :=
  support.transport closed (tree.frame outside accepted).1 (tree.frame outside accepted).2

/-- Reuse the complete earlier witness after inference may load another
standalone. The new cache selection and declaration extension are derived. -/
def CachedConstantInferenceSupport.afterLazyInference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {fuel : Nat} {before keyed after : TcState .anon}
    {id requested : KId .anon} {arguments requestedArguments : Array (KUniv .anon)}
    {info requestedInfo : ExprInfo .anon} {key : Address × Address} {result : KExpr .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (keyRun : TcM.inferKey (.const requested requestedArguments requestedInfo) before = .ok key keyed)
    (different : key ≠ ((KExpr.const id arguments info).addr, emptyCtxAddr))
    (loader : StandaloneLazySupport keyed requested.addr)
    (resources : ∀ concrete loaded, TcM.getConst requested keyed = .ok concrete loaded →
      UniverseInstantiationSupport loaded concrete.ty requestedArguments)
    (accepted : RecM.infer (.const requested requestedArguments requestedInfo)
      (methodsN fuel) before = .ok result after) :
    CachedConstantInferenceSupport resolve entries after id arguments info ref entry type :=
  let frame := infer_lazyConst_cache_frame keyRun different loader resources accepted
  support.transport closed frame.1 frame.2

/-- A later constant's actual returned type inherits typing from its earlier
witness after recursive inference; no semantic premise about caches is added. -/
theorem CachedConstantInferenceSupport.sound_after_inference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β}
    {fuel : Nat} {before middle after : TcState .anon} {term result cachedResult : KExpr .anon}
    {id : KId .anon} {arguments : Array (KUniv .anon)} {info : ExprInfo .anon}
    {ref : ConstRef β} {entry : ConstantEntry β} {type : AExpr β} {methods : Methods .anon}
    (support : CachedConstantInferenceSupport resolve entries before id arguments info ref entry type)
    (closed : (KExpr.const id arguments info).lbr = 0)
    (tree : InferenceCacheTrace fuel before term)
    (outside : ((KExpr.const id arguments info).addr, emptyCtxAddr) ∉ tree.writes)
    (inferred : RecM.infer term (methodsN fuel) before = .ok result middle)
    (accepted : RecM.infer (.const id arguments info) methods middle = .ok cachedResult after) :
    readScopedExpr? resolve locals cachedResult = some type.erase ∧
      TypingClaim.{u,v} entries context (.const ref (arguments.toList.map readLevel)) type :=
  (support.afterInference closed tree outside inferred).sound accepted

/-- Construct a later sort leaf using agreement preserved by a whole
recursive call, deriving its current key and cache selection automatically. -/
def BinderInference.sortAfterInference {β : Type u}
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {locals : List FVarId} {context : Model.Context β} {fuel nextFuel : Nat}
    {before after : TcState .anon} {term result : KExpr .anon}
    {level : KUniv .anon} {info : ExprInfo .anon}
    (closed : (KExpr.sort level info).lbr = 0)
    (agreement : InferenceCacheAgreement before ((KExpr.sort level info).addr, emptyCtxAddr)
      (KExpr.mkSort (KUniv.mkSucc level)))
    (tree : InferenceCacheTrace fuel before term)
    (outside : ((KExpr.sort level info).addr, emptyCtxAddr) ∉ tree.writes)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after)
    (coherent : after.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun candidate => after.env.intern.ExprSupport candidate ∨
      candidate = KExpr.mkSort (KUniv.mkSucc level)) :
    BinderInference resolve entries locals context nextFuel after (.sort level info)
      (.sort (readLevel level)) (.sort (.succ (readLevel level))) :=
  .sortOfAgreement closed (tree.agreement outside agreement accepted) coherent faithful

end Ix.Kernel.Consistency
