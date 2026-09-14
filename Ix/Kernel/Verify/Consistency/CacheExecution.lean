/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.RecursiveCache

/-! The exact inference-cache writes of a supported recursive execution.
Every event retains the call that produced its stored result. Folding the
events reconstructs both complete maps, including newly written keys. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

/-- One actual miss and its successful call, whose final operation publishes
this result under the policy captured at entry. -/
structure InferenceCacheEvent where
  fuel : Nat
  before : TcState .anon
  after : TcState .anon
  source : KExpr .anon
  result : KExpr .anon
  miss : UncachedInference before source
  accepted : RecM.infer source (methodsN fuel) before = .ok result after

namespace InferenceCacheEvent

abbrev CacheMap := Std.HashMap (Address × Address) (KExpr .anon)

def ofRun {fuel : Nat} {before after : TcState .anon} {source result : KExpr .anon}
    (miss : UncachedInference before source)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) : InferenceCacheEvent :=
  ⟨fuel, before, after, source, result, miss, accepted⟩

def fullStep (event : InferenceCacheEvent) (cache : CacheMap) : CacheMap :=
  if event.before.inferOnly then cache else cache.insert event.miss.key event.result

def onlyStep (event : InferenceCacheEvent) (cache : CacheMap) : CacheMap :=
  if event.before.inferOnly then cache.insert event.miss.key event.result else cache

def applyFull (events : List InferenceCacheEvent) (cache : CacheMap) : CacheMap :=
  events.foldl (fun cache event => event.fullStep cache) cache

def applyOnly (events : List InferenceCacheEvent) (cache : CacheMap) : CacheMap :=
  events.foldl (fun cache event => event.onlyStep cache) cache

@[simp] theorem applyFull_nil (cache : CacheMap) : applyFull [] cache = cache := rfl
@[simp] theorem applyOnly_nil (cache : CacheMap) : applyOnly [] cache = cache := rfl

theorem applyFull_append (first second : List InferenceCacheEvent) (cache : CacheMap) :
    applyFull (first ++ second) cache = applyFull second (applyFull first cache) :=
  List.foldl_append

theorem applyOnly_append (first second : List InferenceCacheEvent) (cache : CacheMap) :
    applyOnly (first ++ second) cache = applyOnly second (applyOnly first cache) :=
  List.foldl_append

/-- A present value was already present or was published by a recorded full
check. Repeated writes are allowed and the result is the selected value. -/
theorem applyFull_origin (events : List InferenceCacheEvent) (cache : CacheMap)
    {key : Address × Address} {result : KExpr .anon}
    (stored : (applyFull events cache)[key]? = some result) :
    cache[key]? = some result ∨ ∃ event ∈ events,
      event.before.inferOnly = false ∧ event.miss.key = key ∧ event.result = result := by
  induction events generalizing cache with
  | nil => exact .inl stored
  | cons event events ih =>
      rcases ih (event.fullStep cache) stored with old | ⟨written, member, policy, same, value⟩
      · unfold fullStep at old
        split at old
        · exact .inl old
        · rename_i full
          by_cases same : event.miss.key = key
          · rw [same, Std.HashMap.getElem?_insert_self] at old
            exact .inr ⟨event, .head _, Bool.eq_false_iff.mpr full, same, Option.some.inj old⟩
          · exact .inl (by simpa [Std.HashMap.getElem?_insert, same] using old)
      · exact .inr ⟨written, .tail _ member, policy, same, value⟩

theorem applyOnly_origin (events : List InferenceCacheEvent) (cache : CacheMap)
    {key : Address × Address} {result : KExpr .anon}
    (stored : (applyOnly events cache)[key]? = some result) :
    cache[key]? = some result ∨ ∃ event ∈ events,
      event.before.inferOnly = true ∧ event.miss.key = key ∧ event.result = result := by
  induction events generalizing cache with
  | nil => exact .inl stored
  | cons event events ih =>
      rcases ih (event.onlyStep cache) stored with old | ⟨written, member, policy, same, value⟩
      · unfold onlyStep at old
        split at old
        · rename_i policy
          by_cases same : event.miss.key = key
          · rw [same, Std.HashMap.getElem?_insert_self] at old
            exact .inr ⟨event, .head _, policy, same, Option.some.inj old⟩
          · exact .inl (by simpa [Std.HashMap.getElem?_insert, same] using old)
        · exact .inl old
      · exact .inr ⟨written, .tail _ member, policy, same, value⟩

end InferenceCacheEvent

/-- Child calls precede their parent's final publication. Hits contribute
no events; lazy loading and beta exposure preserve both inference maps. -/
def InferenceCacheTrace.events {fuel : Nat} {before after : TcState .anon}
    {term result : KExpr .anon} (tree : InferenceCacheTrace.{u} fuel before term)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) : List InferenceCacheEvent :=
  match tree with
  | .hit _ => []
  | .sort miss | .fvar miss | .const miss .. | .lazyConst miss .. => [.ofRun miss accepted]
  | .app _ miss trace _ functionTree argumentTree =>
      functionTree.events trace.functionRun ++ argumentTree.events trace.argumentRun ++ [.ofRun miss accepted]
  | .appBeta _ miss trace _ _ functionTree argumentTree =>
      functionTree.events trace.functionRun ++ argumentTree.events trace.argumentRun ++ [.ofRun miss accepted]
  | .forallE miss trace domainTree bodyTree =>
      domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
  | .lam _ miss trace domainTree bodyTree =>
      domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
  | .lamBody _ miss trace domainTree bodyTree =>
      domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
  | .letE _ miss trace _ domainTree valueTree bodyTree =>
      domainTree.events trace.domainRun ++ valueTree.events trace.valueRun ++
        bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
  | .forallSort miss trace _ _ domainTree bodyTree =>
      domainTree.events trace.domainCheck.inferRun ++ bodyTree.events trace.bodyCheck.inferRun ++ [.ofRun miss accepted]
  | .lamSort _ miss trace _ domainTree bodyTree =>
      domainTree.events trace.domainCheck.inferRun ++ bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
  | .letSort _ miss trace _ _ domainTree valueTree bodyTree =>
      domainTree.events trace.domainCheck.inferRun ++ valueTree.events trace.valueRun ++
        bodyTree.events trace.bodyRun ++ [.ofRun miss accepted]
termination_by structural tree

/-- Actual child publications, before the enclosing miss writes its result. -/
def InferenceCacheTrace.childEvents {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} :
    InferenceCacheTrace.{u} fuel before source → List InferenceCacheEvent
  | .hit _ | .sort _ | .fvar _ | .const .. | .lazyConst .. => []
  | .app _ _ trace _ first second => first.events trace.functionRun ++ second.events trace.argumentRun
  | .appBeta _ _ trace _ _ first second => first.events trace.functionRun ++ second.events trace.argumentRun
  | .forallE _ trace first second => first.events trace.domainRun ++ second.events trace.bodyRun
  | .lam _ _ trace first second => first.events trace.domainRun ++ second.events trace.bodyRun
  | .lamBody _ _ trace first second => first.events trace.domainRun ++ second.events trace.bodyRun
  | .letE _ _ trace _ first second third =>
      first.events trace.domainRun ++ second.events trace.valueRun ++ third.events trace.bodyRun
  | .forallSort _ trace _ _ first second => first.events trace.domainCheck.inferRun ++ second.events trace.bodyCheck.inferRun
  | .lamSort _ _ trace _ first second => first.events trace.domainCheck.inferRun ++ second.events trace.bodyRun
  | .letSort _ _ trace _ _ first second third =>
      first.events trace.domainCheck.inferRun ++ second.events trace.valueRun ++ third.events trace.bodyRun

private theorem openBinder_maps {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {domain body opened : KExpr .anon} {fresh : FVarId} {before after : TcState .anon}
    (accepted : TcM.openBinder name bi domain body before = .ok (opened, fresh) after) :
    after.env.inferCache = before.env.inferCache ∧ after.env.inferOnlyCache = before.env.inferOnlyCache := by
  rw [openBinder_eq] at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl⟩
  · contradiction

private theorem hash_maps {left right : KExpr .anon} {methods : Methods .anon}
    {before after : TcState .anon} (equal : (left.addr == right.addr) = true)
    (accepted : RecM.isDefEq left right methods before = .ok true after) :
    after.env.inferCache = before.env.inferCache ∧ after.env.inferOnlyCache = before.env.inferOnlyCache := by
  rw [isDefEq_hash_state equal] at accepted
  split at accepted <;> cases accepted <;> exact ⟨rfl, rfl⟩

private theorem miss_maps {fuel : Nat} {before after : TcState .anon} {term result : KExpr .anon}
    (miss : UncachedInference before term)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after)
    (priorEvents : List InferenceCacheEvent)
    (effects : ∀ middle,
      RecM.inferUncached RecM.inferCall before.inferOnly term (methodsN fuel) miss.keyed = .ok result middle →
      middle.env.inferCache = InferenceCacheEvent.applyFull priorEvents miss.keyed.env.inferCache ∧
        middle.env.inferOnlyCache = InferenceCacheEvent.applyOnly priorEvents miss.keyed.env.inferOnlyCache) :
    after.env.inferCache = InferenceCacheEvent.applyFull (priorEvents ++ [.ofRun miss accepted]) before.env.inferCache ∧
      after.env.inferOnlyCache = InferenceCacheEvent.applyOnly (priorEvents ++ [.ofRun miss accepted])
        before.env.inferOnlyCache := by
  obtain ⟨middle, run, written⟩ := infer_uncached_success_state miss accepted
  obtain ⟨full, only⟩ := effects middle run
  rw [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
  change after.env.inferCache = (if before.inferOnly then
      InferenceCacheEvent.applyFull priorEvents before.env.inferCache else
      (InferenceCacheEvent.applyFull priorEvents before.env.inferCache).insert miss.key result) ∧
    after.env.inferOnlyCache = (if before.inferOnly then
      (InferenceCacheEvent.applyOnly priorEvents before.env.inferOnlyCache).insert miss.key result else
      InferenceCacheEvent.applyOnly priorEvents before.env.inferOnlyCache)
  rw [written]
  rw [inferKey_environment miss.keyRun] at full only
  cases before.inferOnly <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> first | rw [full] | rw [only]

/-- The complete maps are exactly the fold of executed writes. No catalog,
watched-key exclusion, cache agreement, or collision premise is supplied. -/
theorem InferenceCacheTrace.cache_maps {fuel : Nat} {before after : TcState .anon}
    {term result : KExpr .anon} (tree : InferenceCacheTrace.{u} fuel before term)
    (accepted : RecM.infer term (methodsN fuel) before = .ok result after) :
    after.env.inferCache = InferenceCacheEvent.applyFull (tree.events accepted) before.env.inferCache ∧
      after.env.inferOnlyCache = InferenceCacheEvent.applyOnly (tree.events accepted) before.env.inferOnlyCache := by
  induction tree generalizing result after with
  | hit hit =>
      rw [hit.run] at accepted
      cases accepted
      simp only [events, InferenceCacheEvent.applyFull_nil, InferenceCacheEvent.applyOnly_nil,
        inferKey_environment hit.keyRun, and_self]
  | @sort fuel before level info miss =>
      apply miss_maps miss accepted []
      intro middle run
      change EStateM.Result.ok
        (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
        {miss.keyed with env := {miss.keyed.env with intern :=
          (miss.keyed.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2}} = .ok result middle at run
      cases run
      exact ⟨rfl, rfl⟩
  | @fvar fuel before id name info miss =>
      apply miss_maps miss accepted []
      intro middle run
      change (RecM.inferUncached RecM.inferCall before.inferOnly (.fvar id name info)).run (methodsN fuel) miss.keyed = _ at run
      unfold RecM.inferUncached at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ miss.keyed = _ at run
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) miss.keyed = .ok miss.keyed miss.keyed from rfl] at run
      dsimp only at run
      split at run
      · cases run
        exact ⟨rfl, rfl⟩
      · contradiction
  | const miss concrete loaded resources =>
      apply miss_maps miss accepted []
      intro middle run
      obtain ⟨actual, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      rw [getConst_loaded loaded] at got
      cases got
      have post := TcM.instantiateUnivParams_wf resources.faithful
        (fun _ h => Or.inr h) ⟨resources.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact ⟨rfl, rfl⟩
  | lazyConst miss loader resources =>
      apply miss_maps miss accepted []
      intro middle run
      obtain ⟨concrete, foundState, got, _, instantiated⟩ := inferUncached_const_instantiation run
      have lookup := getConst_verified_cache loader
      rw [got] at lookup
      have resource := resources concrete foundState got
      have post := TcM.instantiateUnivParams_wf resource.faithful
        (fun _ h => Or.inr h) ⟨resource.coherent, fun _ h => Or.inl h⟩
      rw [instantiated] at post
      rw [post.2.2.1]
      exact ⟨lookup.environment.full, lookup.environment.only⟩
  | app full miss trace hashPath functionTree argumentTree functionIH argumentIH =>
      apply miss_maps miss accepted (functionTree.events trace.functionRun ++ argumentTree.events trace.argumentRun)
      intro middle run
      rw [full] at run
      obtain ⟨functionFull, functionOnly⟩ := functionIH trace.functionRun
      obtain ⟨argumentFull, argumentOnly⟩ := argumentIH trace.argumentRun
      obtain ⟨comparisonFull, comparisonOnly⟩ := hash_maps hashPath trace.compareRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨comparisonFull.trans (argumentFull.trans (congrArg _ functionFull)),
        comparisonOnly.trans (argumentOnly.trans (congrArg _ functionOnly))⟩
  | appBeta full miss trace exposure hashPath functionTree argumentTree functionIH argumentIH =>
      apply miss_maps miss accepted (functionTree.events trace.functionRun ++ argumentTree.events trace.argumentRun)
      intro middle run
      rw [full] at run
      obtain ⟨functionFull, functionOnly⟩ := functionIH trace.functionRun
      obtain ⟨argumentFull, argumentOnly⟩ := argumentIH trace.argumentRun
      obtain ⟨comparisonFull, comparisonOnly⟩ := hash_maps hashPath trace.compareRun
      have exposureMaps := exposure.inference_maps
      rw [← trace.exposure_state exposure] at exposureMaps
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨comparisonFull.trans (argumentFull.trans (congrArg _ (exposureMaps.1.trans functionFull))),
        comparisonOnly.trans (argumentOnly.trans (congrArg _ (exposureMaps.2.trans functionOnly)))⟩
  | forallE miss trace domainTree bodyTree domainIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun)
      intro middle run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨openedFull, openedOnly⟩ := openBinder_maps trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (openedFull.trans domainFull)),
        bodyOnly.trans (congrArg _ (openedOnly.trans domainOnly))⟩
  | lam full miss trace domainTree bodyTree domainIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun)
      intro middle run
      rw [full] at run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨openedFull, openedOnly⟩ := openBinder_maps trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (openedFull.trans domainFull)),
        bodyOnly.trans (congrArg _ (openedOnly.trans domainOnly))⟩
  | lamBody full miss trace domainTree bodyTree domainIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainRun ++ bodyTree.events trace.bodyRun)
      intro middle run
      rw [full] at run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨openedFull, openedOnly⟩ := openBinder_maps trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (openedFull.trans domainFull)),
        bodyOnly.trans (congrArg _ (openedOnly.trans domainOnly))⟩
  | letE full miss trace hashPath domainTree valueTree bodyTree domainIH valueIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainRun ++ valueTree.events trace.valueRun ++
        bodyTree.events trace.bodyRun)
      intro middle run
      rw [full] at run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainRun
      obtain ⟨valueFull, valueOnly⟩ := valueIH trace.valueRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨comparisonFull, comparisonOnly⟩ := hash_maps hashPath trace.compareRun
      have opened := openLet_inference_state trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (opened.1.trans
          (comparisonFull.trans (valueFull.trans (congrArg _ domainFull))))),
        bodyOnly.trans (congrArg _ (opened.2.1.trans
          (comparisonOnly.trans (valueOnly.trans (congrArg _ domainOnly)))))⟩
  | forallSort miss trace domainExposure bodyExposure domainTree bodyTree domainIH bodyIH =>
      apply miss_maps miss accepted
        (domainTree.events trace.domainCheck.inferRun ++ bodyTree.events trace.bodyCheck.inferRun)
      intro middle run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainCheck.inferRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyCheck.inferRun
      obtain ⟨domainExposedFull, domainExposedOnly⟩ := trace.domainCheck.exposure_maps domainExposure
      obtain ⟨bodyExposedFull, bodyExposedOnly⟩ := trace.bodyCheck.exposure_maps bodyExposure
      obtain ⟨openedFull, openedOnly⟩ := openBinder_maps trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyExposedFull.trans (bodyFull.trans (congrArg _ (openedFull.trans (domainExposedFull.trans domainFull)))),
        bodyExposedOnly.trans (bodyOnly.trans (congrArg _ (openedOnly.trans (domainExposedOnly.trans domainOnly))))⟩
  | lamSort full miss trace domainExposure domainTree bodyTree domainIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainCheck.inferRun ++ bodyTree.events trace.bodyRun)
      intro middle run
      rw [full] at run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainCheck.inferRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨domainExposedFull, domainExposedOnly⟩ := trace.domainCheck.exposure_maps domainExposure
      obtain ⟨openedFull, openedOnly⟩ := openBinder_maps trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (openedFull.trans (domainExposedFull.trans domainFull))),
        bodyOnly.trans (congrArg _ (openedOnly.trans (domainExposedOnly.trans domainOnly)))⟩
  | letSort full miss trace domainExposure hashPath domainTree valueTree bodyTree domainIH valueIH bodyIH =>
      apply miss_maps miss accepted (domainTree.events trace.domainCheck.inferRun ++ valueTree.events trace.valueRun ++
        bodyTree.events trace.bodyRun)
      intro middle run
      rw [full] at run
      obtain ⟨domainFull, domainOnly⟩ := domainIH trace.domainCheck.inferRun
      obtain ⟨valueFull, valueOnly⟩ := valueIH trace.valueRun
      obtain ⟨bodyFull, bodyOnly⟩ := bodyIH trace.bodyRun
      obtain ⟨domainExposedFull, domainExposedOnly⟩ := trace.domainCheck.exposure_maps domainExposure
      obtain ⟨comparisonFull, comparisonOnly⟩ := hash_maps hashPath trace.compareRun
      have opened := openLet_inference_state trace.openRun
      rw [(trace.output_state run).2]
      simp only [InferenceCacheEvent.applyFull_append, InferenceCacheEvent.applyOnly_append]
      exact ⟨bodyFull.trans (congrArg _ (opened.1.trans
          (comparisonFull.trans (valueFull.trans (congrArg _ (domainExposedFull.trans domainFull)))))),
        bodyOnly.trans (congrArg _ (opened.2.1.trans
          (comparisonOnly.trans (valueOnly.trans (congrArg _ (domainExposedOnly.trans domainOnly))))))⟩

end Ix.Kernel.Consistency
