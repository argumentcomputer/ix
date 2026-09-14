/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisInference
import Ix.Kernel.Verify.Consistency.RecursiveCache

/-!
Reuse the actual check behind a full inference-cache entry. The successful
call supplies the stored result, its reading follows from that check, and a
proved frame preserves the entry. The retained tree still supplies lambda
domains, dependent codomain checks, and subsequent beta derivations.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v w

/-- A completed full check supplies a later synthesis cache node. Neither
cache selection nor the cached type's semantics is a new premise. The key
runs keep context-sensitive key computation explicit. -/
def SynthesisInference.reuseFull {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel nextFuel : Nat}
    {before keyed after current currentKeyed : TcState .anon} {key : Address × Address}
    {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (full : before.inferOnly = false)
    (keyRun : TcM.inferKey source before = .ok key keyed)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (frame : InferenceCacheFrame key after current)
    (currentKeyRun : TcM.inferKey source current = .ok key currentKeyed) :
    SynthesisInference resolve entries locals context bounds nextFuel current source term type level :=
  .cached tree agreement reading accepted
    (InferenceCacheHit.fromFullRun full keyRun accepted frame currentKeyRun) rfl
    (tree.sound formed agreement reading accepted).1

/-- When the raw source has no loose variables, both keys are computed from
its address. Registered free variables may still occur in the source. -/
def SynthesisInference.reuseFullClosed {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel nextFuel : Nat} {before after current : TcState .anon}
    {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (full : before.inferOnly = false) (closed : source.lbr = 0)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (frame : InferenceCacheFrame (source.addr, emptyCtxAddr) after current) :
    SynthesisInference resolve entries locals context bounds nextFuel current source term type level :=
  tree.reuseFull formed agreement reading full (inferKey_closed closed before) accepted frame
    (inferKey_closed closed current)

/-- The preserved full entry executes immediately, at any method-table fuel
and under either current checking policy. -/
theorem infer_full_replay_closed {source result : KExpr .anon}
    {methods currentMethods : Methods .anon} {before after current : TcState .anon}
    (full : before.inferOnly = false) (closed : source.lbr = 0)
    (accepted : RecM.infer source methods before = .ok result after)
    (frame : InferenceCacheFrame (source.addr, emptyCtxAddr) after current) :
    RecM.infer source currentMethods current = .ok result current :=
  (InferenceCacheHit.fromFullRun full (inferKey_closed closed before) accepted frame
    (inferKey_closed closed current)).run currentMethods

/-- Intervening recursive inference computes its write footprint and the
required frame. Public beta Pi exposure and changed cheap-beta lambda bodies
are included in this operational trace. -/
def SynthesisInference.reuseFullAcross {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel nextFuel otherFuel : Nat}
    {before after current : TcState .anon} {source result other otherResult : KExpr .anon}
    {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (formed : ContextFormation.{u,v} entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (full : before.inferOnly = false) (closed : source.lbr = 0)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after)
    (intervening : InferenceCacheTrace.{w} otherFuel after other)
    (outside : (source.addr, emptyCtxAddr) ∉ intervening.writes)
    (otherRun : RecM.infer other (methodsN otherFuel) after = .ok otherResult current) :
    SynthesisInference resolve entries locals context bounds nextFuel current source term type level :=
  tree.reuseFullClosed formed agreement reading full closed accepted (intervening.frame outside otherRun).1

/-- The concrete full-cache entry and its actual checking provenance.
An empty anchor context lets the retained tree cross later interfaces and
local scopes without assuming semantic agreement for the cached answer. -/
structure CachedSynthesisCheck {β : Type u} (resolve : Address → Option (ConstRef β))
    (anchor entries : Model.Environment β) (locals : List FVarId) (context : Model.Context β)
    (state : TcState .anon) (source : KExpr .anon) (term type : AExpr β) (level : VLevel) where
  result : KExpr .anon
  closed : source.lbr = 0
  sourceReading : readScopedExpr? resolve locals source = some term.erase
  resultReading : readScopedExpr? resolve locals result = some type.erase
  check : SynthesisRetainedCheck resolve anchor [] [] entries context term type level
  stored : state.env.inferCache[(source.addr, emptyCtxAddr)]? = some result

/-- Full inference supplies the stored result and its reading. The anchor's
context is constructed from the executed domain checks of the source tree. -/
def CachedSynthesisCheck.ofFull {β : Type u} {resolve : Address → Option (ConstRef β)}
    {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
    {bounds : List VLevel} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries locals context bounds fuel before source term type level)
    (contextOrigin : SynthesisContext resolve anchor [] [] entries context bounds)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (full : before.inferOnly = false) (closed : source.lbr = 0)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    CachedSynthesisCheck resolve anchor entries locals context after source term type level :=
  ⟨result, closed, reading,
    (tree.soundWithSpine.{u,u} (contextOrigin.sound (ContextFormation.empty anchor)) agreement reading accepted).1,
    .source contextOrigin tree agreement reading accepted,
    infer_full_success_cache full (inferKey_closed closed before) accepted⟩

/-- Closed declaration calls establish an anchor directly. -/
def CachedSynthesisCheck.ofClosedFull {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term type : AExpr β} {level : VLevel}
    (tree : SynthesisInference resolve entries [] [] [] fuel before source term type level)
    (reading : readScopedExpr? resolve [] source = some term.erase)
    (full : before.inferOnly = false) (closed : source.lbr = 0)
    (accepted : RecM.infer source (methodsN fuel) before = .ok result after) :
    CachedSynthesisCheck resolve entries entries [] [] after source term type level :=
  .ofFull tree .current (.empty _ _) reading full closed accepted

namespace CachedSynthesisCheck

variable {β : Type u} {resolve : Address → Option (ConstRef β)}
  {anchor entries : Model.Environment β} {locals : List FVarId} {context : Model.Context β}
  {state : TcState .anon} {source : KExpr .anon} {term type : AExpr β} {level : VLevel}

/-- A proved operational frame preserves the physical result at its key. -/
def frame (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    {after : TcState .anon} (preserved : InferenceCacheFrame (source.addr, emptyCtxAddr) state after) :
    CachedSynthesisCheck resolve anchor entries locals context after source term type level :=
  { cached with stored := preserved.full.trans cached.stored }

/-- Declaration growth transports all retained source, domain, and body
checks while preserving the concrete cache entry and source readings. -/
def extend (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    {later : Model.Environment β} (extension : InterfaceExtends entries later) :
    CachedSynthesisCheck resolve anchor later locals context state source term type level :=
  { cached with check := cached.check.extend extension }

/-- A fresh local shifts the annotation of every captured variable. The
same raw source and result remain readable, including beneath binders. -/
def weaken (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    {fresh : FVarId} (absent : fresh ∉ locals) (domain : AExpr β) :
    CachedSynthesisCheck resolve anchor entries (fresh :: locals) (context.push domain) state source
      (term.liftN 1) (type.liftN 1) level :=
  { cached with
    sourceReading := by simpa only [AExpr.erase_liftN] using readScopedExpr?_push absent cached.sourceReading
    resultReading := by simpa only [AExpr.erase_liftN] using readScopedExpr?_push absent cached.resultReading
    check := cached.check.weakenAt (.root context domain) }

/-- Actual binder opening supplies the frame; the fresh identifier supplies
the reader transport. The caller's domain inference still supplies context
formation when this resource is used by a synthesis tree. -/
def afterOpenBinder (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {rawDomain rawBody opened : KExpr .anon} {fresh : FVarId} {after : TcState .anon}
    (domain : AExpr β) (absent : fresh ∉ locals)
    (accepted : TcM.openBinder name bi rawDomain rawBody state = .ok (opened, fresh) after) :
    CachedSynthesisCheck resolve anchor entries (fresh :: locals) (context.push domain) after source
      (term.liftN 1) (type.liftN 1) level := by
  have preserved := PreservesInferenceCache.openBinder (source.addr, emptyCtxAddr) name bi rawDomain rawBody state
  rw [accepted] at preserved
  exact (cached.frame preserved).weaken absent domain

/-- Recursive inference derives its own write footprint and frame, including
lazy loading, beta Pi exposure, and changed cheap-beta lambda bodies. -/
def afterInference (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    {fuel : Nat} {other result : KExpr .anon} {after : TcState .anon}
    (trace : InferenceCacheTrace.{w} fuel state other)
    (outside : (source.addr, emptyCtxAddr) ∉ trace.writes)
    (accepted : RecM.infer other (methodsN fuel) state = .ok result after) :
    CachedSynthesisCheck resolve anchor entries locals context after source term type level :=
  cached.frame (trace.frame outside accepted).1

/-- Selection follows from the retained full entry under either policy.
No new observation or agreement premise is supplied at reuse. -/
def hit (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level) :
    InferenceCacheHit state source :=
  ⟨(source.addr, emptyCtxAddr), state, cached.result, inferKey_closed cached.closed state, .inl cached.stored⟩

/-- Materialize the cache branch of the original synthesis recursion.
The stored check can already contain transported cache hits of its own. -/
def support (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    (bounds : List VLevel) (fuel : Nat) :
    SynthesisInference resolve entries locals context bounds fuel state source term type level :=
  .cachedFrom (.rebase (.empty anchor) cached.check) cached.hit cached.resultReading

theorem run (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level)
    (methods : Methods .anon) : RecM.infer source methods state = .ok cached.result state :=
  cached.hit.run methods

/-- Replay is typed from its retained execution, even after the interface
and annotated context have changed. -/
theorem sound (cached : CachedSynthesisCheck resolve anchor entries locals context state source term type level) :
    TypingClaim.{u,v} entries context term type ∧
      TypingClaim.{u,v} entries context type (.sort level) ∧
      LambdaSpineTyping.{u,v} entries context term type :=
  cached.check.soundWithSpine (.empty anchor)

end CachedSynthesisCheck

end Ix.Kernel.Consistency
