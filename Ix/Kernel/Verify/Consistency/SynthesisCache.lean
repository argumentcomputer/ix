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

end Ix.Kernel.Consistency
