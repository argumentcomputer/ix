/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaReannotation

/-! Retained cache provenance is independent of a later source annotation.
Each entry stores an actual producing call and its initial intern coherence. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

structure BetaHeadCacheOrigin {β : Type u} (source result : KExpr .anon) where
  resolve : Address → Option (ConstRef β)
  locals : List FVarId
  fuel : Nat
  flags : WhnfFlags
  before : TcState .anon
  after : TcState .anon
  term : AExpr β
  target : AExpr β
  call : BetaHeadReduction resolve locals fuel flags before source term after result target
  coherent : before.env.intern.WF

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}

namespace BetaHeadReduction

def origin {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (coherent : before.env.intern.WF) : BetaHeadCacheOrigin (β := β) source result :=
  ⟨resolve, locals, fuel, flags, before, after, term, target, call, coherent⟩

theorem published {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target) :
    BetaCoreCache.lookup flags (betaWhnfKey source after).1 (betaWhnfKey source after).2 = some result := by
  simp only [call.frame.keys source, BetaCoreCache.lookup, betaWhnfKey_environment]
  cases call with
  | reduce path moving enough miss =>
      simpa only [BetaCoreCache.lookup] using BetaCoreCache.published flags _ result _
  | cached origin coherent hit =>
      simpa only [BetaCoreCache.lookup, betaWhnfKey_environment] using hit

def replay {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (coherent : before.env.intern.WF) :
    BetaHeadReduction resolve locals 0 flags after source term (betaWhnfKey source after).2 result target :=
  .cached call coherent call.published

theorem replay_run {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (coherent : before.env.intern.WF) :
    (RecM.whnfCoreWithFlags source flags).run (methodsN 0) after =
      .ok result (betaWhnfKey source after).2 := (call.replay coherent).run

end BetaHeadReduction

/-- The present source reading rebuilds all annotations in the retained
producer. The observed lookup selects the result and current cache partition. -/
def BetaHeadCacheOrigin.replay {γ : Type v} {source result : KExpr .anon}
    (origin : BetaHeadCacheOrigin (β := γ) source result)
    {fuel : Nat} {flags : WhnfFlags} {before : TcState .anon} {current : AExpr β}
    (reading : readScopedExpr? resolve locals source = some current.erase)
    (hit : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = some result) :
    Σ target, BetaHeadReduction resolve locals fuel flags before source current (betaWhnfKey source before).2 result target :=
  let rebuilt := origin.call.reannotate reading origin.coherent
  ⟨rebuilt.1, .cached rebuilt.2 origin.coherent hit⟩

namespace BetaWhnfSource

def HeadOrigins {β : Type u} (flags : WhnfFlags) (before : TcState .anon) (source : KExpr .anon) : Prop :=
  ∀ cached, BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = some cached →
    Nonempty (BetaHeadCacheOrigin (β := β) source cached)

theorem HeadOrigins.absent {flags : WhnfFlags} {before : TcState .anon} {source : KExpr .anon}
    (miss : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none) :
    HeadOrigins (β := β) flags before source := by
  intro cached found
  rw [miss] at found
  cases found

theorem HeadOrigins.ofCall {fuel : Nat} {flags : WhnfFlags} {before after : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (call : BetaHeadReduction resolve locals fuel flags before source term after result target)
    (coherent : before.env.intern.WF) : HeadOrigins (β := β) flags after source := by
  intro cached found
  rw [call.published] at found
  cases Option.some.inj found
  exact ⟨call.origin coherent⟩

/-- Choice only selects a retained producing execution. Its fresh annotation
and replay trace are then constructed by the raw reannotation theorem. -/
noncomputable def HeadOrigins.replay {flags : WhnfFlags} {before : TcState .anon}
    {source result : KExpr .anon} (origins : HeadOrigins (β := β) flags before source)
    {fuel : Nat} {current : AExpr β}
    (reading : readScopedExpr? resolve locals source = some current.erase)
    (hit : BetaCoreCache.lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = some result) :
    Σ target, BetaHeadReduction resolve locals fuel flags before source current (betaWhnfKey source before).2 result target :=
  (Classical.choice (origins result hit)).replay reading hit

end BetaWhnfSource

end Ix.Kernel.Consistency
