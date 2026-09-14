/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheExecution

/-! Pi and sort exposure follow public beta WHNF, including retained
reduction origins at each cache layer. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

/-- Pi exposure retains raw beta execution through public WHNF and its three
cache layers. Only an outer miss consumes shared fuel. -/
inductive BetaPiExposure {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (fuel : Nat) (before : TcState .anon)
    (source : KExpr .anon) (term : AExpr β) (condition : Certified.PropWhen) (domain body : AExpr β)
    (rawDomain rawBody : KExpr .anon) : Type u
  | reduce {name bi info}
      (plan : BetaPublicWhnfPlan resolve locals fuel before source term
        (.all name bi rawDomain rawBody info) (.forallE condition domain body)) :
      BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody
  | execute {name bi info}
      (execution : BetaPublicExecution resolve locals fuel before source term
        (.all name bi rawDomain rawBody info) (.forallE condition domain body)) :
      BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody
  | cached {originFuel originBefore name bi info}
      (origin : BetaPublicWhnfPlan resolve locals originFuel originBefore source term
        (.all name bi rawDomain rawBody info) (.forallE condition domain body))
      (coherent : originBefore.env.intern.WF)
      (hit : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
        (BetaPublicWhnf.outerKey source before).1]? = some (.all name bi rawDomain rawBody info)) :
      BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody

namespace BetaPiExposure

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source rawDomain rawBody : KExpr .anon}
  {term domain body : AExpr β} {condition : Certified.PropWhen}

def after (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    TcState .anon :=
  match exposure with
  | .reduce plan => plan.after
  | .cached .. => (BetaPublicWhnf.outerKey source before).2
  | .execute execution => execution.after

theorem run (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    (RecM.ensureForallDirect source).run (methodsN (fuel + 1)) before =
      .ok (rawDomain, rawBody) exposure.after := by
  cases exposure with
  | reduce plan =>
      have first := plan.path.first plan.moving
      have entry : RecM.ensureForallDirect source = RecM.ensureForallWhnf source := by
        rw [first.sourceEq]; rfl
      rw [entry, RecM.ensureForallWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, plan.run]
      rfl
  | cached origin _ hit =>
      have first := origin.path.first origin.moving
      have entry : RecM.ensureForallDirect source = RecM.ensureForallWhnf source := by
        rw [first.sourceEq]; rfl
      rw [entry, RecM.ensureForallWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, origin.cache_hit _ _ hit]
      rfl
  | execute execution =>
      have entry : RecM.ensureForallDirect source = RecM.ensureForallWhnf source := by
        rw [execution.first.2.sourceEq]; rfl
      rw [entry, RecM.ensureForallWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, execution.run]
      rfl

theorem reading (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals rawDomain = some domain.erase ∧
      readScopedExpr? resolve locals rawBody 1 = some body.erase ∧ exposure.after.env.intern.WF := by
  cases exposure with
  | reduce plan =>
      obtain ⟨reads, preserved⟩ := plan.reading sourceReading coherent
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reads
      exact ⟨domainReads, bodyReads, preserved⟩
  | cached origin originCoherent _ =>
      obtain ⟨reads, _⟩ := origin.reading sourceReading originCoherent
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reads
      refine ⟨domainReads, bodyReads, ?_⟩
      simpa only [after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
        (betaWhnfPrefix_fields before).1] using coherent
  | execute execution =>
      obtain ⟨reads, preserved⟩ := execution.reading sourceReading coherent
      obtain ⟨domainReads, bodyReads⟩ := readScopedExpr?_all_parts reads
      exact ⟨domainReads, bodyReads, preserved⟩

theorem context (exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody) :
    exposure.after.lctx = before.lctx := by
  cases exposure with
  | reduce plan => exact plan.context
  | execute execution => exact execution.frame.context
  | cached origin originCoherent hit =>
      simp only [after, BetaPublicWhnf.outerKey, betaWhnfKey_context, (betaWhnfPrefix_fields before).2.1]

end BetaPiExposure

/-- Sort exposure follows the syntactic branch, a public beta reduction,
or an exact cached result of that reduction. The level is the one returned
by the actual exposure call. -/
inductive BetaSortExposure {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (fuel : Nat) (before : TcState .anon) :
    KExpr .anon → AExpr β → KUniv .anon → Type u
  | direct (level : KUniv .anon) (info : ExprInfo .anon) :
      BetaSortExposure resolve locals fuel before (.sort level info) (.sort (readLevel level)) level
  | reduce {source term level info}
      (plan : BetaPublicWhnfPlan resolve locals fuel before source term
        (.sort level info) (.sort (readLevel level))) :
      BetaSortExposure resolve locals fuel before source term level

  | execute {source term level info}
      (execution : BetaPublicExecution resolve locals fuel before source term
        (.sort level info) (.sort (readLevel level))) :
      BetaSortExposure resolve locals fuel before source term level
  | cached {originFuel originBefore source term level info}
      (origin : BetaPublicWhnfPlan resolve locals originFuel originBefore source term
        (.sort level info) (.sort (readLevel level)))
      (hit : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
        (BetaPublicWhnf.outerKey source before).1]? = some (.sort level info)) :
      BetaSortExposure resolve locals fuel before source term level

namespace BetaSortExposure

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source : KExpr .anon} {term : AExpr β} {level : KUniv .anon}

def after (exposure : BetaSortExposure resolve locals fuel before source term level) : TcState .anon :=
  match exposure with
  | .direct .. => before
  | .reduce plan => plan.after
  | .cached .. => (BetaPublicWhnf.outerKey source before).2
  | .execute execution => execution.after

theorem run (exposure : BetaSortExposure resolve locals fuel before source term level) :
    (RecM.ensureSortDirect source).run (methodsN (fuel + 1)) before = .ok level exposure.after := by
  cases exposure with
  | direct => rfl
  | reduce plan =>
      have first := plan.path.first plan.moving
      have entry : RecM.ensureSortDirect source = RecM.ensureSortWhnf source := by
        rw [first.sourceEq]; rfl
      rw [entry, RecM.ensureSortWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, plan.run]
      rfl
  | cached origin hit =>
      have first := origin.path.first origin.moving
      have entry : RecM.ensureSortDirect source = RecM.ensureSortWhnf source := by
        rw [first.sourceEq]; rfl
      rw [entry, RecM.ensureSortWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, origin.cache_hit _ _ hit]
      rfl
  | execute execution =>
      have entry : RecM.ensureSortDirect source = RecM.ensureSortWhnf source := by
        rw [execution.first.2.sourceEq]; rfl
      rw [entry, RecM.ensureSortWhnf, ReaderT.run_bind]
      change EStateM.bind ((RecM.whnf source).run (methodsN (fuel + 1))) _ before = _
      rw [EStateM.bind, execution.run]
      rfl

theorem coherent (exposure : BetaSortExposure resolve locals fuel before source term level)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (initial : before.env.intern.WF) : exposure.after.env.intern.WF := by
  cases exposure with
  | direct => exact initial
  | reduce plan => exact (plan.reading reading initial).2
  | execute execution => exact (execution.reading reading initial).2
  | cached origin hit =>
      simpa only [after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
        (betaWhnfPrefix_fields before).1] using initial

theorem context (exposure : BetaSortExposure resolve locals fuel before source term level) :
    exposure.after.lctx = before.lctx := by
  cases exposure with
  | direct => rfl
  | reduce plan => exact plan.context
  | execute execution => exact execution.frame.context
  | cached origin hit =>
      simp only [after, BetaPublicWhnf.outerKey, betaWhnfKey_context, (betaWhnfPrefix_fields before).2.1]

end BetaSortExposure

end Ix.Kernel.Consistency
