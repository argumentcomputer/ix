/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheConstruction
import Ix.Kernel.Verify.Consistency.BetaPublicWhnf
import Ix.Kernel.Verify.Infer.ExposureSuccess

/-! Recover the Pi and sort exposure witnesses used by the original
inference traces from source resources and actual successful exposure. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

private theorem sort_reading_shape {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {level : KUniv .anon} {info : ExprInfo .anon} {target : AExpr β}
    (reading : readScopedExpr? resolve locals (.sort level info) = some target.erase) :
    target = .sort (readLevel level) := by
  cases target <;> simp_all [readScopedExpr?, AExpr.erase]

private theorem forall_reading_shape {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {name bi} {rawDomain rawBody : KExpr .anon} {info : ExprInfo .anon}
    {target : AExpr β}
    (reading : readScopedExpr? resolve locals (.all name bi rawDomain rawBody info) = some target.erase) :
    ∃ condition domain body, target = .forallE condition domain body := by
  cases target with
  | forallE condition domain body => exact ⟨condition, domain, body, rfl⟩
  | _ =>
      cases domainReads : readScopedExpr? resolve locals rawDomain <;>
        cases bodyReads : readScopedExpr? resolve locals rawBody 1 <;>
        simp [readScopedExpr?, domainReads, bodyReads, AExpr.erase] at reading

theorem BetaSortExposure.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source : KExpr .anon} {term : AExpr β} {level : KUniv .anon}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.PublicResources resolve locals before source term)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.ensureSortDirect source).run (methodsN (fuel + 1)) before = .ok level after) :
    ∃ exposure : BetaSortExposure resolve locals fuel before source term level, exposure.after = after := by
  have entry : RecM.ensureSortDirect source = RecM.ensureSortWhnf source :=
    (BetaWhnfSource.selected_entry chosen).sort
  rw [entry] at accepted
  obtain ⟨info, rawRun⟩ := RecM.ensureSortWhnf_success accepted
  obtain ⟨target, execution, stateEq⟩ := BetaPublicExecution.exists_of_success chosen resources reading coherent rawRun
  have resultReading := (execution.reading reading coherent).1
  obtain rfl := sort_reading_shape resultReading
  exact ⟨.execute execution, stateEq⟩

theorem BetaPiExposure.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source rawDomain rawBody : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.PublicResources resolve locals before source term)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.ensureForallDirect source).run (methodsN (fuel + 1)) before = .ok (rawDomain, rawBody) after) :
    ∃ condition domain body,
      ∃ exposure : BetaPiExposure resolve locals fuel before source term condition domain body rawDomain rawBody,
        exposure.after = after := by
  have entry : RecM.ensureForallDirect source = RecM.ensureForallWhnf source :=
    (BetaWhnfSource.selected_entry chosen).forallE
  rw [entry] at accepted
  obtain ⟨name, bi, info, rawRun⟩ := RecM.ensureForallWhnf_success accepted
  obtain ⟨target, execution, stateEq⟩ := BetaPublicExecution.exists_of_success chosen resources reading coherent rawRun
  have resultReading := (execution.reading reading coherent).1
  obtain ⟨condition, domain, body, rfl⟩ := forall_reading_shape resultReading
  exact ⟨condition, domain, body, .execute execution, stateEq⟩

end Ix.Kernel.Consistency
