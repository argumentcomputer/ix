/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaTraceConstruction

/-! Construct the three cache-layer witnesses from actual successful calls.
Inputs describe finite raw resources and the origins of stored entries; the
current cache lookup, fuel charge, reduction path, and result are recovered. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

namespace BetaWhnfSource

/-- A structural hit has an actual producing execution. A miss needs only
the finite resources along the source's computed beta orbit. -/
structure CoreResources {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (before : TcState .anon) (source : KExpr .anon) (term : AExpr β) : Prop where
  origins : ∀ cached,
    (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = some cached →
      ∃ originFuel originBefore target,
        ∃ _ : BetaCoreExecution resolve locals originFuel originBefore source term cached target,
          originBefore.env.intern.WF
  cold : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none →
    Resources maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source

structure NoDeltaResources {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (before : TcState .anon) (source : KExpr .anon) (term : AExpr β) : Prop where
  origins : ∀ cached,
    (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = some cached →
      ∃ originFuel originBefore target,
        ∃ _ : BetaNoDeltaExecution resolve locals originFuel originBefore source term cached target,
          originBefore.env.intern.WF
  cold : (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = none →
    CoreResources resolve locals (betaWhnfKey source before).2 source term

structure PublicResources {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) (before : TcState .anon) (source : KExpr .anon) (term : AExpr β) : Prop where
  origins : ∀ cached,
    (BetaPublicWhnf.outerKey source before).2.env.whnfCache[(BetaPublicWhnf.outerKey source before).1]? = some cached →
      ∃ originFuel originBefore target,
        ∃ _ : BetaPublicExecution resolve locals originFuel originBefore source term cached target,
          originBefore.env.intern.WF
  cold : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
      (BetaPublicWhnf.outerKey source before).1]? = none →
    NoDeltaResources resolve locals (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2) source term

end BetaWhnfSource

theorem betaWhnfCharge_success {before after : TcState .anon} {methods : Methods .anon}
    (accepted : (RecM.whnfWithNatSuccModeMissCharge : RecM .anon Unit).run methods before = .ok () after) :
    (before.recFuel == 0) = false ∧ after = betaWhnfCharge before := by
  have enough : (before.recFuel == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro empty
    unfold RecM.whnfWithNatSuccModeMissCharge at accepted
    rw [ReaderT.run_bind] at accepted
    change EStateM.bind (TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }))
      (fun _ => TcM.tick) before = _ at accepted
    let bumped := if before.stats then { before with whnfMisses := before.whnfMisses + 1 } else before
    have bumpRun : TcM.bumpStats (fun state => { state with whnfMisses := state.whnfMisses + 1 }) before =
        .ok () bumped := by
      unfold TcM.bumpStats
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
      by_cases stats : before.stats = true
      · simp only [bumped, if_pos stats]; rfl
      · simp only [bumped, if_neg stats]; rfl
    have exhausted : (bumped.recFuel == 0) = true := by
      dsimp only [bumped]
      split <;> exact empty
    have failed : TcM.tick bumped = .error .maxRecFuel bumped := by
      unfold TcM.tick
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ bumped = _
      rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) bumped = .ok bumped bumped from rfl]
      simp only
      rw [exhausted]
      rfl
    rw [EStateM.bind, bumpRun] at accepted
    change TcM.tick bumped = _ at accepted
    rw [failed] at accepted
    cases accepted
  exact ⟨enough, (EStateM.Result.ok.inj ((betaWhnfCharge_run before methods enough).symm.trans accepted)).2.symm⟩

/-- The actual lookup selects its branch; successful execution supplies the
result and exact state, including an entry supplied by an earlier run. -/
theorem BetaCoreExecution.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.CoreResources resolve locals before source term)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCore source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaCoreExecution resolve locals fuel before source term result target,
      execution.after = after := by
  cases observed : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? with
  | none => exact exists_of_miss_success chosen (resources.cold observed) reading coherent observed accepted
  | some cached =>
      obtain ⟨originFuel, originBefore, target, origin, initial⟩ := resources.origins cached observed
      let execution : BetaCoreExecution resolve locals fuel before source term cached target :=
        .cached origin initial observed
      obtain ⟨rfl, finalEq⟩ := EStateM.Result.ok.inj (execution.run.symm.trans accepted)
      exact ⟨target, execution, finalEq⟩

theorem BetaNoDeltaExecution.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.NoDeltaResources resolve locals before source term)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfNoDelta source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaNoDeltaExecution resolve locals fuel before source term result target,
      execution.after = after := by
  cases observed : (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? with
  | none =>
      have entry : RecM.whnfNoDelta source = RecM.whnfNoDeltaImplNonLeaf source .FULL .collapse :=
        (BetaWhnfSource.selected_entry chosen).noDelta .FULL .collapse
      have direct := accepted
      rw [entry] at direct
      obtain ⟨coreResult, coreAfter, coreRun⟩ := RecM.whnfNoDeltaImplNonLeaf_fullMiss_core_success rfl
        (betaWhnfKey_run source before) ((BetaWhnfSource.selected_entry chosen).not_transient _ _) observed direct
      have initial : (betaWhnfKey source before).2.env.intern.WF := by
        simpa only [betaWhnfKey_environment] using coherent
      obtain ⟨target, core, _⟩ := BetaCoreExecution.exists_of_success chosen
        (resources.cold observed) reading initial coreRun
      let execution : BetaNoDeltaExecution resolve locals fuel before source term coreResult target :=
        .reduce core observed
      obtain ⟨rfl, finalEq⟩ := EStateM.Result.ok.inj (execution.run.symm.trans accepted)
      exact ⟨target, execution, finalEq⟩
  | some cached =>
      obtain ⟨originFuel, originBefore, target, origin, initial⟩ := resources.origins cached observed
      let execution : BetaNoDeltaExecution resolve locals fuel before source term cached target :=
        .cached origin initial observed
      obtain ⟨rfl, finalEq⟩ := EStateM.Result.ok.inj (execution.run.symm.trans accepted)
      exact ⟨target, execution, finalEq⟩

theorem BetaPublicExecution.exists_of_success {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (resources : BetaWhnfSource.PublicResources resolve locals before source term)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnf source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaPublicExecution resolve locals fuel before source term result target,
      execution.after = after := by
  cases observed : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
      (BetaPublicWhnf.outerKey source before).1]? with
  | none =>
      have entry : RecM.whnf source = RecM.whnfWithNatSuccModeNonLeaf source .collapse :=
        (BetaWhnfSource.selected_entry chosen).full .collapse
      have direct := accepted
      rw [entry] at direct
      obtain ⟨charged, noDeltaResult, noDeltaAfter, charge, noDeltaRun⟩ :=
        RecM.whnfWithNatSuccModeNonLeaf_miss_noDelta_success (betaWhnfPrefix_run source before _)
          (betaWhnfKey_run source _) ((BetaWhnfSource.selected_entry chosen).not_transient _ _) observed direct
      obtain ⟨fuelAvailable, rfl⟩ := betaWhnfCharge_success charge
      have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2).env.intern.WF := by
        simpa only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_environment,
          betaWhnfPrefix_fields] using coherent
      obtain ⟨target, inner, _⟩ := BetaNoDeltaExecution.exists_of_success chosen
        (resources.cold observed) reading initial noDeltaRun
      let execution : BetaPublicExecution resolve locals fuel before source term noDeltaResult target :=
        .reduce inner observed (by
          simpa only [BetaPublicWhnf.outerKey, betaWhnfKey_fuel, betaWhnfPrefix_fields] using fuelAvailable)
      obtain ⟨rfl, finalEq⟩ := EStateM.Result.ok.inj (execution.run.symm.trans accepted)
      exact ⟨target, execution, finalEq⟩
  | some cached =>
      obtain ⟨originFuel, originBefore, target, origin, initial⟩ := resources.origins cached observed
      let execution : BetaPublicExecution resolve locals fuel before source term cached target :=
        .cached origin initial observed
      obtain ⟨rfl, finalEq⟩ := EStateM.Result.ok.inj (execution.run.symm.trans accepted)
      exact ⟨target, execution, finalEq⟩

end Ix.Kernel.Consistency
