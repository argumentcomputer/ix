/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheHistory
import Ix.Kernel.Verify.Consistency.BetaCacheConstruction

/-! A single retained map history supplies the origins at every cache layer.
The caller provides finite collision data and the resources needed on misses. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

namespace BetaCacheEventOrigin

variable {β : Type u} {partition : WhnfCachePartition} {key : Address × Address}
  {source result : KExpr .anon}

theorem terminal (origin : BetaCacheEventOrigin (β := β) partition key source result) :
    BetaWhnfTerminal result :=
  match origin with
  | .head _ _ terminal => terminal
  | .noDelta execution .. => execution.terminal
  | .full execution .. => execution.terminal

theorem headOrigin (origin : BetaCacheEventOrigin (β := β) partition key source result)
    (core : partition = .core ∨ partition = .coreCheap) : Nonempty (BetaHeadCacheOrigin (β := β) source result) :=
  match origin with
  | .head call coherent _ => ⟨call.origin coherent⟩
  | .noDelta .. => by rcases core with impossible | impossible <;> cases impossible
  | .full .. => by rcases core with impossible | impossible <;> cases impossible

theorem noDeltaOrigin (origin : BetaCacheEventOrigin (β := β) partition key source result)
    (selected : partition = .noDelta) :
    ∃ resolve : Address → Option (ConstRef β), ∃ locals fuel before term target,
      ∃ _ : BetaNoDeltaExecution resolve locals fuel before source term result target, before.env.intern.WF :=
  match origin with
  | .head (flags := flags) _ _ _ => by
      cases full : flags.isFull <;> simp only [WhnfCachePartition.ofFlags, full, Bool.false_eq_true, if_false, if_true] at selected
      all_goals cases selected
  | .noDelta execution coherent _ => ⟨_, _, _, _, _, _, execution, coherent⟩
  | .full .. => by cases selected

theorem fullOrigin (origin : BetaCacheEventOrigin (β := β) partition key source result)
    (selected : partition = .full) :
    ∃ resolve : Address → Option (ConstRef β), ∃ locals fuel before term target,
      ∃ _ : BetaPublicExecution resolve locals fuel before source term result target, before.env.intern.WF :=
  match origin with
  | .head (flags := flags) _ _ _ => by
      cases full : flags.isFull <;> simp only [WhnfCachePartition.ofFlags, full, Bool.false_eq_true, if_false, if_true] at selected
      all_goals cases selected
  | .noDelta .. => by cases selected
  | .full execution coherent _ => ⟨_, _, _, _, _, _, execution, coherent⟩

end BetaCacheEventOrigin

namespace BetaCacheHistory

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {state : TcState .anon} {source : KExpr .anon}

theorem headOrigins (history : BetaCacheHistory β state) (data : history.KeyData source) (flags : WhnfFlags) :
    BetaWhnfSource.HeadOrigins (β := β) flags state source := by
  intro cached found
  rw [WhnfCachePartition.lookupCore, WhnfCachePartition.key] at found
  obtain ⟨origin⟩ := history.selected data (betaWhnfKey_address source state) found
  apply origin.headOrigin
  cases full : flags.isFull <;> simp [WhnfCachePartition.ofFlags, full]

/-- A full structural hit can originate at a recursive head call, including
one that ran with zero method depth. The current replay constructs the
ordinary structural witness without assuming matching annotations. -/
theorem coreResources (history : BetaCacheHistory β state) (data : history.KeyData source)
    (coherent : state.env.intern.WF)
    (cold : (betaWhnfKey source state).2.env.whnfCoreCache[(betaWhnfKey source state).1]? = none →
      BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (betaWhnfKey source state).2 source) :
    BetaWhnfSource.CoreResources resolve locals fuel state source := by
  refine ⟨?_, cold⟩
  intro cached found
  have stored : (WhnfCachePartition.core.cache state)[(betaWhnfKey source state).1]? = some cached := by
    simpa only [WhnfCachePartition.cache, betaWhnfKey_environment] using found
  obtain ⟨origin⟩ := history.selected data (betaWhnfKey_address source state) stored
  obtain ⟨producer⟩ := origin.headOrigin (.inl rfl)
  exact ⟨producer.resolve, producer.locals, 0, state, producer.term, producer.target,
    .cachedHead producer.call producer.coherent origin.terminal found, coherent⟩

theorem noDeltaResources (history : BetaCacheHistory β state) (data : history.KeyData source)
    (coherent : state.env.intern.WF)
    (cold : (betaWhnfKey source state).2.env.whnfNoDeltaCache[(betaWhnfKey source state).1]? = none →
      (betaWhnfKey source state).2.env.whnfCoreCache[(betaWhnfKey source state).1]? = none →
        BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (betaWhnfKey source state).2 source) :
    BetaWhnfSource.NoDeltaResources resolve locals fuel state source := by
  constructor
  · intro cached found
    have stored : (WhnfCachePartition.noDelta.cache state)[(betaWhnfKey source state).1]? = some cached := by
      simpa only [WhnfCachePartition.cache, betaWhnfKey_environment] using found
    obtain ⟨origin⟩ := history.selected data (betaWhnfKey_address source state) stored
    exact origin.noDeltaOrigin rfl
  · intro missing
    apply (history.key source).coreResources data ((betaWhnfKey_environment _ _).symm ▸ coherent)
    intro coreMissing
    simpa only [betaWhnfKey_replay] using cold missing (by simpa only [betaWhnfKey_replay] using coreMissing)

theorem publicResources (history : BetaCacheHistory β state) (data : history.KeyData source)
    (coherent : state.env.intern.WF)
    (cold : (BetaPublicWhnf.outerKey source state).2.env.whnfCache[(BetaPublicWhnf.outerKey source state).1]? = none →
      (BetaPublicWhnf.noDeltaKey source state).2.env.whnfNoDeltaCache[(BetaPublicWhnf.noDeltaKey source state).1]? = none →
      (BetaPublicWhnf.coreKey source state).2.env.whnfCoreCache[(BetaPublicWhnf.coreKey source state).1]? = none →
        BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (BetaPublicWhnf.coreKey source state).2 source) :
    BetaWhnfSource.PublicResources resolve locals fuel state source := by
  constructor
  · intro cached found
    have stored : (WhnfCachePartition.full.cache state)[(BetaPublicWhnf.outerKey source state).1]? = some cached := by
      simpa only [WhnfCachePartition.cache, BetaPublicWhnf.outerKey, betaWhnfKey_environment, betaWhnfPrefix_fields] using found
    obtain ⟨origin⟩ := history.selected data (betaWhnfKey_address source (betaWhnfPrefix state)) stored
    exact origin.fullOrigin rfl
  · intro missing
    have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source state).2).env.intern.WF := by
      simpa only [BetaPublicWhnf.outerKey, betaWhnfCharge_fields, betaWhnfKey_environment, betaWhnfPrefix_fields] using coherent
    apply ((history.instrument.key source).charge).noDeltaResources data initial
    intro noDeltaMissing coreMissing
    have missingCore : (BetaPublicWhnf.coreKey source state).2.env.whnfCoreCache[
        (BetaPublicWhnf.coreKey source state).1]? = none := by
      simpa only [BetaPublicWhnf.coreKey, BetaPublicWhnf.noDeltaKey, BetaPublicWhnf.outerKey, betaWhnfKey_replay] using coreMissing
    simpa only [BetaPublicWhnf.coreKey, BetaPublicWhnf.noDeltaKey, BetaPublicWhnf.outerKey, betaWhnfKey_replay] using
      cold missing noDeltaMissing missingCore

end BetaCacheHistory

theorem BetaCoreExecution.exists_of_history {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (history : BetaCacheHistory β before) (data : history.KeyData source)
    (cold : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none →
      BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfCore source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaCoreExecution resolve locals fuel before source term result target,
      execution.after = after ∧ Nonempty (BetaCacheHistory β after) := by
  obtain ⟨target, execution, stateEq⟩ := exists_of_success chosen (history.coreResources data coherent cold) reading coherent accepted
  refine ⟨target, execution, stateEq, ?_⟩
  rw [← stateEq]
  exact ⟨history.afterCore execution reading coherent⟩

theorem BetaNoDeltaExecution.exists_of_history {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (history : BetaCacheHistory β before) (data : history.KeyData source)
    (cold : (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = none →
      (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none →
        BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (betaWhnfKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnfNoDelta source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaNoDeltaExecution resolve locals fuel before source term result target,
      execution.after = after ∧ Nonempty (BetaCacheHistory β after) := by
  obtain ⟨target, execution, stateEq⟩ := exists_of_success chosen (history.noDeltaResources data coherent cold) reading coherent accepted
  refine ⟨target, execution, stateEq, ?_⟩
  rw [← stateEq]
  exact ⟨history.afterNoDelta execution reading coherent⟩

theorem BetaPublicExecution.exists_of_history {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before after : TcState .anon}
    {source result : KExpr .anon} {term : AExpr β}
    (chosen : BetaWhnfSource.selected source = true)
    (history : BetaCacheHistory β before) (data : history.KeyData source)
    (cold : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[(BetaPublicWhnf.outerKey source before).1]? = none →
      (BetaPublicWhnf.noDeltaKey source before).2.env.whnfNoDeltaCache[(BetaPublicWhnf.noDeltaKey source before).1]? = none →
      (BetaPublicWhnf.coreKey source before).2.env.whnfCoreCache[(BetaPublicWhnf.coreKey source before).1]? = none →
        BetaWhnfSource.Resources resolve locals (fuel + 1) .FULL maxWhnfCoreFuel.toNat (BetaPublicWhnf.coreKey source before).2 source)
    (reading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF)
    (accepted : (RecM.whnf source).run (methodsN (fuel + 1)) before = .ok result after) :
    ∃ target, ∃ execution : BetaPublicExecution resolve locals fuel before source term result target,
      execution.after = after ∧ Nonempty (BetaCacheHistory β after) := by
  obtain ⟨target, execution, stateEq⟩ := exists_of_success chosen (history.publicResources data coherent cold) reading coherent accepted
  refine ⟨target, execution, stateEq, ?_⟩
  rw [← stateEq]
  exact ⟨history.afterPublic execution reading coherent⟩

end Ix.Kernel.Consistency
