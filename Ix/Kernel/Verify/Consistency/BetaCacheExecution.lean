/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheKeys

/-! Executed beta reduction and retained origins at all three WHNF cache layers. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

/-- State shared by surrounding inference is unchanged by these beta paths.
The three reduction caches, intern table, key memoization, and WHNF counters
are tracked by the computed result state instead. -/
structure BetaCacheFrame (before after : TcState .anon) : Prop where
  constants : after.env.consts = before.env.consts
  full : after.env.inferCache = before.env.inferCache
  only : after.env.inferOnlyCache = before.env.inferOnlyCache
  context : after.lctx = before.lctx
  policy : after.inferOnly = before.inferOnly
  native : after.inNativeReduce = before.inNativeReduce

namespace BetaCacheFrame

theorem refl (before : TcState .anon) : BetaCacheFrame before before :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {before middle after : TcState .anon}
    (first : BetaCacheFrame before middle) (second : BetaCacheFrame middle after) :
    BetaCacheFrame before after :=
  ⟨second.constants.trans first.constants, second.full.trans first.full,
    second.only.trans first.only, second.context.trans first.context,
    second.policy.trans first.policy, second.native.trans first.native⟩

theorem key (source : KExpr .anon) (before : TcState .anon) :
    BetaCacheFrame before (betaWhnfKey source before).2 := by
  unfold betaWhnfKey
  split
  · exact .refl _
  · dsimp only
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem instrument (before : TcState .anon) : BetaCacheFrame before (betaWhnfPrefix before) := by
  unfold betaWhnfPrefix
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem charge (before : TcState .anon) : BetaCacheFrame before (betaWhnfCharge before) := by
  unfold betaWhnfCharge
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end BetaCacheFrame

namespace BetaCacheExecution

def writeNoDelta (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) : TcState .anon :=
  if before.inNativeReduce then before else
    {before with env := {before.env with whnfNoDeltaCache := before.env.whnfNoDeltaCache.insert key result}}

def writeFull (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) : TcState .anon :=
  if before.inNativeReduce then before else
    {before with env := {before.env with whnfCache := before.env.whnfCache.insert key result}}

theorem writeNoDelta_frame (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    BetaCacheFrame before (writeNoDelta key result before) := by
  unfold writeNoDelta
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem writeFull_frame (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    BetaCacheFrame before (writeFull key result before) := by
  unfold writeFull
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem writeNoDelta_intern (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    (writeNoDelta key result before).env.intern = before.env.intern := by
  unfold writeNoDelta
  split <;> rfl

theorem writeFull_intern (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    (writeFull key result before).env.intern = before.env.intern := by
  unfold writeFull
  split <;> rfl

theorem writeNoDelta_key (source result : KExpr .anon) (key : Address × Address) (before : TcState .anon) :
    (betaWhnfKey source (writeNoDelta key result before)).1 = (betaWhnfKey source before).1 := by
  unfold writeNoDelta
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

theorem writeFull_key (source result : KExpr .anon) (key : Address × Address) (before : TcState .anon) :
    (betaWhnfKey source (writeFull key result before)).1 = (betaWhnfKey source before).1 := by
  unfold writeFull
  split <;> exact betaWhnfKey_congr source rfl rfl rfl rfl

end BetaCacheExecution

/-- Structural beta execution either runs its raw path or retains the
execution that produced the exact cached result. Cache presence supplies no
semantic typing assumption. -/
inductive BetaCoreExecution {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) : Nat → TcState .anon → KExpr .anon → AExpr β → KExpr .anon → AExpr β → Type u
  | reduce {fuel before source term result target reduced steps}
      (path : BetaWhnfTrace resolve locals fuel .FULL steps
        (betaWhnfKey source before).2 source term reduced result target)
      (moving : 0 < steps)
      (enough : steps < maxWhnfCoreFuel.toNat)
      (miss : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = none)
      (terminal : BetaWhnfTerminal result) :
      BetaCoreExecution resolve locals fuel before source term result target
  | cached {fuel before source term result target originFuel originBefore}
      (origin : BetaCoreExecution resolve locals originFuel originBefore source term result target)
      (coherent : originBefore.env.intern.WF)
      (hit : (betaWhnfKey source before).2.env.whnfCoreCache[(betaWhnfKey source before).1]? = some result) :
      BetaCoreExecution resolve locals fuel before source term result target

namespace BetaCoreExecution

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def after (execution : BetaCoreExecution resolve locals fuel before source term result target) : TcState .anon :=
  match execution with
  | .reduce (reduced := reduced) _ _ _ _ _ =>
      {reduced with env := {reduced.env with
        whnfCoreCache := reduced.env.whnfCoreCache.insert (betaWhnfKey source before).1 result}}
  | .cached .. => (betaWhnfKey source before).2

/-- A retained first step gives the source's lambda spine at every later
cache use. It does not require repeating reduction in the later state. -/
def first {fuel : Nat} {before : TcState .anon}
    (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    Σ state, BetaStepPlan resolve locals state source term :=
  match execution with
  | .reduce path moving .. => ⟨_, path.first moving⟩
  | .cached origin .. => origin.first

theorem terminal {fuel : Nat} {before : TcState .anon}
    (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    BetaWhnfTerminal result :=
  match execution with
  | .reduce _ _ _ _ terminal => terminal
  | .cached origin .. => origin.terminal

theorem run (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    (RecM.whnfCore source).run (methodsN (fuel + 1)) before = .ok result execution.after := by
  have entry : RecM.whnfCore source = RecM.whnfCoreWithFlagsNonLeaf source .FULL := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  cases execution with
  | reduce path moving enough miss terminal =>
      exact RecM.whnfCoreWithFlagsNonLeaf_fullMiss rfl (betaWhnfKey_run source _)
        ((path.first moving).not_transient _ _) miss (path.run enough)
  | cached origin coherent hit =>
      exact RecM.whnfCoreWithFlagsNonLeaf_fullHit rfl (betaWhnfKey_run source _)
        (origin.first.2.not_transient _ _) hit

theorem reading (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ execution.after.env.intern.WF := by
  induction execution with
  | reduce path moving enough miss terminal =>
      exact path.reading sourceReading ((betaWhnfKey_environment _ _).symm ▸ coherent)
  | cached origin initial hit ih =>
      refine ⟨(ih sourceReading initial).1, ?_⟩
      simpa only [after, betaWhnfKey_environment] using coherent

theorem frame (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    BetaCacheFrame before execution.after := by
  cases execution with
  | reduce path moving enough miss terminal =>
      obtain ⟨table, reduced⟩ := path.frame
      have keyed := BetaCacheFrame.key source before
      simp only [after, reduced]
      exact ⟨keyed.constants, keyed.full, keyed.only, keyed.context, keyed.policy, keyed.native⟩
  | cached => exact .key source before

theorem stable_key (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    (betaWhnfKey source execution.after).1 = (betaWhnfKey source before).1 := by
  cases execution with
  | reduce path moving enough miss terminal =>
      obtain ⟨table, reduced⟩ := path.frame
      simp only [after, reduced]
      apply Eq.trans (b := (betaWhnfKey source (betaWhnfKey source before).2).1)
      · exact betaWhnfKey_congr source rfl rfl rfl rfl
      · exact congrArg Prod.fst (betaWhnfKey_replay source before)
  | cached => exact congrArg Prod.fst (betaWhnfKey_replay source before)

/-- Structural WHNF publishes on a miss even while native reduction is
active; a hit retains the same entry. -/
theorem published (execution : BetaCoreExecution resolve locals fuel before source term result target) :
    execution.after.env.whnfCoreCache[(betaWhnfKey source before).1]? = some result := by
  cases execution with
  | reduce => simp only [after, Std.HashMap.getElem?_insert_self]
  | cached origin coherent hit => exact hit

/-- The producing execution supplies the later hit, including a newly
memoized context suffix. No cache-equality observation is supplied. -/
def replay (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (coherent : before.env.intern.WF) (nextFuel : Nat) :
    BetaCoreExecution resolve locals nextFuel execution.after source term result target :=
  .cached execution coherent (by
    rw [betaWhnfKey_environment, execution.stable_key]
    exact execution.published)

/-- An actual published hit needs no recursive methods or shared fuel. -/
theorem replay_run (execution : BetaCoreExecution resolve locals fuel before source term result target)
    (methods : Methods .anon) :
    (RecM.whnfCore source).run methods execution.after =
      .ok result (betaWhnfKey source execution.after).2 := by
  have entry : RecM.whnfCore source = RecM.whnfCoreWithFlagsNonLeaf source .FULL := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  exact RecM.whnfCoreWithFlagsNonLeaf_fullHit rfl (betaWhnfKey_run source _)
    (execution.first.2.not_transient _ _) (by
      rw [betaWhnfKey_environment, execution.stable_key]
      exact execution.published)

end BetaCoreExecution

/-- The no-delta layer may use its own retained result or an executed
structural reduction, which may itself be a cache hit. -/
inductive BetaNoDeltaExecution {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) : Nat → TcState .anon → KExpr .anon → AExpr β → KExpr .anon → AExpr β → Type u
  | reduce {fuel before source term result target}
      (core : BetaCoreExecution resolve locals fuel (betaWhnfKey source before).2 source term result target)
      (miss : (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = none) :
      BetaNoDeltaExecution resolve locals fuel before source term result target
  | cached {fuel before source term result target originFuel originBefore}
      (origin : BetaNoDeltaExecution resolve locals originFuel originBefore source term result target)
      (coherent : originBefore.env.intern.WF)
      (hit : (betaWhnfKey source before).2.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = some result) :
      BetaNoDeltaExecution resolve locals fuel before source term result target

namespace BetaNoDeltaExecution

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def after (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) : TcState .anon :=
  match execution with
  | .reduce core _ => BetaCacheExecution.writeNoDelta (betaWhnfKey source before).1 result core.after
  | .cached .. => (betaWhnfKey source before).2

def first {fuel : Nat} {before : TcState .anon}
    (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) :
    Σ state, BetaStepPlan resolve locals state source term :=
  match execution with
  | .reduce core _ => core.first
  | .cached origin .. => origin.first

theorem terminal {fuel : Nat} {before : TcState .anon}
    (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) :
    BetaWhnfTerminal result :=
  match execution with
  | .reduce core _ => core.terminal
  | .cached origin .. => origin.terminal

theorem run (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) :
    (RecM.whnfNoDelta source).run (methodsN (fuel + 1)) before = .ok result execution.after := by
  have entry : RecM.whnfNoDelta source = RecM.whnfNoDeltaImplNonLeaf source .FULL .collapse := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  cases execution with
  | reduce core miss =>
      exact RecM.whnfNoDeltaImplNonLeaf_fullMiss_conditional rfl (betaWhnfKey_run source _)
        (core.first.2.not_transient _ _) miss (core.terminal.noDelta_uncached .FULL .collapse core.run)
  | cached origin coherent hit =>
      exact RecM.whnfNoDeltaImplNonLeaf_fullHit rfl (betaWhnfKey_run source _)
        (origin.first.2.not_transient _ _) hit

theorem reading (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ execution.after.env.intern.WF := by
  induction execution with
  | reduce core miss =>
      obtain ⟨reading, preserved⟩ := core.reading sourceReading ((betaWhnfKey_environment _ _).symm ▸ coherent)
      exact ⟨reading, (BetaCacheExecution.writeNoDelta_intern _ _ _).symm ▸ preserved⟩
  | cached origin initial hit ih =>
      refine ⟨(ih sourceReading initial).1, ?_⟩
      simpa only [after, betaWhnfKey_environment] using coherent

theorem frame (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) :
    BetaCacheFrame before execution.after := by
  cases execution with
  | reduce core miss =>
      exact (BetaCacheFrame.key source before).trans
        (core.frame.trans (BetaCacheExecution.writeNoDelta_frame _ _ _))
  | cached => exact .key source before

theorem stable_key (execution : BetaNoDeltaExecution resolve locals fuel before source term result target) :
    (betaWhnfKey source execution.after).1 = (betaWhnfKey source before).1 := by
  cases execution with
  | reduce core miss =>
      exact (BetaCacheExecution.writeNoDelta_key _ _ _ _).trans
        (core.stable_key.trans (congrArg Prod.fst (betaWhnfKey_replay source before)))
  | cached => exact congrArg Prod.fst (betaWhnfKey_replay source before)

theorem published (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (inactive : before.inNativeReduce = false) :
    execution.after.env.whnfNoDeltaCache[(betaWhnfKey source before).1]? = some result := by
  cases execution with
  | reduce core miss =>
      have native : core.after.inNativeReduce = false :=
        core.frame.native.trans ((betaWhnfKey_native _ _).trans inactive)
      simp only [after, BetaCacheExecution.writeNoDelta, native, Bool.false_eq_true,
        if_false, Std.HashMap.getElem?_insert_self]
  | cached origin coherent hit => exact hit

def replay (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) (nextFuel : Nat) :
    BetaNoDeltaExecution resolve locals nextFuel execution.after source term result target :=
  .cached execution coherent (by
    rw [betaWhnfKey_environment, execution.stable_key]
    exact execution.published inactive)

theorem replay_run (execution : BetaNoDeltaExecution resolve locals fuel before source term result target)
    (inactive : before.inNativeReduce = false) (methods : Methods .anon) :
    (RecM.whnfNoDelta source).run methods execution.after =
      .ok result (betaWhnfKey source execution.after).2 := by
  have entry : RecM.whnfNoDelta source = RecM.whnfNoDeltaImplNonLeaf source .FULL .collapse := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  exact RecM.whnfNoDeltaImplNonLeaf_fullHit rfl (betaWhnfKey_run source _)
    (execution.first.2.not_transient _ _) (by
      rw [betaWhnfKey_environment, execution.stable_key]
      exact execution.published inactive)

end BetaNoDeltaExecution

/-- Public WHNF composes its own cache policy with the two lower layers.
Only an outer miss charges shared fuel. Native reduction can suppress writes
at either upper layer without invalidating the executed beta result. -/
inductive BetaPublicExecution {β : Type u} (resolve : Address → Option (ConstRef β))
    (locals : List FVarId) : Nat → TcState .anon → KExpr .anon → AExpr β → KExpr .anon → AExpr β → Type u
  | reduce {fuel before source term result target}
      (inner : BetaNoDeltaExecution resolve locals fuel
        (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2) source term result target)
      (miss : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
        (BetaPublicWhnf.outerKey source before).1]? = none)
      (fuelAvailable : (before.recFuel == 0) = false) :
      BetaPublicExecution resolve locals fuel before source term result target
  | cached {fuel before source term result target originFuel originBefore}
      (origin : BetaPublicExecution resolve locals originFuel originBefore source term result target)
      (coherent : originBefore.env.intern.WF)
      (hit : (BetaPublicWhnf.outerKey source before).2.env.whnfCache[
        (BetaPublicWhnf.outerKey source before).1]? = some result) :
      BetaPublicExecution resolve locals fuel before source term result target

namespace BetaPublicExecution

variable {β : Type u} {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
  {fuel : Nat} {before : TcState .anon} {source result : KExpr .anon} {term target : AExpr β}

def after (execution : BetaPublicExecution resolve locals fuel before source term result target) : TcState .anon :=
  match execution with
  | .reduce inner .. => BetaCacheExecution.writeFull (BetaPublicWhnf.outerKey source before).1 result inner.after
  | .cached .. => (BetaPublicWhnf.outerKey source before).2

def first {fuel : Nat} {before : TcState .anon}
    (execution : BetaPublicExecution resolve locals fuel before source term result target) :
    Σ state, BetaStepPlan resolve locals state source term :=
  match execution with
  | .reduce inner .. => inner.first
  | .cached origin .. => origin.first

theorem terminal {fuel : Nat} {before : TcState .anon}
    (execution : BetaPublicExecution resolve locals fuel before source term result target) :
    BetaWhnfTerminal result :=
  match execution with
  | .reduce inner .. => inner.terminal
  | .cached origin .. => origin.terminal

theorem run (execution : BetaPublicExecution resolve locals fuel before source term result target) :
    (RecM.whnf source).run (methodsN (fuel + 1)) before = .ok result execution.after := by
  have entry : RecM.whnf source = RecM.whnfWithNatSuccModeNonLeaf source .collapse := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  cases execution with
  | reduce inner miss fuelAvailable =>
      exact RecM.whnfWithNatSuccModeNonLeaf_miss_conditional (betaWhnfPrefix_run source before _)
        (betaWhnfKey_run source _) (inner.first.2.not_transient _ _) miss
        (betaWhnfCharge_run _ _ (by
          simpa only [BetaPublicWhnf.outerKey, betaWhnfKey_fuel,
            (betaWhnfPrefix_fields before).2.2.2] using fuelAvailable))
        (inner.terminal.full_uncached .collapse inner.run)
  | cached origin coherent hit =>
      exact RecM.whnfWithNatSuccModeNonLeaf_hit (betaWhnfPrefix_run source before _)
        (betaWhnfKey_run source _) (origin.first.2.not_transient _ _) hit

theorem reading (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (sourceReading : readScopedExpr? resolve locals source = some term.erase)
    (coherent : before.env.intern.WF) :
    readScopedExpr? resolve locals result = some target.erase ∧ execution.after.env.intern.WF := by
  induction execution with
  | @reduce fuel before source term result target inner miss fuelAvailable =>
      have initial : (betaWhnfCharge (BetaPublicWhnf.outerKey source before).2).env.intern.WF := by
        simpa only [BetaPublicWhnf.outerKey, betaWhnfKey_environment,
          betaWhnfCharge_fields, betaWhnfPrefix_fields] using coherent
      obtain ⟨reading, preserved⟩ := inner.reading sourceReading initial
      exact ⟨reading, (BetaCacheExecution.writeFull_intern _ _ _).symm ▸ preserved⟩
  | cached origin initial hit ih =>
      refine ⟨(ih sourceReading initial).1, ?_⟩
      simpa only [after, BetaPublicWhnf.outerKey, betaWhnfKey_environment,
        betaWhnfPrefix_fields] using coherent

theorem frame (execution : BetaPublicExecution resolve locals fuel before source term result target) :
    BetaCacheFrame before execution.after := by
  have keyed : BetaCacheFrame before (BetaPublicWhnf.outerKey source before).2 :=
    (BetaCacheFrame.instrument before).trans (.key source _)
  cases execution with
  | reduce inner miss fuelAvailable =>
      exact keyed.trans ((BetaCacheFrame.charge _).trans
        (inner.frame.trans (BetaCacheExecution.writeFull_frame _ _ _)))
  | cached => exact keyed

theorem stable_key (execution : BetaPublicExecution resolve locals fuel before source term result target) :
    (betaWhnfKey source execution.after).1 = (betaWhnfKey source before).1 := by
  have keyed : (betaWhnfKey source (BetaPublicWhnf.outerKey source before).2).1 =
      (betaWhnfKey source before).1 :=
    (congrArg Prod.fst (betaWhnfKey_replay source (betaWhnfPrefix before))).trans
      (betaWhnfKey_prefix source before)
  cases execution with
  | reduce inner miss fuelAvailable =>
      exact (BetaCacheExecution.writeFull_key _ _ _ _).trans
        (inner.stable_key.trans ((betaWhnfKey_charge _ _).trans keyed))
  | cached => exact keyed

theorem published (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (inactive : before.inNativeReduce = false) :
    execution.after.env.whnfCache[(betaWhnfKey source before).1]? = some result := by
  have key : (BetaPublicWhnf.outerKey source before).1 = (betaWhnfKey source before).1 :=
    betaWhnfKey_prefix source before
  cases execution with
  | reduce inner miss fuelAvailable =>
      have native : inner.after.inNativeReduce = false := by
        rw [inner.frame.native, BetaPublicWhnf.outerKey]
        simpa only [betaWhnfCharge_fields, betaWhnfKey_native, betaWhnfPrefix_fields] using inactive
      simp only [after, BetaCacheExecution.writeFull, native, Bool.false_eq_true,
        if_false, key, Std.HashMap.getElem?_insert_self]
  | cached origin coherent hit => simpa only [after, key] using hit

def replay (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (coherent : before.env.intern.WF) (inactive : before.inNativeReduce = false) (nextFuel : Nat) :
    BetaPublicExecution resolve locals nextFuel execution.after source term result target :=
  .cached execution coherent (by
    rw [BetaPublicWhnf.outerKey, betaWhnfKey_environment, (betaWhnfPrefix_fields _).1,
      betaWhnfKey_prefix, execution.stable_key]
    exact execution.published inactive)

theorem replay_run (execution : BetaPublicExecution resolve locals fuel before source term result target)
    (inactive : before.inNativeReduce = false) (methods : Methods .anon) :
    (RecM.whnf source).run methods execution.after =
      .ok result (BetaPublicWhnf.outerKey source execution.after).2 := by
  have entry : RecM.whnf source = RecM.whnfWithNatSuccModeNonLeaf source .collapse := by
    rw [execution.first.2.sourceEq]; rfl
  rw [entry]
  exact RecM.whnfWithNatSuccModeNonLeaf_hit (betaWhnfPrefix_run source _ _)
    (betaWhnfKey_run source _) (execution.first.2.not_transient _ _) (by
      rw [BetaPublicWhnf.outerKey, betaWhnfKey_environment, (betaWhnfPrefix_fields _).1,
        betaWhnfKey_prefix, execution.stable_key]
      exact execution.published inactive)

end BetaPublicExecution

/-- The earlier three-miss interface is a special case of the complete
cache-layer execution. No new observation or typing premise is needed. -/
def BetaPublicWhnfPlan.execution {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    BetaPublicExecution resolve locals fuel before source term result target :=
  .reduce (.reduce (.reduce plan.path plan.moving plan.enough plan.coreMiss plan.terminal)
    plan.noDeltaMiss) plan.outerMiss plan.fuelAvailable

theorem BetaPublicWhnfPlan.execution_after {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {fuel : Nat} {before : TcState .anon}
    {source result : KExpr .anon} {term target : AExpr β}
    (plan : BetaPublicWhnfPlan resolve locals fuel before source term result target) :
    plan.execution.after = plan.after := by
  have executed := plan.execution.run
  rw [plan.run] at executed
  exact (EStateM.Result.ok.inj executed).2.symm

end Ix.Kernel.Consistency
