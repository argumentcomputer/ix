/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Policy
import Ix.Theory.Model.Extension

namespace Ix.Theory.Certified

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

namespace PrimitiveSignature

variable (signature : PrimitiveSignature β)

def falseEntry : ConstantEntry β := ⟨0, .sort .zero, none, [], []⟩
def falseElimEntry : ConstantEntry β := ⟨1, signature.falseElimReading, none, [], []⟩

def environment [DecidableEq β] : Environment β := fun r =>
  if r = signature.falseType then some falseEntry
  else if r = signature.falseElim then some signature.falseElimEntry
  else none

@[simp] theorem environment_false [DecidableEq β] :
    signature.environment signature.falseType = some falseEntry := by
  simp [environment]

@[simp] theorem environment_falseElim [DecidableEq β] :
    signature.environment signature.falseElim = some signature.falseElimEntry := by
  simp [environment, Ne.symm signature.distinct]

theorem environment_equations [DecidableEq β] {r : ConstRef β} {entry : ConstantEntry β}
    (h : signature.environment r = some entry) : entry.equations = [] := by
  unfold environment at h
  split at h
  · cases Option.some.inj h; rfl
  · split at h
    · cases Option.some.inj h; rfl
    · contradiction

def Present (entries : Environment β) : Prop :=
  entries signature.falseType = some falseEntry ∧
    entries signature.falseElim = some signature.falseElimEntry

theorem environment_facts [DecidableEq β] {r : ConstRef β} {entry : ConstantEntry β}
    (h : signature.environment r = some entry) : entry.facts = [] := by
  unfold environment at h
  split at h
  · cases Option.some.inj h; rfl
  · split at h
    · cases Option.some.inj h; rfl
    · contradiction

theorem present_environment [DecidableEq β] : signature.Present signature.environment :=
  ⟨signature.environment_false, signature.environment_falseElim⟩

theorem Present.insert [DecidableEq β] {entries : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} (h : signature.Present entries) (fresh : entries r = none) :
    signature.Present (entries.insert r entry) :=
  ⟨Environment.insert_old fresh h.1, Environment.insert_old fresh h.2⟩

/-- Compatibility fixes primitive values in addition to declaration membership.
In particular, membership in Prop cannot choose the meaning of False. -/
structure Compatible (entries : Environment β) (constants : Assignment β V) : Prop where
  realizes : Realizes constants entries
  falseValue : ∀ levels, constants signature.falseType levels = empty
  falseElimValue : ∀ levels,
    constants signature.falseElim levels = Model.falseElimValue (levels.getD 0 0)

theorem Compatible.extend {entries entries' : Environment β}
    {constants constants' : Assignment β V}
    (h : signature.Compatible entries constants) (present : signature.Present entries)
    (hM : Realizes constants' entries')
    (agree : Assignment.AgreesOn entries constants constants') :
    signature.Compatible entries' constants' where
  realizes := hM
  falseValue levels := (agree _ _ present.1 levels).trans (h.falseValue levels)
  falseElimValue levels := (agree _ _ present.2 levels).trans (h.falseElimValue levels)

noncomputable def assignment [DecidableEq β] : Assignment β V := fun r levels =>
  if r = signature.falseType then falseValue
  else if r = signature.falseElim then falseElimValue (levels.getD 0 0)
  else empty

@[simp] theorem assignment_false [DecidableEq β] (levels : List Nat) :
    signature.assignment signature.falseType levels = (empty : V) := by
  simp [assignment, falseValue]

@[simp] theorem assignment_falseElim [DecidableEq β] (levels : List Nat) :
    signature.assignment signature.falseElim levels = (falseElimValue (levels.getD 0 0) : V) := by
  simp [assignment, Ne.symm signature.distinct]

theorem interp_falseElimReading (constants : Assignment β V)
    (hfalse : constants signature.falseType [] = empty)
    (levels : List Nat) (env : Nat → V) :
    interp constants levels env signature.falseElimReading =
      (Model.falseElimType (levels.getD 0 0) : V) := by
  have hz : regime (.param 0) levels = 0 ↔ levels.getD 0 0 = 0 :=
    regime_zeroCondition (.param 0) levels
  simp only [falseElimReading, interp, List.map_nil, hfalse, regime_never,
    VLevel.eval, Valuation.cons_succ, Valuation.cons_zero, Model.falseElimType]
  have hdom : piR 1 (empty : V) (fun _ => univ (levels.getD 0 0)) =
      piR (levels.getD 0 0 + 1) empty (fun _ => univ (levels.getD 0 0)) :=
    piR_zero_agree (by simp) (fun _ _ => rfl)
  rw [hdom]
  apply piR_zero_agree hz
  intro motive _
  exact piR_zero_agree hz (fun _ _ => rfl)

theorem wellDenoted_falseElimReading (constants : Assignment β V)
    (hfalse : constants signature.falseType [] = empty)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted constants levels env signature.falseElimReading := by
  have hz : regime (.param 0) levels = 0 ↔ levels.getD 0 0 = 0 :=
    regime_zeroCondition (.param 0) levels
  simp only [falseElimReading, WellDenoted, interp, List.map_nil, hfalse,
    regime_never, VLevel.eval, Valuation.cons_succ, Valuation.cons_zero]
  refine ⟨⟨trivial, fun _ _ => trivial, levels.getD 0 0 + 1, by simp,
    fun _ _ => univ_mem_univ _⟩, ?_, levels.getD 0 0, hz, ?_⟩
  · intro motive _
    exact ⟨trivial, fun x hx => (not_mem_empty x hx).elim, levels.getD 0 0, hz,
      fun x hx => (not_mem_empty x hx).elim⟩
  · intro motive _
    have hpi := piR_mem_univ (V := V) (a := 0) (b := levels.getD 0 0)
      (B := fun x => app motive x) (empty_mem_univ 0)
      (fun x hx => (not_mem_empty x hx).elim)
    rw [← piR_zero_agree hz (fun _ _ => rfl)] at hpi
    have hi : VLevel.natIMax 0 (levels.getD 0 0) = levels.getD 0 0 := by
      unfold VLevel.natIMax
      split
      · exact Eq.symm ‹_ = 0›
      · exact Nat.zero_max _
    simpa only [hi] using hpi

/-- A produced interpretation of the fixed, two-entry prelude. All later
declaration extensions must preserve these exact values. -/
theorem realizes [DecidableEq β] :
    Realizes (signature.assignment : Assignment β V) signature.environment := by
  constructor
  · intro r entry h levels _ env
    unfold environment at h
    split at h
    next hr =>
      cases Option.some.inj h
      exact trivial
    next hr =>
      split at h
      next he =>
        cases Option.some.inj h
        exact signature.wellDenoted_falseElimReading _ (signature.assignment_false []) levels env
      next => contradiction
  · intro r entry h levels _ env
    unfold environment at h
    split at h
    next hr =>
      subst r
      cases Option.some.inj h
      simpa only [assignment_false, falseEntry, interp, VLevel.eval] using
        (empty_mem_univ 0 : (empty : V) ∈ˢ univ 0)
    next hr =>
      split at h
      next he =>
        subst r
        cases Option.some.inj h
        simp only [falseElimEntry, assignment_falseElim,
          interp_falseElimReading _ _ (signature.assignment_false [])]
        exact falseElimValue_mem _
      next => contradiction
  · intro r entry h body hb levels _ env
    unfold environment at h
    split at h
    · cases Option.some.inj h; contradiction
    · split at h
      · cases Option.some.inj h; contradiction
      · contradiction

  · intro r entry h body hb levels _ env
    unfold environment at h
    split at h
    · cases Option.some.inj h; contradiction
    · split at h
      · cases Option.some.inj h; contradiction
      · contradiction

  · intro r entry h equation he
    simp only [signature.environment_equations h, List.not_mem_nil] at he

  · intro r entry h fact hf
    simp only [signature.environment_facts h, List.not_mem_nil] at hf

theorem compatible_assignment [DecidableEq β] :
    signature.Compatible signature.environment (signature.assignment : Assignment β V) :=
  ⟨signature.realizes, signature.assignment_false, signature.assignment_falseElim⟩

theorem environment_wf [DecidableEq β] : signature.environment.WF := by
  have hrefs : signature.falseElimReading.ReferencesIn signature.environment := by
    intro r hr
    simp only [falseElimReading, AExpr.references, List.append_nil,
      List.mem_append, List.mem_singleton, or_self] at hr
    subst r
    simp
  constructor
  · intro r entry h
    unfold environment at h
    split at h
    · cases Option.some.inj h; exact trivial
    · split at h
      · cases Option.some.inj h; exact signature.falseElimReading_scoped
      · contradiction
  · intro r entry h body hb
    unfold environment at h
    split at h
    · cases Option.some.inj h; contradiction
    · split at h
      · cases Option.some.inj h; contradiction
      · contradiction
  · intro r entry h
    unfold environment at h
    split at h
    · cases Option.some.inj h
      simp [falseEntry, AExpr.ReferencesIn, AExpr.references]
    · split at h
      · cases Option.some.inj h; exact hrefs
      · contradiction
  · intro r entry h body hb
    unfold environment at h
    split at h
    · cases Option.some.inj h; contradiction
    · split at h
      · cases Option.some.inj h; contradiction
      · contradiction
  · intro r entry h equation he
    simp only [signature.environment_equations h, List.not_mem_nil] at he
  · intro r entry h equation he
    simp only [signature.environment_equations h, List.not_mem_nil] at he
  · intro r entry h fact hf
    simp only [signature.environment_facts h, List.not_mem_nil] at hf
  · intro r entry h fact hf
    simp only [signature.environment_facts h, List.not_mem_nil] at hf

end PrimitiveSignature

end Ix.Theory.Certified
