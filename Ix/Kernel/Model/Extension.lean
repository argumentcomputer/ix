/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Extension.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Support
import Ix.Kernel.Model.Judgment

namespace Ix.Kernel.Model

open SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

def Environment.insert (entries : Environment β) (r : ConstRef β)
    (entry : ConstantEntry β) : Environment β :=
  fun q => if q = r then some entry else entries q

def Assignment.insert (constants : Assignment β V) (r : ConstRef β)
    (value : List Nat → V) : Assignment β V :=
  fun q levels => if q = r then value levels else constants q levels

/-- All exact old references retain their values at every universe instance. -/
def Assignment.AgreesOn (entries : Environment β) (constants constants' : Assignment β V) : Prop :=
  ∀ r entry, entries r = some entry → ∀ levels, constants' r levels = constants r levels

@[simp] theorem Environment.insert_same (entries : Environment β) (r : ConstRef β)
    (entry : ConstantEntry β) : entries.insert r entry r = some entry := by
  simp only [insert, ↓reduceIte]

theorem Environment.insert_replace (entries : Environment β) (r : ConstRef β)
    (old entry : ConstantEntry β) : (entries.insert r old).insert r entry = entries.insert r entry := by
  funext q
  by_cases h : q = r <;> simp [insert, h]

@[simp] theorem Assignment.insert_same (constants : Assignment β V) (r : ConstRef β)
    (value : List Nat → V) (levels : List Nat) :
    constants.insert r value r levels = value levels := by
  simp only [insert, ↓reduceIte]

omit [DecidableEq β] in
theorem fresh_ne {entries : Environment β} {r q : ConstRef β} {entry : ConstantEntry β}
    (fresh : entries r = none) (h : entries q = some entry) : q ≠ r := by
  intro hqr
  subst q
  rw [fresh] at h
  contradiction

theorem Environment.insert_old {entries : Environment β} {r q : ConstRef β}
    {entry old : ConstantEntry β} (fresh : entries r = none) (h : entries q = some old) :
    entries.insert r entry q = some old := by
  simp only [insert, if_neg (fresh_ne fresh h), h]

theorem Assignment.insert_agrees {entries : Environment β} {r : ConstRef β}
    (fresh : entries r = none) (constants : Assignment β V) (value : List Nat → V) :
    Assignment.AgreesOn entries constants (constants.insert r value) := by
  intro q entry h levels
  simp only [Assignment.insert, if_neg (fresh_ne fresh h)]

theorem AExpr.ReferencesIn.insert {entries : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} {e : AExpr β} (h : e.ReferencesIn entries) :
    e.ReferencesIn (entries.insert r entry) := by
  intro q hq
  unfold Environment.insert
  split
  · rfl
  · exact h q hq

theorem ConstantFact.ReferencesIn.insert {entries : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} {fact : ConstantFact β} (h : fact.ReferencesIn entries) :
    fact.ReferencesIn (entries.insert r entry) := by
  intro q hq
  unfold Environment.insert
  split
  · rfl
  · exact h q hq

theorem Environment.WF.insert {entries : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} (hE : entries.WF)
    (hTs : entry.type.Scope entry.universes 0)
    (hBs : ∀ body, entry.body = some body → body.Scope entry.universes 0)
    (hTr : entry.type.ReferencesIn entries)
    (hBr : ∀ body, entry.body = some body → body.ReferencesIn entries)
    (hQs : ∀ equation ∈ entry.equations,
      equation.lhs.Scope entry.universes 0 ∧ equation.rhs.Scope entry.universes 0)
    (hQr : ∀ equation ∈ entry.equations,
      equation.lhs.ReferencesIn entries ∧ equation.rhs.ReferencesIn entries)
    (hFs : ∀ fact ∈ entry.facts, fact.Scope entry.universes)
    (hFr : ∀ fact ∈ entry.facts, fact.ReferencesIn entries) :
    (entries.insert r entry).WF := by
  constructor
  · intro q old h
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact hTs
    · exact hE.typeScope q old h
  · intro q old h body hb
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact hBs body hb
    · exact hE.bodyScope q old h body hb
  · intro q old h
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact hTr.insert
    · exact (hE.typeReferences q old h).insert
  · intro q old h body hb
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact (hBr body hb).insert
    · exact (hE.bodyReferences q old h body hb).insert
  · intro q old h equation he
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact hQs equation he
    · exact hE.equationScope q old h equation he
  · intro q old h equation he
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h
      exact ⟨(hQr equation he).1.insert, (hQr equation he).2.insert⟩
    · exact ⟨(hE.equationReferences q old h equation he).1.insert,
        (hE.equationReferences q old h equation he).2.insert⟩
  · intro q old h fact hf
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact hFs fact hf
    · exact hE.factScope q old h fact hf
  · intro q old h fact hf
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h; exact (hFr fact hf).insert
    · exact (hE.factReferences q old h fact hf).insert

variable {V : Type v} [SetTheory V]

omit [DecidableEq β] in
theorem Assignment.AgreesOn.interp {entries : Environment β}
    {constants constants' : Assignment β V}
    (h : Assignment.AgreesOn entries constants constants')
    {e : AExpr β} (he : e.ReferencesIn entries) (levels : List Nat) (env : Nat → V) :
    interp constants' levels env e = interp constants levels env e := by
  apply interp_congr_constants
  intro r hr ls
  have hl := he r hr
  cases hE : entries r with
  | none => simp [hE] at hl
  | some entry => exact h r entry hE ls

omit [DecidableEq β] in
theorem Assignment.AgreesOn.wellDenoted {entries : Environment β}
    {constants constants' : Assignment β V}
    (h : Assignment.AgreesOn entries constants constants')
    {e : AExpr β} (he : e.ReferencesIn entries) (levels : List Nat) (env : Nat → V) :
    WellDenoted constants' levels env e ↔ WellDenoted constants levels env e := by
  apply wellDenoted_congr_constants
  intro r hr ls
  have hl := he r hr
  cases hE : entries r with
  | none => simp [hE] at hl
  | some entry => exact h r entry hE ls

omit [DecidableEq β] in
theorem Assignment.AgreesOn.factMeaning {entries : Environment β}
    {constants constants' : Assignment β V} (h : Assignment.AgreesOn entries constants constants')
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry)
    {fact : ConstantFact β} (hf : fact.ReferencesIn entries) (levels : List Nat) (env : Nat → V)
    (hm : fact.Meaning constants r levels env) : fact.Meaning constants' r levels env := by
  have heq (q) (hq : q ∈ fact.references) (ls) : constants' q ls = constants q ls := by
    have hv := hf q hq
    cases he : entries q with
    | none => simp [he] at hv
    | some value => exact h q value he ls
  cases fact with
  | typed e type =>
    have her : e.ReferencesIn entries := fun q hq => hf q (List.mem_append_left _ hq)
    have htr : type.ReferencesIn entries := fun q hq => hf q (List.mem_append_right _ hq)
    simpa only [ConstantFact.Meaning, h.wellDenoted her, h.wellDenoted htr,
      h.interp her, h.interp htr] using hm
  | natural zero succ =>
    refine ⟨hm.1, ?_⟩
    have hz := heq zero (by simp [ConstantFact.references]) []
    have hs := heq succ (by simp [ConstantFact.references]) []
    constructor
    · intro n; rw [h r entry hr []]; exact hm.2.member n
    · intro x; rw [h r entry hr []]; exact hm.2.complete x
    · rw [hz]; exact hm.2.zeroValue
    · intro n; rw [hs]; exact hm.2.succValue n

omit [DecidableEq β] in
theorem Realizes.of_agrees {entries : Environment β} {constants constants' : Assignment β V}
    (hM : Realizes constants entries) (hE : entries.WF)
    (h : Assignment.AgreesOn entries constants constants') : Realizes constants' entries where
  typeValid r entry hr levels hn env :=
    (h.wellDenoted (hE.typeReferences r entry hr) levels env).mpr (hM.typeValid r entry hr levels hn env)
  member r entry hr levels hn env := by
    rw [h r entry hr levels, h.interp (hE.typeReferences r entry hr) levels env]
    exact hM.member r entry hr levels hn env
  bodyValid r entry hr body hb levels hn env :=
    (h.wellDenoted (hE.bodyReferences r entry hr body hb) levels env).mpr
      (hM.bodyValid r entry hr body hb levels hn env)
  bodyValue r entry hr body hb levels hn env := by
    rw [h r entry hr levels, h.interp (hE.bodyReferences r entry hr body hb) levels env]
    exact hM.bodyValue r entry hr body hb levels hn env
  equationValue r entry hr law hl levels hn env := by
    rw [h.interp (hE.equationReferences r entry hr law hl).1 levels env,
      h.interp (hE.equationReferences r entry hr law hl).2 levels env]
    exact hM.equationValue r entry hr law hl levels hn env
  factMeaning r entry hr fact hf levels hn env :=
    h.factMeaning hr (hE.factReferences r entry hr fact hf) levels env
      (hM.factMeaning r entry hr fact hf levels hn env)

/-- Local mathematical realization package. Admission constructs every field;
certificate data cannot supply this proof package. -/
structure EntryRealization (constants : Assignment β V) (r : ConstRef β)
    (entry : ConstantEntry β) : Prop where
  typeValid : ∀ levels, levels.length = entry.universes → ∀ env,
    WellDenoted constants levels env entry.type
  member : ∀ levels, levels.length = entry.universes → ∀ env,
    constants r levels ∈ˢ interp constants levels env entry.type
  bodyValid : ∀ body, entry.body = some body → ∀ levels, levels.length = entry.universes → ∀ env,
    WellDenoted constants levels env body
  bodyValue : ∀ body, entry.body = some body → ∀ levels, levels.length = entry.universes → ∀ env,
    constants r levels = interp constants levels env body
  equationValue : ∀ law ∈ entry.equations, ∀ levels, levels.length = entry.universes → ∀ env,
    interp constants levels env law.lhs = interp constants levels env law.rhs
  factMeaning : ∀ fact ∈ entry.facts, ∀ levels, levels.length = entry.universes → ∀ env,
    fact.Meaning constants r levels env

theorem Realizes.insert {entries : Environment β} {constants : Assignment β V}
    {r : ConstRef β} {entry : ConstantEntry β} (hM : Realizes constants entries)
    (h : EntryRealization constants r entry) : Realizes constants (entries.insert r entry) := by
  constructor
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    · cases Option.some.inj hq; exact h.typeValid
    · exact hM.typeValid q old hq
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    next he => subst q; cases Option.some.inj hq; exact h.member
    next => exact hM.member q old hq
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    · cases Option.some.inj hq; exact h.bodyValid
    · exact hM.bodyValid q old hq
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    next he => subst q; cases Option.some.inj hq; exact h.bodyValue
    next => exact hM.bodyValue q old hq
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    · cases Option.some.inj hq; exact h.equationValue
    · exact hM.equationValue q old hq
  · intro q old hq
    unfold Environment.insert at hq
    split at hq
    next he => subst q; cases Option.some.inj hq; exact h.factMeaning
    next => exact hM.factMeaning q old hq

/-- Safe-definition admission extends every compatible old model. The new
value is constructed from the checked body in that very model. -/
theorem extend_definition {entries : Environment β} {r : ConstRef β}
    {entry : ConstantEntry β} {body : AExpr β} {level : VLevel}
    (hE : entries.WF) (fresh : entries r = none) (hb : entry.body = some body)
    (hq : entry.equations = []) (hf : entry.facts = [])
    (hBs : body.Scope entry.universes 0)
    (hTr : entry.type.ReferencesIn entries) (hBr : body.ReferencesIn entries)
    (hT : TypingClaim.{u,v} entries [] entry.type (.sort level))
    (hB : TypingClaim.{u,v} entries [] body entry.type)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    ∃ constants' : Assignment β V,
      Realizes constants' (entries.insert r entry) ∧
        Assignment.AgreesOn entries constants constants' := by
  let constants' := constants.insert r (fun levels => interp constants levels (fun _ => empty) body)
  have hagree : Assignment.AgreesOn entries constants constants' := by
    intro q old h levels
    simp only [constants', Assignment.insert, if_neg (fresh_ne fresh h)]
  have hnew (levels : List Nat) (env : Nat → V) :
      constants' r levels = interp constants levels env body := by
    simp only [constants', Assignment.insert, ↓reduceIte]
    exact interp_closed body constants levels hBs _ env
  refine ⟨constants', ?_, hagree⟩
  constructor
  · intro q old h levels _ env
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h
      exact (hagree.wellDenoted hTr levels env).mpr
        (hT V constants hM levels env (Context.valid_nil constants levels env)).1
    · exact (hagree.wellDenoted (hE.typeReferences q old h) levels env).mpr
        (hM.typeValid q old h levels ‹_› env)
  · intro q old h levels _ env
    unfold Environment.insert at h
    split at h
    next hqr =>
      subst q
      cases Option.some.inj h
      rw [hnew levels env, hagree.interp hTr levels env]
      exact (hB V constants hM levels env (Context.valid_nil constants levels env)).2.2
    next =>
      rw [hagree q old h levels, hagree.interp (hE.typeReferences q old h) levels env]
      exact hM.member q old h levels ‹_› env
  · intro q old h b hb' levels _ env
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h
      have he : body = b := Option.some.inj (hb.symm.trans hb')
      subst b
      exact (hagree.wellDenoted hBr levels env).mpr
        (hB V constants hM levels env (Context.valid_nil constants levels env)).1
    · exact (hagree.wellDenoted (hE.bodyReferences q old h b hb') levels env).mpr
        (hM.bodyValid q old h b hb' levels ‹_› env)
  · intro q old h b hb' levels _ env
    unfold Environment.insert at h
    split at h
    next hqr =>
      subst q
      cases Option.some.inj h
      have he : body = b := Option.some.inj (hb.symm.trans hb')
      subst b
      rw [hnew levels env, hagree.interp hBr levels env]
    next =>
      rw [hagree q old h levels, hagree.interp (hE.bodyReferences q old h b hb') levels env]
      exact hM.bodyValue q old h b hb' levels ‹_› env
  · intro q old h equation he levels hn env
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h
      simp only [hq, List.not_mem_nil] at he
    · rw [hagree.interp (hE.equationReferences q old h equation he).1 levels env,
        hagree.interp (hE.equationReferences q old h equation he).2 levels env]
      exact hM.equationValue q old h equation he levels hn env
  · intro q old h fact hfact levels hn env
    unfold Environment.insert at h
    split at h
    · cases Option.some.inj h
      simp only [hf, List.not_mem_nil] at hfact
    · exact hagree.factMeaning h (hE.factReferences q old h fact hfact) levels env
        (hM.factMeaning q old h fact hfact levels hn env)

end Ix.Kernel.Model
