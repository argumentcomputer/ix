/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Standard/Checked.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store, the witness, and the typing witness are removed; the
checked facts are about a reference and a spec, and the type is checked by
inference (`checkSort`) in place of witness validation.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Standard.Realization
import Ix.Kernel.Certified.Checker

namespace Ix.Kernel.Certified.Standard

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure Checked (entries : Environment β) (ref : ConstRef β) (spec : Spec β) : Prop where
  fresh : entries ref = none
  prerequisites : spec.Prerequisites entries
  scope : spec.type.Scope spec.universes 0
  references : spec.type.ReferencesIn entries
  typing : ∃ level, TypingClaim.{u,v} entries [] spec.type (.sort level)

def check (fuel : Nat) (entries : Environment β) (ref : ConstRef β) (spec : Spec β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries ref spec)) :=
  if hf : entries ref = none then
    if hp : spec.Prerequisites entries then
      if hc : spec.type.Scope spec.universes 0 then
        if hr : spec.type.ReferencesIn entries then
          match checkSort.{u,v} fuel entries [] spec.type with
          | some ⟨level, ht⟩ => some ⟨⟨hf, hp, hc, hr, ⟨level, ht⟩⟩⟩
          | none => none
        else none
      else none
    else none
  else none

variable {entries : Environment β} {ref : ConstRef β} {spec : Spec β}

theorem environment_wf (h : Checked.{u,v} entries ref spec) (hE : entries.WF) :
    (entries.insert ref spec.entry).WF := by
  apply hE.insert h.scope (by simp [Spec.entry]) h.references
    (by simp [Spec.entry]) (by simp [Spec.entry]) (by simp [Spec.entry])
    (by simp [Spec.entry]) (by simp [Spec.entry])

variable {V : Type v} [SetTheory V]

noncomputable def assignment (constants : Assignment β V) (ref : ConstRef β) (spec : Spec β) :
    Assignment β V :=
  constants.insert ref (spec.value constants)

theorem assignment_agrees (h : Checked.{u,v} entries ref spec) (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (assignment constants ref spec) :=
  Assignment.insert_agrees h.fresh _ _

theorem assignment_realizes (h : Checked.{u,v} entries ref spec) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (assignment constants ref spec) (entries.insert ref spec.entry) := by
  have ha := assignment_agrees h constants
  obtain ⟨level, ht⟩ := h.typing
  apply (hM.of_agrees hE ha).insert
  constructor
  · intro levels hn env
    exact (ht V (assignment constants ref spec) (hM.of_agrees hE ha) levels env
      (Context.valid_nil (assignment constants ref spec) levels env)).1
  · intro levels hn env
    change (assignment constants ref spec) ref levels ∈ˢ
      interp (assignment constants ref spec) levels env spec.type
    rw [ha.interp h.references]
    rw [assignment, Assignment.insert_same]
    exact spec.value_mem h.prerequisites hM levels hn env
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; simp only [Spec.entry, List.not_mem_nil] at hl
  · intro fact hf; simp only [Spec.entry, List.not_mem_nil] at hf

end Ix.Kernel.Certified.Standard
