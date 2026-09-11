/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Environment

namespace Ix.Theory.Model.Environment

open SetTheory

universe u v
variable {β : Type u}

/-- An exact type interface read from an already admitted entry. Bodies and
equations remain those of that entry; this predicate grants no admission. -/
def HasType (entries : Environment β) (ref : ConstRef β) (n : Nat) (type : AExpr β) : Prop :=
  ∃ entry, entries ref = some entry ∧ entry.universes = n ∧ entry.type = type

instance [DecidableEq β] (entries : Environment β) (ref : ConstRef β) (n : Nat) (type : AExpr β) :
    Decidable (entries.HasType ref n type) :=
  match h : entries ref with
  | none => .isFalse (by rintro ⟨entry, he, _⟩; simp [h] at he)
  | some entry =>
    if he : entry.universes = n ∧ entry.type = type then
      .isTrue ⟨entry, h, he⟩
    else .isFalse (by rintro ⟨other, ho, hu, ht⟩; cases h.symm.trans ho; exact he ⟨hu, ht⟩)

variable {V : Type v} [SetTheory V] {constants : Assignment β V} {entries : Environment β}

theorem HasType.member {ref : ConstRef β} {n : Nat} {type : AExpr β}
    (h : entries.HasType ref n type) (hM : Realizes constants entries)
    {levels : List Nat} (hn : levels.length = n) (env : Nat → V) :
    constants ref levels ∈ˢ interp constants levels env type := by
  obtain ⟨entry, he, rfl, rfl⟩ := h
  exact hM.member ref entry he levels hn env

end Ix.Theory.Model.Environment
