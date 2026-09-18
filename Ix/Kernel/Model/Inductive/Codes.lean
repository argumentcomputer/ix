/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Inductive/Codes.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Inductive.Telescope
import Ix.Kernel.Model.SetModel.TaggedSum

namespace Ix.Kernel.Model.InductiveCodes

open SetTheory SetTheory.Tower

universe u
variable {V : Type u} [SetTheory V]

open Classical in
noncomputable def natIndex (x : V) : Nat :=
  if h : ∃ i, x = vnat i then Classical.choose h else 0

theorem natIndex_vnat (i : Nat) : natIndex (vnat i : V) = i := by
  unfold natIndex
  rw [dif_pos ⟨i, rfl⟩]
  exact (vnat_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ j, (vnat i : V) = vnat j))).symm

noncomputable def tag (x : V) : Nat := natIndex (sfst x)

@[simp] theorem tag_inj (i : Nat) (x : V) : tag (inj i x) = i := by
  simp only [tag, sfst_inj, natIndex_vnat]

theorem sum_graph_mem {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (hf : ∀ i, f i ∈ˢ (univ w : V)) : sumSet 1 f ∈ˢ (univ w : V) := by
  cases w with
  | zero => exact (hw rfl).elim
  | succ w =>
    unfold sumSet
    rw [sigmaSet_pos (by decide : 1 ≠ 0)]
    apply (univ_isTGUniverse hw).sigmaPairs_mem (omega_mem_univ_succ w)
    intro k hk
    obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
    rw [natFibre_vnat]
    exact hf i

end Ix.Kernel.Model.InductiveCodes
