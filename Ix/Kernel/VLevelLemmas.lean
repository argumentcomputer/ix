/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/VLevelLemmas.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Level
import Ix.Kernel.VLevel

/-!
# Additional universe-level lemmas

Order, equivalence, and well-formedness facts about the shared `VLevel`
semantics, together with the definitional bridge to Lean's natural-number
`imax`. Everything here is stated over `Ix.Kernel.VLevel` alone, so the
kernel proofs can use these lemmas without importing any module of the
named specification, which is being retired. The named-parameter conversion
`ofLevel` stays with that specification in `Ix.Kernel.Named.VLevel`.
-/

namespace Ix.Kernel.VLevel

theorem le_trans {a b c : VLevel} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun _ => Nat.le_trans (h1 _) (h2 _)

theorem zero_le : zero ≤ a := fun _ => Nat.zero_le _

theorem le_succ : a ≤ succ a := fun _ => Nat.le_succ _

theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := fun _ => Nat.succ_le_succ (h _)

theorem le_max_left : a ≤ max a b := fun _ => Nat.le_max_left ..
theorem le_max_right : b ≤ max a b := fun _ => Nat.le_max_right ..

theorem equiv_def' {a b : VLevel} : a ≈ b ↔ a.eval = b.eval := .rfl
theorem equiv_congr_left {a b c : VLevel} (h : a ≈ b) : a ≈ c ↔ b ≈ c :=
  iff_of_eq (congrArg (· = _) h)

theorem equiv_congr_right {a b c : VLevel} (h : a ≈ b) : c ≈ a ↔ c ≈ b :=
  iff_of_eq (congrArg (_ = ·) h)

theorem succ_congr_iff {a b : VLevel} : succ a ≈ succ b ↔ a ≈ b := by
  simp [equiv_def, eval]

theorem max_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : max a₁ a₂ ≈ max b₁ b₂ := by
  simp_all [equiv_def, eval]

theorem max_comm : max a b ≈ max b a := by simp [equiv_def, eval, Nat.max_comm]

theorem LE.max_eq_left (h : b.LE a) : max a b ≈ a := by
  simp [equiv_def, eval, Nat.max_eq_left (h _)]

theorem LE.max_eq_right (h : a.LE b) : max a b ≈ b := by
  simp [equiv_def, eval, Nat.max_eq_right (h _)]

theorem max_self : max a a ≈ a := by simp [equiv_def, eval]

theorem zero_imax : imax zero a ≈ a := by
  simp [equiv_def, eval, natIMax, eq_comm (b := 0)]

theorem imax_zero : imax a zero ≈ zero := by simp [equiv_def, eval, natIMax]

theorem imax_eq_zero : imax a b ≈ zero ↔ b ≈ zero := by
  simp [equiv_def, eval, natIMax]
  refine ⟨fun H ls => ?_, fun H ls hn => nomatch hn (H ls)⟩
  exact Decidable.byContradiction fun h => h (H ls h).2

def IsNeverZero (a : VLevel) : Prop := ∀ ls, a.eval ls ≠ 0

theorem IsNeverZero.imax_eq_max (h : IsNeverZero b) : imax a b ≈ max a b := by
  simp_all [equiv_def, eval, natIMax, IsNeverZero]

theorem id_WF : ∀ l ∈ (List.range u).map param, l.WF u := by simp [WF]

end Ix.Kernel.VLevel

/-- The internal universe operation agrees definitionally with Lean's
natural-number operation used by the reference implementation proofs. -/
@[simp] theorem Ix.Kernel.VLevel.natIMax_eq_core (a b : Nat) :
    Ix.Kernel.VLevel.natIMax a b = Lean.Nat.imax a b := rfl
