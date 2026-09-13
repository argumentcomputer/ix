/-
Adapted for Ix: shared universe semantics and additional proof support.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.VLevel
import Ix.Theory.Named.Std.Basic

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
export Lean (Name)
end Ix.Theory.Named

namespace Ix.Theory.VLevel
open Ix.Theory.Named

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

variable (ls : List Name) in
def ofLevel : Lean.Level → Option VLevel
  | .zero => return .zero
  | .succ l => return .succ (← ofLevel l)
  | .max l₁ l₂ => return .max (← ofLevel l₁) (← ofLevel l₂)
  | .imax l₁ l₂ => return .imax (← ofLevel l₁) (← ofLevel l₂)
  | .param n =>
    let i := ls.idxOf n
    if i < ls.length then some (.param i) else none
  | .mvar _ => none

theorem WF.of_ofLevel (h : ofLevel ls l = some l') : l'.WF ls.length := by
  induction l generalizing l' with simp [ofLevel, bind] at h
  | zero => cases h; trivial
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact @ih l' h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩
  | param n => exact h.2 ▸ h.1

theorem WF.of_mapM_ofLevel (h : List.mapM (VLevel.ofLevel Us) us = some us')
    (a) (hl : a ∈ us') : VLevel.WF Us.length a := by
  rw [List.mapM_eq_some] at h
  have ⟨_, _, h⟩ := h.forall_exists_r _ hl; exact .of_ofLevel h

end Ix.Theory.VLevel

/-- The internal universe operation agrees definitionally with Lean's
natural-number operation used by the reference implementation proofs. -/
@[simp] theorem Ix.Theory.VLevel.natIMax_eq_core (a b : Nat) :
    Ix.Theory.VLevel.natIMax a b = Lean.Nat.imax a b := rfl
