/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.LevelEq
import Ix.Kernel.Certified.LevelNorm

/-! # Universe level comparison for the checker

Levels are compared by Géran's sublevel domination
(`Certified.LevelNorm.levelLe`), which decides the pointwise order under every
valuation: equivalence is the order both ways, and a level is zero when it is
at most `zero`. Each check is sound and complete (`levelEquiv_iff`,
`levelIsZero_iff`), so a failed comparison is a real difference, not a
limitation of the search. The previous conservative check
(`Certified.LevelEq.normalize`) is retained in its ported module; the checker
no longer uses it. -/

namespace Ix.Kernel

open Certified

/-- Equivalence of universe levels under every valuation: structural equality,
or the order both ways. -/
def levelEquiv (a b : VLevel) : Bool :=
  a == b || (LevelNorm.levelLe a b && LevelNorm.levelLe b a)

theorem levelEquiv_sound {a b : VLevel} (h : levelEquiv a b = true) (values : List Nat) :
    a.eval values = b.eval values := by
  simp only [levelEquiv, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with rfl | ⟨hab, hba⟩
  · rfl
  · exact Nat.le_antisymm (LevelNorm.levelLe_sound hab values) (LevelNorm.levelLe_sound hba values)

theorem levelEquiv_complete {a b : VLevel} (h : ∀ values, a.eval values = b.eval values) :
    levelEquiv a b = true := by
  simp only [levelEquiv, Bool.or_eq_true, Bool.and_eq_true]
  exact .inr ⟨LevelNorm.levelLe_complete fun ls => Nat.le_of_eq (h ls),
    LevelNorm.levelLe_complete fun ls => Nat.le_of_eq (h ls).symm⟩

/-- `levelEquiv` decides equivalence of levels. -/
theorem levelEquiv_iff {a b : VLevel} :
    levelEquiv a b = true ↔ ∀ values, a.eval values = b.eval values :=
  ⟨fun h values => levelEquiv_sound h values, levelEquiv_complete⟩

/-- Pointwise equivalence of two level lists of the same length. -/
def levelsEquiv : List VLevel → List VLevel → Bool
  | [], [] => true
  | a :: as, b :: bs => levelEquiv a b && levelsEquiv as bs
  | _, _ => false

theorem levelsEquiv_sound : ∀ {ls ls' : List VLevel}, levelsEquiv ls ls' = true →
    ∀ values, ls.map (VLevel.eval values) = ls'.map (VLevel.eval values)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, h, values => by
    simp only [levelsEquiv, Bool.and_eq_true] at h
    simp only [List.map_cons, levelEquiv_sound h.1 values, levelsEquiv_sound h.2 values]
  | [], _ :: _, h, _ => by simp [levelsEquiv] at h
  | _ :: _, [], h, _ => by simp [levelsEquiv] at h

theorem levelsEquiv_length : ∀ {ls ls' : List VLevel}, levelsEquiv ls ls' = true →
    ls.length = ls'.length
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [levelsEquiv, Bool.and_eq_true] at h
    simp [levelsEquiv_length h.2]
  | [], _ :: _, h => by simp [levelsEquiv] at h
  | _ :: _, [], h => by simp [levelsEquiv] at h

/-- Whether a level is zero at every valuation, i.e. the sort is `Prop` at
every instance. -/
def levelIsZero (l : VLevel) : Bool := LevelNorm.levelLe l .zero

theorem levelIsZero_sound {l : VLevel} (h : levelIsZero l = true) (values : List Nat) :
    l.eval values = 0 :=
  Nat.le_zero.1 (LevelNorm.levelLe_sound h values)

/-- `levelIsZero` decides whether a level is zero at every valuation. -/
theorem levelIsZero_iff {l : VLevel} : levelIsZero l = true ↔ ∀ values, l.eval values = 0 :=
  ⟨fun h values => levelIsZero_sound h values, fun h =>
    LevelNorm.levelLe_complete fun ls => Nat.le_of_eq (h ls)⟩

end Ix.Kernel
