/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.LevelEq

/-! # Universe level equivalence for the checker

Level equivalence is decided by normalization (`Certified.LevelEq.normalize`,
ported from the old branch): a conservative check whose success implies equal
evaluation under every valuation, which is what the semantic rules for `sort`
and `const` need. Failure declines. -/

namespace Ix.Kernel

open Certified

/-- Sound and conservative equivalence of universe levels. -/
def levelEquiv (a b : VLevel) : Bool :=
  decide (LevelEq.normalize a = LevelEq.normalize b)

theorem levelEquiv_sound {a b : VLevel} (h : levelEquiv a b = true) (values : List Nat) :
    a.eval values = b.eval values := by
  have h' : LevelEq.normalize a = LevelEq.normalize b := by simpa [levelEquiv] using h
  rw [← LevelEq.eval_normalize a values, ← LevelEq.eval_normalize b values, h']

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

/-- Whether a level is equivalent to zero, i.e. the sort is `Prop` at every instance. -/
def levelIsZero (l : VLevel) : Bool := levelEquiv l .zero

theorem levelIsZero_sound {l : VLevel} (h : levelIsZero l = true) (values : List Nat) :
    l.eval values = 0 :=
  levelEquiv_sound h values

end Ix.Kernel
