/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/ExprSubstitution.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
`letE` added (2026-09-17): the let-binding constructor, interpreted by
substitution, with its cases in every definition and proof here.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Expr

/-!
# Substitution through erased lets

The structural reader eliminates a let by substitution. These syntactic
identities allow context extension and production substitution to commute
with that elimination, including inside dependent binders. The proofs use
the anonymous model syntax directly and include projections and literals.
-/

namespace Ix.Kernel

universe u
variable {β : Type u}

theorem liftVar_lt {i k n : Nat} (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le {i k n : Nat} (h : k ≤ i) : liftVar n i k = n + i :=
  if_neg (Nat.not_lt.mpr h)

namespace VExpr

@[simp] theorem liftN_zero (e : VExpr β) (k : Nat) : e.liftN 0 k = e := by
  induction e generalizing k <;> simp_all [liftN, liftVar]

theorem liftN_combine {e : VExpr β} {n₁ n₂ k₁ k₂ : Nat}
    (lower : k₁ ≤ k₂) (upper : k₂ ≤ n₁ + k₁) :
    (e.liftN n₁ k₁).liftN n₂ k₂ = e.liftN (n₁ + n₂) k₁ := by
  induction e generalizing k₁ k₂ with
  | bvar i =>
      simp only [liftN, liftVar, VExpr.bvar.injEq]
      split <;> split <;> omega
  | lam _ _ hA hb | forallE _ _ hA hb =>
      simp only [liftN, hA lower upper,
        hb (k₁ := k₁ + 1) (k₂ := k₂ + 1) (by omega) (by omega)]
  | letE _ _ _ ht hv hb =>
      simp only [liftN, ht lower upper, hv lower upper,
        hb (k₁ := k₁ + 1) (k₂ := k₂ + 1) (by omega) (by omega)]
  | _ => simp_all [liftN]

theorem liftN_comm (e : VExpr β) (n₁ n₂ k₁ k₂ : Nat) (order : k₂ ≤ k₁) :
    (e.liftN n₁ k₁).liftN n₂ k₂ = (e.liftN n₂ k₂).liftN n₁ (n₂ + k₁) := by
  induction e generalizing k₁ k₂ with
  | bvar i =>
      simp only [liftN, liftVar, VExpr.bvar.injEq]
      split <;> split <;> (try split) <;> (try split) <;> omega
  | lam _ _ hA hb | forallE _ _ hA hb =>
      simp only [liftN, hA k₁ k₂ order, Nat.add_assoc,
        hb (k₁ + 1) (k₂ + 1) (by omega)]
  | letE _ _ _ ht hv hb =>
      simp only [liftN, ht k₁ k₂ order, hv k₁ k₂ order, Nat.add_assoc,
        hb (k₁ + 1) (k₂ + 1) (by omega)]
  | _ => simp_all [liftN]

theorem liftN_instVar_lo (n : Nat) (e : VExpr β) (i j k : Nat) (order : k ≤ j) :
    (instVar i e j).liftN n k = instVar (liftVar n i k) e (n + j) := by
  simp only [instVar]
  split <;> rename_i before
  · rw [if_pos]
    · rfl
    · simp only [liftVar]; split <;> omega
  split <;> rename_i equal
  · subst i
    rw [liftN_combine (Nat.zero_le _) order, liftVar_le order,
      if_neg (by omega), if_pos rfl, Nat.add_comm]
  · have greater : j < i := by omega
    rw [liftVar_le (by omega : k ≤ i), if_neg (by omega), if_neg (by omega)]
    simp only [liftN, liftVar_le (by omega : k ≤ i - 1), VExpr.bvar.injEq]
    omega

theorem liftN_inst_lo (n : Nat) (e a : VExpr β) (j k : Nat) (order : k ≤ j) :
    (e.inst a j).liftN n k = (e.liftN n k).inst a (n + j) := by
  induction e generalizing j k with
  | bvar i => exact liftN_instVar_lo n a i j k order
  | lam _ _ hA hb | forallE _ _ hA hb =>
      simp only [inst, liftN, hA j k order, hb (j + 1) (k + 1) (by omega), Nat.add_assoc]
  | letE _ _ _ ht hv hb =>
      simp only [inst, liftN, ht j k order, hv j k order, hb (j + 1) (k + 1) (by omega), Nat.add_assoc]
  | _ => simp_all [inst, liftN]

theorem liftN_instVar_hi (i : Nat) (a : VExpr β) (n k j : Nat) :
    (instVar i a j).liftN n (k + j) =
      instVar (liftVar n i (k + j + 1)) (a.liftN n k) j := by
  simp only [instVar]
  split <;> rename_i before
  · rw [liftVar_lt (by omega : i < k + j + 1), if_pos before]
    simp [liftN, liftVar_lt (by omega : i < k + j)]
  split <;> rename_i equal
  · subst i
    simp only [liftVar_lt (by omega : j < k + j + 1), Nat.lt_irrefl,
      if_false, if_true]
    rw [liftN_comm a n j k 0 (Nat.zero_le _), Nat.add_comm]
  · by_cases cut : i < k + j + 1
    · rw [liftVar_lt cut, if_neg before, if_neg equal]
      simp [liftN, liftVar_lt (by omega : i - 1 < k + j)]
    · rw [liftVar_le (by omega : k + j + 1 ≤ i), if_neg (by omega), if_neg (by omega)]
      simp only [liftN, liftVar_le (by omega : k + j ≤ i - 1), VExpr.bvar.injEq]
      omega

theorem liftN_inst_hi_at (e a : VExpr β) (n k j : Nat) :
    (e.inst a j).liftN n (k + j) =
      (e.liftN n (k + j + 1)).inst (a.liftN n k) j := by
  induction e generalizing j with
  | bvar i => exact liftN_instVar_hi i a n k j
  | lam _ _ hA hb | forallE _ _ hA hb =>
      simp only [inst, liftN, hA, Nat.add_assoc, hb]
  | letE _ _ _ ht hv hb =>
      simp only [inst, liftN, ht, hv, Nat.add_assoc, hb]
  | _ => simp_all [inst, liftN]

theorem liftN_inst_hi (e a : VExpr β) (n k : Nat) :
    (e.inst a).liftN n k = (e.liftN n (k + 1)).inst (a.liftN n k) :=
  liftN_inst_hi_at e a n k 0

theorem inst_liftN (e a : VExpr β) (k : Nat) : (e.liftN 1 k).inst a k = e := by
  induction e generalizing k with
  | bvar i =>
      simp only [liftN, inst, liftVar]
      split <;> rename_i before
      · simp [instVar, before]
      · simp only [instVar, if_neg (by omega : ¬ 1 + i < k),
          if_neg (by omega : 1 + i ≠ k), VExpr.bvar.injEq]
        omega
  | _ => simp_all [liftN, inst]

theorem inst_instVar_hi (i : Nat) (a b : VExpr β) (k j : Nat) :
    (instVar i a k).inst b (j + k) =
      (instVar i b (j + k + 1)).inst (a.inst b j) k := by
  simp only [instVar]
  split <;> rename_i before
  · simp [inst, instVar, before, show i < j + k + 1 by omega,
      show i < j + k by omega]
  split <;> rename_i equal
  · subst i
    simp only [if_pos (by omega : k < j + k + 1), inst, instVar,
      Nat.lt_irrefl, if_false, if_true]
    simpa only [Nat.zero_add, Nat.add_comm] using
      (liftN_inst_lo k a b j 0 (Nat.zero_le _)).symm
  · by_cases below : i < j + k + 1
    · simp [inst, instVar, below, before, equal, show i - 1 < j + k by omega]
    · by_cases sameIndex : i = j + k + 1
      · subst i
        simp only [if_true,
          show j + k + 1 - 1 = j + k by omega, inst, instVar,
          Nat.lt_irrefl, if_false, if_true]
        rw [← liftN_combine (e := b) (n₁ := j + k) (n₂ := 1)
          (k₁ := 0) (k₂ := k) (by omega) (by omega), inst_liftN]
      · simp only [if_neg below, if_neg sameIndex, inst, instVar,
          if_neg (by omega : ¬ i - 1 < j + k), if_neg (by omega : i - 1 ≠ j + k),
          if_neg (by omega : ¬ i - 1 < k), if_neg (by omega : i - 1 ≠ k)]

theorem inst_inst_hi (e a b : VExpr β) (k j : Nat) :
    (e.inst a k).inst b (j + k) =
      (e.inst b (j + k + 1)).inst (a.inst b j) k := by
  induction e generalizing k with
  | bvar i => exact inst_instVar_hi i a b k j
  | lam _ _ hA hb | forallE _ _ hA hb =>
      simp only [inst, hA, Nat.add_assoc, hb]
  | letE _ _ _ ht hv hb =>
      simp only [inst, ht, hv, Nat.add_assoc, hb]
  | _ => simp_all [inst]

theorem inst0_inst_hi (e a b : VExpr β) (j : Nat) :
    (e.inst a).inst b j = (e.inst b (j + 1)).inst (a.inst b j) :=
  inst_inst_hi e a b 0 j

end VExpr
end Ix.Kernel
