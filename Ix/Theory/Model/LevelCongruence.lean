/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Judgment

/-!
# Replacing universe levels by equivalent levels

Kernel universe substitution uses simplifying constructors. Its result can
therefore differ from structural substitution while denoting the same type.
The relations below retain every term constructor, reference, index, and
binder annotation. Only universe expressions may change, and their values
must agree under every universe valuation.

This congruence preserves hereditary validity as well as interpretation.
Consequently it transports typing without assuming that an arbitrary
semantically equal expression is a valid type.
-/

namespace Ix.Theory

universe u v
variable {β : Type u}

namespace VExpr

/-- Structural equality except for semantically equivalent universe levels. -/
inductive LevelEquivalent : VExpr β → VExpr β → Prop
  | bvar (index) : LevelEquivalent (.bvar index) (.bvar index)
  | sort {left right} (levels : left ≈ right) :
      LevelEquivalent (.sort left) (.sort right)
  | const (ref) {left right}
      (levels : ∀ valuation, left.map (VLevel.eval valuation) =
        right.map (VLevel.eval valuation)) :
      LevelEquivalent (.const ref left) (.const ref right)
  | app {f f' a a'} (fn : LevelEquivalent f f') (arg : LevelEquivalent a a') :
      LevelEquivalent (.app f a) (.app f' a')
  | lam {A A' b b'} (domain : LevelEquivalent A A') (body : LevelEquivalent b b') :
      LevelEquivalent (.lam A b) (.lam A' b')
  | forallE {A A' B B'} (domain : LevelEquivalent A A') (body : LevelEquivalent B B') :
      LevelEquivalent (.forallE A B) (.forallE A' B')
  | proj (ref index) {e e'} (major : LevelEquivalent e e') :
      LevelEquivalent (.proj ref index e) (.proj ref index e')
  | natLit (value) : LevelEquivalent (.natLit value) (.natLit value)

namespace LevelEquivalent

theorem refl (e : VExpr β) : LevelEquivalent e e := by
  induction e with
  | bvar i => exact .bvar i
  | sort l => exact .sort (VLevel.equiv_def.mpr fun _ => rfl)
  | const r ls => exact .const r fun _ => rfl
  | app _ _ hf ha => exact .app hf ha
  | lam _ _ hA hb => exact .lam hA hb
  | forallE _ _ hA hB => exact .forallE hA hB
  | proj r i _ he => exact .proj r i he
  | natLit n => exact .natLit n

theorem liftN {e e' : VExpr β} (h : LevelEquivalent e e') (n k : Nat) :
    LevelEquivalent (e.liftN n k) (e'.liftN n k) := by
  induction h generalizing k with
  | bvar i => exact .bvar _
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ hf ha => exact .app (hf k) (ha k)
  | lam _ _ hA hb => exact .lam (hA k) (hb (k + 1))
  | forallE _ _ hA hB => exact .forallE (hA k) (hB (k + 1))
  | proj r i _ he => exact .proj r i (he k)
  | natLit n => exact .natLit n

theorem inst {e e' a a' : VExpr β} (h : LevelEquivalent e e')
    (ha : LevelEquivalent a a') (k : Nat := 0) :
    LevelEquivalent (e.inst a k) (e'.inst a' k) := by
  induction h generalizing k with
  | bvar i =>
      by_cases hi : i < k
      · simpa [VExpr.inst, instVar, hi] using LevelEquivalent.bvar (β := β) i
      · by_cases hik : i = k
        · simpa [VExpr.inst, instVar, hi, hik] using ha.liftN k 0
        · simpa [VExpr.inst, instVar, hi, hik] using LevelEquivalent.bvar (β := β) (i - 1)
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ hf hb => exact .app (hf k) (hb k)
  | lam _ _ hA hb => exact .lam (hA k) (hb (k + 1))
  | forallE _ _ hA hB => exact .forallE (hA k) (hB (k + 1))
  | proj r i _ he => exact .proj r i (he k)
  | natLit n => exact .natLit n

end LevelEquivalent

theorem instL_liftN (e : VExpr β) (levels : List VLevel) (n k : Nat) :
    (e.liftN n k).instL levels = (e.instL levels).liftN n k := by
  induction e generalizing k <;> simp_all [VExpr.liftN, VExpr.instL]

theorem instL_inst (e a : VExpr β) (levels : List VLevel) (k : Nat := 0) :
    (e.inst a k).instL levels = (e.instL levels).inst (a.instL levels) k := by
  induction e generalizing k with
  | bvar i =>
      by_cases hi : i < k
      · simp [VExpr.inst, VExpr.instL, instVar, hi]
      · by_cases hik : i = k <;>
          simp [VExpr.inst, VExpr.instL, instVar, hi, hik, instL_liftN]
  | _ => simp_all [VExpr.inst, VExpr.instL]

/-- The production empty-argument fast path is justified by universe scope. -/
theorem LevelWF.instL_nil {e : VExpr β} (scope : e.LevelWF 0) :
    e.instL [] = e := by
  induction e with
  | bvar _ | natLit _ => rfl
  | sort l =>
      exact congrArg VExpr.sort (VLevel.inst_id scope)
  | const r ls =>
      simp only [VExpr.instL, VExpr.const.injEq, true_and]
      simpa using List.map_congr_left (f := VLevel.inst []) (g := id)
        (fun l hl => VLevel.inst_id (scope l hl))
  | app _ _ hf ha => simp only [VExpr.instL, hf scope.1, ha scope.2]
  | lam _ _ hA hb => simp only [VExpr.instL, hA scope.1, hb scope.2]
  | forallE _ _ hA hB => simp only [VExpr.instL, hA scope.1, hB scope.2]
  | proj r i _ he => exact congrArg (VExpr.proj r i) (he scope)

end VExpr

namespace Model
namespace AExpr

/-- Universe congruence with the same binder annotations at every occurrence. -/
inductive LevelEquivalent : AExpr β → AExpr β → Prop
  | bvar (index) : LevelEquivalent (.bvar index) (.bvar index)
  | sort {left right} (levels : left ≈ right) :
      LevelEquivalent (.sort left) (.sort right)
  | const (ref) {left right}
      (levels : ∀ valuation, left.map (VLevel.eval valuation) =
        right.map (VLevel.eval valuation)) :
      LevelEquivalent (.const ref left) (.const ref right)
  | app {f f' a a'} (fn : LevelEquivalent f f') (arg : LevelEquivalent a a') :
      LevelEquivalent (.app f a) (.app f' a')
  | lam (condition) {A A' b b'}
      (domain : LevelEquivalent A A') (body : LevelEquivalent b b') :
      LevelEquivalent (.lam condition A b) (.lam condition A' b')
  | forallE (condition) {A A' B B'}
      (domain : LevelEquivalent A A') (body : LevelEquivalent B B') :
      LevelEquivalent (.forallE condition A B) (.forallE condition A' B')
  | proj (ref index) {e e'} (major : LevelEquivalent e e') :
      LevelEquivalent (.proj ref index e) (.proj ref index e')
  | natLit (value) : LevelEquivalent (.natLit value) (.natLit value)

/-- Copy occurrence annotations to a structurally congruent expression. -/
theorem reannotate_levels (e : AExpr β) {source : VExpr β}
    (same : VExpr.LevelEquivalent e.erase source) :
    ∃ result : AExpr β, result.erase = source ∧ LevelEquivalent e result := by
  induction e generalizing source with
  | bvar i => cases same; exact ⟨.bvar i, rfl, .bvar i⟩
  | sort l => cases same with | sort h => exact ⟨.sort _, rfl, .sort h⟩
  | const r ls => cases same with | const _ h => exact ⟨.const r _, rfl, .const r h⟩
  | app f a hf ha =>
      cases same with
      | app sf sa =>
          obtain ⟨f', rfl, ef⟩ := hf sf
          obtain ⟨a', rfl, ea⟩ := ha sa
          exact ⟨.app f' a', rfl, .app ef ea⟩
  | lam p A b hA hb =>
      cases same with
      | lam sA sb =>
          obtain ⟨A', rfl, eA⟩ := hA sA
          obtain ⟨b', rfl, eb⟩ := hb sb
          exact ⟨.lam p A' b', rfl, .lam p eA eb⟩
  | forallE p A B hA hB =>
      cases same with
      | forallE sA sB =>
          obtain ⟨A', rfl, eA⟩ := hA sA
          obtain ⟨B', rfl, eB⟩ := hB sB
          exact ⟨.forallE p A' B', rfl, .forallE p eA eB⟩
  | proj r i e ih =>
      cases same with
      | proj _ _ se =>
          obtain ⟨e', rfl, ee⟩ := ih se
          exact ⟨.proj r i e', rfl, .proj r i ee⟩
  | natLit n => cases same; exact ⟨.natLit n, rfl, .natLit n⟩

namespace LevelEquivalent

theorem interp {e e' : AExpr β} (same : LevelEquivalent e e')
    {V : Type v} [SetTheory V] (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    Model.interp constants levels env e = Model.interp constants levels env e' := by
  induction same generalizing env with
  | bvar _ | natLit _ => rfl
  | sort h => exact congrArg SetTheory.univ (VLevel.equiv_def.mp h levels)
  | const r h => exact congrArg (constants r) (h levels)
  | app _ _ hf ha => simp only [Model.interp, hf, ha]
  | lam p _ _ hA hb | forallE p _ _ hA hb =>
      simp only [Model.interp, hA]
      congr 1
      funext x
      exact hb _
  | proj r i _ he => exact congrArg (projectValue i) (he env)

theorem wellDenoted {e e' : AExpr β} (same : LevelEquivalent e e')
    {V : Type v} [SetTheory V] (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted constants levels env e ↔ WellDenoted constants levels env e' := by
  induction same generalizing env with
  | bvar _ | sort _ | const _ _ | natLit _ => rfl
  | app sf sa hf ha =>
      simp only [WellDenoted, hf, ha, sf.interp constants levels, sa.interp constants levels]
  | lam p sA sb hA hb | forallE p sA sb hA hb =>
      simp only [WellDenoted, hA, hb, sA.interp constants levels, sb.interp constants levels]
  | proj r i se he => exact he env

/-- Type transport uses hereditary validity, not just equality of denotations. -/
theorem typing {entries : Environment β} {context : Context β} {e A B : AExpr β}
    (same : LevelEquivalent A B) (typed : TypingClaim.{u,v} entries context e A) :
    TypingClaim.{u,v} entries context e B := by
  intro V _ constants realizes levels env valid
  obtain ⟨termValid, typeValid, member⟩ := typed V constants realizes levels env valid
  exact ⟨termValid, (same.wellDenoted constants levels env).mp typeValid,
    same.interp constants levels env ▸ member⟩

end LevelEquivalent
end AExpr
end Model
end Ix.Theory
