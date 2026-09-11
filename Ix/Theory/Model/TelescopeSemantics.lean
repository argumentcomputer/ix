/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Instantiation

namespace Ix.Theory.Model.Telescope

open SetTheory SetTheory.Tower SetModel Certified

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

theorem fits_append_iff (constants : Assignment β V) (levels : List Nat) (env : Nat → V)
    (left right : List (AExpr β)) (xs : List V) :
    FitsS (interpret constants levels env (left ++ right)) xs ↔
      ∃ ys zs, xs = ys ++ zs ∧ FitsS (interpret constants levels env left) ys ∧
        FitsS (interpret constants levels (extend env ys) right) zs := by
  induction left generalizing env xs with
  | nil =>
    constructor
    · intro h
      exact ⟨[], xs, rfl, trivial, h⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      cases ys with
      | nil => exact hz
      | cons _ _ => exact hy.elim
  | cons A rest ih =>
    constructor
    · intro h
      cases xs with
      | nil => exact h.elim
      | cons x xs =>
        obtain ⟨ys, zs, rfl, hy, hz⟩ := (ih (Valuation.cons x env) xs).mp h.2
        exact ⟨x :: ys, zs, rfl, ⟨h.1, hy⟩, hz⟩
    · rintro ⟨ys, zs, rfl, hy, hz⟩
      cases ys with
      | nil => exact hy.elim
      | cons y ys => exact ⟨hy.1, (ih (Valuation.cons y env) (ys ++ zs)).mpr ⟨ys, zs, rfl, hy.2, hz⟩⟩

/-- Close a pointwise semantic fact over a formed telescope. The result
includes hereditary validity of both complete endpoints and a uniform sort
for the resulting product. It does not assume a model for any new fact. -/
theorem Formed.lamN_semantics {entries : Environment β} {Γ : Context β}
    {domains : List (AExpr β)} (h : Formed.{u,v} entries Γ domains)
    (constants : Assignment β V) (hM : Realizes constants entries) (levels : List Nat)
    (body B : AExpr β) (b : VLevel) :
    ∃ l, zeroCondition l = zeroCondition b ∧ ∀ env, Γ.Valid constants levels env →
      (∀ xs, FitsS (interpret constants levels env domains) xs →
        let env' := extend env xs
        WellDenoted constants levels env' body ∧ WellDenoted constants levels env' B ∧
          interp constants levels env' body ∈ˢ interp constants levels env' B ∧
          interp constants levels env' B ∈ˢ (univ (b.eval levels) : V)) →
      WellDenoted constants levels env (.lamN (zeroCondition b) domains body) ∧
        WellDenoted constants levels env (.forallN (zeroCondition b) domains B) ∧
        interp constants levels env (.lamN (zeroCondition b) domains body) ∈ˢ
          interp constants levels env (.forallN (zeroCondition b) domains B) ∧
        interp constants levels env (.forallN (zeroCondition b) domains B) ∈ˢ
          (univ (l.eval levels) : V) := by
  induction h with
  | nil => exact ⟨b, rfl, fun env _ hb => hb [] trivial⟩
  | @cons Γ A rest a hA hrest ih =>
    obtain ⟨l, hl, ih⟩ := ih
    refine ⟨.imax a l, hl, ?_⟩
    intro env hΓ hb
    have hAt := hA V constants hM levels env hΓ
    have ht x hx := ih (Valuation.cons x env) (hΓ.push hAt.1 hx)
      (fun xs hxs => hb (x :: xs) ⟨hx, hxs⟩)
    have hz : regime (zeroCondition b) levels = 0 ↔ l.eval levels = 0 := by
      rw [← hl]
      exact regime_zeroCondition ..
    refine ⟨⟨hAt.1, fun x hx => (ht x hx).1, l.eval levels,
      (fun x => interp constants levels (Valuation.cons x env) (.forallN (zeroCondition b) rest B)),
      hz, fun x hx => ⟨(ht x hx).2.2.1, (ht x hx).2.2.2⟩⟩,
      ⟨hAt.1, fun x hx => (ht x hx).2.1, l.eval levels, hz,
        fun x hx => (ht x hx).2.2.2⟩, ?_, ?_⟩
    · exact lamR_mem (fun x hx => (ht x hx).2.2.1)
    · exact annotated_pi_mem_univ hl.symm hAt.2.2 (fun x hx => (ht x hx).2.2.2)

end Ix.Theory.Model.Telescope
