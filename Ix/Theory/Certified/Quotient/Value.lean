/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Quotient.Syntax
import Ix.Theory.Model.SetTheory.Derive.Quot

namespace Ix.Theory.Certified.Quotient

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

def bit (u : Nat) : Nat := if u = 0 then 0 else 1

noncomputable def relationSet (A : V) : V :=
  piR 1 A (fun _ => piR 1 A (fun _ => univZero))

noncomputable def formerValue (u : Nat) : V :=
  lamR 1 (univ u) (fun A => lamR 1 (relationSet A) (fun R => quotSet u A R))

noncomputable def constructorValue (u : Nat) : V :=
  lamR (bit u) (univ u) (fun A => lamR (bit u) (relationSet A) (fun R =>
    lamR (bit u) A (fun a => quotClass u A R a)))

noncomputable def invariantSet (constants : Assignment β V) (eq : ConstRef β)
    (v : Nat) (A R B f : V) : V :=
  piR 0 A (fun a => piR 0 A (fun b => piR 0 (app (app R a) b)
    (fun _ => Basis.Equality.value constants eq v B (app f a) (app f b))))

noncomputable def liftValue (constants : Assignment β V) (eq : ConstRef β) (u v : Nat) : V :=
  lamR (bit v) (univ u) (fun A => lamR (bit v) (relationSet A) (fun R =>
    lamR (bit v) (univ v) (fun B => lamR (bit v) (piR (bit v) A (fun _ => B)) (fun f =>
      lamR (bit v) (invariantSet constants eq v A R B f) (fun _ =>
        lamR (bit v) (quotSet u A R) (fun q => app f (qrep u A R q)))))))

noncomputable def formerSet (u : Nat) : V :=
  piR 1 (univ u) (fun A => piR 1 (relationSet A) (fun _ => univ u))

noncomputable def constructorSet (u : Nat) : V :=
  piR (bit u) (univ u) (fun A => piR (bit u) (relationSet A) (fun R =>
    piR (bit u) A (fun _ => quotSet u A R)))

noncomputable def liftSet (constants : Assignment β V) (eq : ConstRef β) (u v : Nat) : V :=
  piR (bit v) (univ u) (fun A => piR (bit v) (relationSet A) (fun R =>
    piR (bit v) (univ v) (fun B => piR (bit v) (piR (bit v) A (fun _ => B)) (fun f =>
      piR (bit v) (invariantSet constants eq v A R B f) (fun _ =>
        piR (bit v) (quotSet u A R) (fun _ => B))))))

noncomputable def indSet (u : Nat) : V :=
  piR 0 (univ u) (fun A => piR 0 (relationSet A) (fun R =>
    piR 0 (piR 1 (quotSet u A R) (fun _ => univZero)) (fun motive =>
      piR 0 (piR 0 A (fun a => app motive (quotClass u A R a))) (fun _ =>
        piR 0 (quotSet u A R) (fun q => app motive q)))))

noncomputable def soundSet (constants : Assignment β V) (eq : ConstRef β) (u : Nat) : V :=
  piR 0 (univ u) (fun A => piR 0 (relationSet A) (fun R =>
    piR 0 A (fun a => piR 0 A (fun b => piR 0 (app (app R a) b) (fun _ =>
      Basis.Equality.value constants eq u (quotSet u A R)
        (quotClass u A R a) (quotClass u A R b))))))

theorem app_mem_bit {u : Nat} {A B f a : V} (hB : B ∈ˢ univ u)
    (hf : f ∈ˢ piR (bit u) A (fun _ => B)) (ha : a ∈ˢ A) : app f a ∈ˢ B := by
  apply app_mem_piR hf ha
  intro hu _ _
  have he : u = 0 := by simpa [bit] using hu
  simpa [he, univ_zero] using hB

theorem formerValue_mem (u : Nat) : (formerValue u : V) ∈ˢ formerSet u := by
  apply lamR_mem
  intro A hA
  exact lamR_mem fun _ _ => quotSet_mem_univ hA

theorem constructorValue_mem (u : Nat) : (constructorValue u : V) ∈ˢ constructorSet u := by
  apply lamR_mem
  intro A _
  apply lamR_mem
  intro R _
  exact lamR_mem fun _ ha => quotClass_mem ha

theorem formerValue_apply {u : Nat} {A R : V} (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) :
    app (app (formerValue u) A) R = quotSet u A R := by
  rw [formerValue, app_lamR_pos (by decide : 1 ≠ 0) hA,
    app_lamR_pos (by decide : 1 ≠ 0) hR]

theorem constructorValue_apply {u : Nat} {A R a : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) (ha : a ∈ˢ A) :
    app (app (app (constructorValue u) A) R) a = quotClass u A R a := by
  by_cases hu : u = 0
  · subst u
    simp [constructorValue, bit, lamR_zero, app_pt, quotClass]
  · simp only [constructorValue, bit, if_neg hu]
    rw [app_lamR_pos (by decide : 1 ≠ 0) hA,
      app_lamR_pos (by decide : 1 ≠ 0) hR, app_lamR_pos (by decide : 1 ≠ 0) ha]

theorem liftValue_mem (constants : Assignment β V) (eq : ConstRef β) (u v : Nat) :
    liftValue constants eq u v ∈ˢ liftSet constants eq u v := by
  apply lamR_mem
  intro A _
  apply lamR_mem
  intro R _
  apply lamR_mem
  intro B hB
  apply lamR_mem
  intro f hf
  apply lamR_mem
  intro _ _
  apply lamR_mem
  intro q hq
  exact app_mem_bit hB hf (qrep_spec hq).1

theorem indValue_mem (u : Nat) : (pt : V) ∈ˢ indSet u := by
  apply pt_mem_piR_zero_of
  intro A _
  apply pt_mem_piR_zero_of
  intro R _
  apply pt_mem_piR_zero_of
  intro motive hm
  apply pt_mem_piR_zero_of
  intro f hf
  apply pt_mem_piR_zero_of
  intro q hq
  obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
  have hprop : ∀ x, x ∈ˢ quotSet u A R → app motive x ∈ˢ univZero :=
    fun _ hx => app_mem_piR_pos (by decide : 1 ≠ 0) hm hx
  have hf' : app f a ∈ˢ app motive (quotClass u A R a) :=
    app_mem_piR hf ha (fun _ a ha => hprop _ (quotClass_mem ha))
  rwa [eq_pt_of_mem_univZero (hprop _ (quotClass_mem ha)) hf'] at hf'

theorem soundValue_mem {entries : Environment β} {constants : Assignment β V} {eq refl recursor : ConstRef β}
    (hE : Basis.Equality.Interface entries eq refl recursor) (hM : Realizes constants entries) (u : Nat) :
    (pt : V) ∈ˢ soundSet constants eq u := by
  apply pt_mem_piR_zero_of
  intro A hA
  apply pt_mem_piR_zero_of
  intro R _
  apply pt_mem_piR_zero_of
  intro a ha
  apply pt_mem_piR_zero_of
  intro b hb
  apply pt_mem_piR_zero_of
  intro h hh
  rw [Basis.Equality.value_eq_eqv hE hM (quotSet_mem_univ hA) (quotClass_mem ha) (quotClass_mem hb),
    quotSound ha hb hh]
  exact pt_mem_eqv_self _

theorem invariant_of_mem {entries : Environment β} {constants : Assignment β V}
    {eq refl recursor : ConstRef β} (hE : Basis.Equality.Interface entries eq refl recursor)
    (hM : Realizes constants entries) {v : Nat} {A R B f h : V}
    (hB : B ∈ˢ univ v) (hf : f ∈ˢ piR (bit v) A (fun _ => B))
    (hh : h ∈ˢ invariantSet constants eq v A R B f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) → app f a = app f b := by
  intro a b ha hb ⟨w, hw⟩
  obtain ⟨ha', hha⟩ := Basis.Equality.exists_of_mem_piR_zero hh ha
  obtain ⟨hb', hhb⟩ := Basis.Equality.exists_of_mem_piR_zero hha hb
  obtain ⟨q, hq⟩ := Basis.Equality.exists_of_mem_piR_zero hhb hw
  exact Basis.Equality.eq_of_mem hE hM hB (app_mem_bit hB hf ha) (app_mem_bit hB hf hb) hq

/-- The whole quotient-lift application computes for any typed invariant
function. Both the Prop and graph regimes are included. -/
theorem liftValue_apply {entries : Environment β} {constants : Assignment β V}
    {eq refl recursor : ConstRef β} (hE : Basis.Equality.Interface entries eq refl recursor)
    (hM : Realizes constants entries) {u v : Nat} {A R B f h a : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) (hB : B ∈ˢ univ v)
    (hf : f ∈ˢ piR (bit v) A (fun _ => B))
    (hh : h ∈ˢ invariantSet constants eq v A R B f) (ha : a ∈ˢ A) :
    app (app (app (app (app (app (liftValue constants eq u v) A) R) B) f) h)
      (quotClass u A R a) = app f a := by
  by_cases hv : v = 0
  · subst v
    have he : f = pt := eq_pt_of_mem_piR_zero hf
    simp [liftValue, bit, lamR_zero, he, app_pt]
  · simp only [liftValue, bit, if_neg hv]
    rw [app_lamR_pos (by decide : 1 ≠ 0) hA,
      app_lamR_pos (by decide : 1 ≠ 0) hR,
      app_lamR_pos (by decide : 1 ≠ 0) hB,
      app_lamR_pos (by decide : 1 ≠ 0) (by simpa only [bit, if_neg hv] using hf),
      app_lamR_pos (by decide : 1 ≠ 0) hh,
      app_lamR_pos (by decide : 1 ≠ 0) (quotClass_mem ha)]
    have hs := qrep_spec (u := u) (R := R) (quotClass_mem ha)
    exact app_eq_of_quotClass_eq hA hs.1 ha (invariant_of_mem hE hM hB hf hh) hs.2.symm

end Ix.Theory.Certified.Quotient
