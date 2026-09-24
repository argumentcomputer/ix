/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Interpret
import Ix.Kernel.Model.SetTheory.Derive.Quot

/-! # Quotient values

The set-theoretic values of the quotient former, constructor, and lift, and
the sets their types denote. They are stated here, before the environment,
because the `quotient` facts an installed quotient constant publishes pin its
value to them (`Ix.Kernel.Model.ConstantFact`), which is what lets the five
quotient constants be installed one at a time. The definitions and the
membership lemmas are those of the old branch's `Certified/Quotient/Value`;
the lemmas needing the meaning of equality stay with the route. -/

namespace Ix.Kernel.Model.Quotient

open SetTheory SetModel

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

/-- The value of an equality family applied to a type and two terms. -/
noncomputable def eqValue (constants : Assignment β V) (eq : ConstRef β) (v : Nat) (B a b : V) : V :=
  app (app (app (constants eq [v]) B) a) b

noncomputable def invariantSet (constants : Assignment β V) (eq : ConstRef β)
    (v : Nat) (A R B f : V) : V :=
  piR 0 A (fun a => piR 0 A (fun b => piR 0 (app (app R a) b)
    (fun _ => eqValue constants eq v B (app f a) (app f b))))

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
      eqValue constants eq u (quotSet u A R) (quotClass u A R a) (quotClass u A R b))))))

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

/-- The lift's value depends on the assignment only through the equality family. -/
theorem invariantSet_congr {constants constants' : Assignment β V} {eq : ConstRef β} {v : Nat}
    (h : constants' eq [v] = constants eq [v]) (A R B f : V) :
    invariantSet constants' eq v A R B f = invariantSet constants eq v A R B f := by
  simp only [invariantSet, eqValue, h]

theorem liftValue_congr {constants constants' : Assignment β V} {eq : ConstRef β} {u v : Nat}
    (h : constants' eq [v] = constants eq [v]) :
    liftValue constants' eq u v = liftValue constants eq u v := by
  simp only [liftValue, invariantSet_congr h]

theorem liftSet_congr {constants constants' : Assignment β V} {eq : ConstRef β} {u v : Nat}
    (h : constants' eq [v] = constants eq [v]) :
    liftSet constants' eq u v = liftSet constants eq u v := by
  simp only [liftSet, invariantSet_congr h]

end Ix.Kernel.Model.Quotient
