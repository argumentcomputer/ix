/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Standard/Realization.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
no further changes.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Basis.Iff
import Ix.Kernel.Certified.Basis.Nonempty

/-! Realizations of the exact standard propext and choice types. Their
prerequisite meanings follow from admitted inductive interfaces in every
compatible prefix model, rather than being new semantic assumptions. -/

namespace Ix.Kernel.Certified.Standard

open Model Model.SetTheory Model.SetModel Basis

universe u v
variable {β : Type u}

inductive Spec (β : Type u) where
  | propext (eq eqRefl eqRec iff iffIntro iffRec : ConstRef β)
  | choice (nonempty intro recursor : ConstRef β)

def Spec.universes : Spec β → Nat
  | .propext .. => 0
  | .choice .. => 1

def propextType (eq iff : ConstRef β) : AExpr β :=
  .forallE .always (.sort .zero) <| .forallE .always (.sort .zero) <|
  .forallE .always (Iff.applied iff (.bvar 1) (.bvar 0)) <|
    Equality.applied eq (.succ .zero) (.sort .zero) (.bvar 2) (.bvar 1)

def choiceType (nonempty : ConstRef β) : AExpr β :=
  .forallE (.param 0) (.sort (.param 0)) <|
  .forallE (.param 0) (Nonempty.applied nonempty (.param 0) (.bvar 0)) (.bvar 1)

def Spec.type : Spec β → AExpr β
  | .propext eq _ _ iff _ _ => propextType eq iff
  | .choice nonempty _ _ => choiceType nonempty

def Spec.Prerequisites (entries : Environment β) : Spec β → Prop
  | .propext eq eqRefl eqRec iff iffIntro iffRec =>
    Equality.Interface entries eq eqRefl eqRec ∧ Iff.Interface entries iff iffIntro iffRec
  | .choice nonempty intro recursor => Nonempty.Interface entries nonempty intro recursor

instance [DecidableEq β] (entries : Environment β) (spec : Spec β) :
    Decidable (spec.Prerequisites entries) := by cases spec <;> unfold Spec.Prerequisites <;> infer_instance

def Spec.entry (spec : Spec β) : ConstantEntry β := ⟨spec.universes, spec.type, none, [], []⟩
def Spec.source (spec : Spec β) : Const β := .axiom spec.universes spec.type.erase .safe

variable {V : Type v} [SetTheory V]

open Classical in
noncomputable def chooseSet (A : V) : V :=
  if h : ∃ a, a ∈ˢ A then Classical.choose h else empty

theorem chooseSet_mem {A : V} (h : ∃ a, a ∈ˢ A) : chooseSet A ∈ˢ A := by
  rw [chooseSet, dif_pos h]
  exact Classical.choose_spec h

noncomputable def choiceValue (constants : Assignment β V) (nonempty : ConstRef β) (u : Nat) : V :=
  lamR (if u = 0 then 0 else 1) (univ u) (fun A =>
    lamR (if u = 0 then 0 else 1) (Nonempty.value constants nonempty u A) (fun _ => chooseSet A))

noncomputable def Spec.value (spec : Spec β) (constants : Assignment β V) (levels : List Nat) : V :=
  match spec with
  | .propext .. => pt
  | .choice nonempty _ _ => choiceValue constants nonempty (levels.getD 0 0)

theorem propextType_interp (constants : Assignment β V) (eq iff : ConstRef β) (env : Nat → V) :
    interp constants [] env (propextType eq iff) =
      piR 0 univZero (fun P => piR 0 univZero (fun Q =>
        piR 0 (Iff.value constants iff P Q) (fun _ => Equality.value constants eq 1 univZero P Q))) := by
  simp [propextType, Iff.applied, Equality.applied, Iff.value, Equality.value,
    AExpr.appN, interp, VLevel.eval, Valuation.cons, univ_zero]

theorem choiceType_interp (constants : Assignment β V) (nonempty : ConstRef β) (u : Nat) (env : Nat → V) :
    interp constants [u] env (choiceType nonempty) =
      piR (if u = 0 then 0 else 1) (univ u) (fun A =>
        piR (if u = 0 then 0 else 1) (Nonempty.value constants nonempty u A) (fun _ => A)) := by
  simp [choiceType, Nonempty.applied, Nonempty.value, interp, VLevel.eval, Valuation.cons,
    regime, PropWhen.param, PropWhen.holds]

theorem propextValue_mem {entries : Environment β} {constants : Assignment β V}
    {eq eqRefl eqRec iff iffIntro iffRec : ConstRef β}
    (hE : Equality.Interface entries eq eqRefl eqRec)
    (hI : Iff.Interface entries iff iffIntro iffRec) (hM : Realizes constants entries) (env : Nat → V) :
    (pt : V) ∈ˢ interp constants [] env (propextType eq iff) := by
  rw [propextType_interp]
  apply pt_mem_piR_zero_of
  intro P hP
  apply pt_mem_piR_zero_of
  intro Q hQ
  apply pt_mem_piR_zero_of
  intro proof hp
  rw [Equality.value_eq_eqv hE hM (by simpa only [univ_zero] using univ_mem_univ (V := V) 0) hP hQ]
  have he := Iff.eq_of_mem hI hM hP hQ hp
  subst Q
  exact pt_mem_eqv_self _

theorem choiceValue_mem {entries : Environment β} {constants : Assignment β V}
    {nonempty intro recursor : ConstRef β}
    (h : Nonempty.Interface entries nonempty intro recursor) (hM : Realizes constants entries)
    (u : Nat) (env : Nat → V) :
    choiceValue constants nonempty u ∈ˢ interp constants [u] env (choiceType nonempty) := by
  rw [choiceType_interp]
  apply lamR_mem
  intro A hA
  apply lamR_mem
  intro proof hp
  exact chooseSet_mem (Nonempty.exists_of_mem h hM hA hp)

theorem Spec.value_mem {entries : Environment β} {constants : Assignment β V}
    (spec : Spec β) (h : spec.Prerequisites entries) (hM : Realizes constants entries)
    (levels : List Nat) (hn : levels.length = spec.universes) (env : Nat → V) :
    spec.value constants levels ∈ˢ interp constants levels env spec.type := by
  cases spec with
  | propext eq eqRefl eqRec iff iffIntro iffRec =>
    have he : levels = [] := List.length_eq_zero_iff.mp hn
    subst levels
    exact propextValue_mem h.1 h.2 hM env
  | choice nonempty intro recursor =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
    exact choiceValue_mem h hM u env

end Ix.Kernel.Certified.Standard
