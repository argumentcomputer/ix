/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Basis/Equality.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store is removed; the shape of `Eq` and the link to a checked
block move to `Basis.EqualityChecked` so that this module depends on the model
only and the kernel core can read the interface.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Basis.Interface
import Ix.Kernel.Model.Inductive.Telescope

/-! Equality's meaning follows from the admitted former, reflexivity and
dependent eliminator types, in every compatible model. It does not assume
that an arbitrary prefix assignment is the model chosen by one producer. -/

namespace Ix.Kernel.Certified.Basis.Equality

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u}


def type : AExpr β :=
  .forallE .never (.sort (.param 0))
    (.forallE .never (.bvar 0) (.forallE .never (.bvar 1) (.sort .zero)))

def applied (family : ConstRef β) (l : VLevel) (A a b : AExpr β) : AExpr β :=
  .appN (.const family [l]) [A, a, b]

def reflexivity (refl : ConstRef β) (l : VLevel) (A a : AExpr β) : AExpr β :=
  .appN (.const refl [l]) [A, a]

def reflType (family : ConstRef β) : AExpr β :=
  .forallE .always (.sort (.param 0)) (.forallE .always (.bvar 0)
    (applied family (.param 0) (.bvar 1) (.bvar 0) (.bvar 0)))

def recType (family refl : ConstRef β) : AExpr β :=
  .forallE (.param 0) (.sort (.param 1)) <|
  .forallE (.param 0) (.bvar 0) <|
  .forallE (.param 0)
    (.forallE .never (.bvar 1)
      (.forallE .never (applied family (.param 1) (.bvar 2) (.bvar 1) (.bvar 0)) (.sort (.param 0)))) <|
  .forallE (.param 0)
    (.appN (.bvar 0) [.bvar 1, reflexivity refl (.param 1) (.bvar 2) (.bvar 1)]) <|
  .forallE (.param 0) (.bvar 3) <|
  .forallE (.param 0) (applied family (.param 1) (.bvar 4) (.bvar 3) (.bvar 0)) <|
    .appN (.bvar 3) [.bvar 1, .bvar 0]

structure Interface (entries : Environment β) (family refl recursor : ConstRef β) : Prop where
  former : entries.HasType family 1 type
  reflexivity : entries.HasType refl 1 (reflType family)
  elimination : entries.HasType recursor 2 (recType family refl)

instance [DecidableEq β] (entries : Environment β) (family refl recursor : ConstRef β) :
    Decidable (Interface entries family refl recursor) :=
  decidable_of_iff (entries.HasType family 1 type ∧ entries.HasType refl 1 (reflType family) ∧
    entries.HasType recursor 2 (recType family refl))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.former, h.reflexivity, h.elimination⟩⟩




theorem Interface.of_extension {entries next : Environment β} {family refl recursor : ConstRef β}
    (h : Interface entries family refl recursor)
    (hext : ∀ r entry, entries r = some entry → next r = some entry) :
    Interface next family refl recursor := by
  constructor
  all_goals
    first
    | obtain ⟨entry, he, hn, ht⟩ := h.former
      exact ⟨entry, hext _ _ he, hn, ht⟩
    | obtain ⟨entry, he, hn, ht⟩ := h.reflexivity
      exact ⟨entry, hext _ _ he, hn, ht⟩
    | obtain ⟨entry, he, hn, ht⟩ := h.elimination
      exact ⟨entry, hext _ _ he, hn, ht⟩

variable {V : Type v} [SetTheory V]

noncomputable def value (constants : Assignment β V) (family : ConstRef β)
    (u : Nat) (A a b : V) : V := app (app (app (constants family [u]) A) a) b

noncomputable def reflValue (constants : Assignment β V) (refl : ConstRef β)
    (u : Nat) (A a : V) : V := app (app (constants refl [u]) A) a

theorem type_interp (constants : Assignment β V) (u : Nat) (env : Nat → V) :
    interp constants [u] env (type : AExpr β) =
      piR 1 (univ u) (fun A => piR 1 A (fun _ => piR 1 A (fun _ => univZero))) := by
  simp [type, interp, VLevel.eval, Valuation.cons, univ_zero]

theorem reflType_interp (constants : Assignment β V) (family : ConstRef β)
    (u : Nat) (env : Nat → V) :
    interp constants [u] env (reflType family) =
      piR 0 (univ u) (fun A => piR 0 A (fun a => value constants family u A a a)) := by
  simp [reflType, applied, AExpr.appN, value, interp, VLevel.eval, Valuation.cons]

theorem recType_zero_interp (constants : Assignment β V) (family refl : ConstRef β)
    (u : Nat) (env : Nat → V) :
    interp constants [0, u] env (recType family refl) =
      piR 0 (univ u) (fun A => piR 0 A (fun a =>
        piR 0 (piR 1 A (fun b => piR 1 (value constants family u A a b) (fun _ => univZero)))
          (fun motive => piR 0 (app (app motive a) (reflValue constants refl u A a))
            (fun _ => piR 0 A (fun b => piR 0 (value constants family u A a b)
              (fun h => app (app motive b) h)))))) := by
  simp [recType, applied, reflexivity, AExpr.appN, value, reflValue, interp, VLevel.eval,
    Valuation.cons, regime, PropWhen.param, PropWhen.holds, univ_zero]

variable {entries : Environment β} {family refl recursor : ConstRef β}
  {constants : Assignment β V}

theorem value_mem_univZero (h : Interface entries family refl recursor) (hM : Realizes constants entries)
    {u : Nat} {A a b : V} (hA : A ∈ˢ univ u) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    value constants family u A a b ∈ˢ univZero := by
  have ht := h.former.member hM (levels := [u]) rfl (fun _ => empty)
  rw [type_interp] at ht
  have h1 : app (constants family [u]) A ∈ˢ
      piR 1 A (fun _ => piR 1 A (fun _ => univZero)) :=
    app_mem_piR_pos (by decide : 1 ≠ 0) ht hA
  have h2 : app (app (constants family [u]) A) a ∈ˢ piR 1 A (fun _ => univZero) :=
    app_mem_piR_pos (by decide : 1 ≠ 0) h1 ha
  exact app_mem_piR_pos (by decide : 1 ≠ 0) h2 hb

theorem reflValue_mem (h : Interface entries family refl recursor) (hM : Realizes constants entries)
    {u : Nat} {A a : V} (hA : A ∈ˢ univ u) (ha : a ∈ˢ A) :
    reflValue constants refl u A a ∈ˢ value constants family u A a a := by
  have ht := h.reflexivity.member hM (levels := [u]) rfl (fun _ => empty)
  rw [reflType_interp] at ht
  have h1 : app (constants refl [u]) A ∈ˢ piR 0 A (fun x => value constants family u A x x) :=
    app_mem_piR ht hA (fun _ _ _ => piR_zero_mem_univZero)
  exact app_mem_piR (B := fun x => value constants family u A x x) h1 ha
    (fun _ b hb => value_mem_univZero h hM hA hb hb)

theorem exists_of_mem_piR_zero {A f a : V} {B : V → V}
    (hf : f ∈ˢ piR 0 A B) (ha : a ∈ˢ A) : ∃ b, b ∈ˢ B a := by
  rw [piR_zero] at hf
  exact of_mem_truthVal hf a ha

theorem eq_of_mem (h : Interface entries family refl recursor) (hM : Realizes constants entries)
    {u : Nat} {A a b proof : V} (hA : A ∈ˢ univ u) (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hp : proof ∈ˢ value constants family u A a b) : a = b := by
  let motive := lamR 1 A (fun b => lamR 1 (value constants family u A a b) (fun _ => eqv a b))
  have hm : motive ∈ˢ piR 1 A (fun b =>
      piR 1 (value constants family u A a b) (fun _ => univZero)) :=
    lamR_mem fun _ _ => lamR_mem fun _ _ => eqv_mem_univZero _ _
  have hbeta (x q : V) (hx : x ∈ˢ A) (hq : q ∈ˢ value constants family u A a x) :
      app (app motive x) q = eqv a x := by
    rw [app_lamR_pos (by decide : 1 ≠ 0) hx, app_lamR_pos (by decide : 1 ≠ 0) hq]
  have hminor : (pt : V) ∈ˢ app (app motive a) (reflValue constants refl u A a) := by
    rw [hbeta _ _ ha (reflValue_mem h hM hA ha)]
    exact pt_mem_eqv_self _
  have hr := h.elimination.member hM (levels := [0, u]) rfl (fun _ => empty)
  rw [recType_zero_interp] at hr
  obtain ⟨rA, hrA⟩ := exists_of_mem_piR_zero hr hA
  obtain ⟨ra, hra⟩ := exists_of_mem_piR_zero hrA ha
  obtain ⟨rm, hrm⟩ := exists_of_mem_piR_zero hra hm
  obtain ⟨ri, hri⟩ := exists_of_mem_piR_zero hrm hminor
  obtain ⟨rb, hrb⟩ := exists_of_mem_piR_zero hri hb
  obtain ⟨result, hresult⟩ := exists_of_mem_piR_zero hrb hp
  rw [hbeta _ _ hb hp] at hresult
  exact eq_of_mem_eqv hresult

/-- The prerequisite needed by standard axiom realizations is derived from
admitted types. No equality-meaning oracle is added to the prefix model. -/
theorem value_eq_eqv (h : Interface entries family refl recursor) (hM : Realizes constants entries)
    {u : Nat} {A a b : V} (hA : A ∈ˢ univ u) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    value constants family u A a b = eqv a b := by
  apply univZero_ext (value_mem_univZero h hM hA ha hb) (eqv_mem_univZero _ _)
  · intro hp
    have he := eq_of_mem h hM hA ha hb hp
    subst b
    exact pt_mem_eqv_self _
  · intro hp
    have he := eq_of_mem_eqv hp
    subst b
    have hr := reflValue_mem h hM hA ha
    rwa [eq_pt_of_mem_univZero (value_mem_univZero h hM hA ha ha) hr] at hr

end Ix.Kernel.Certified.Basis.Equality
