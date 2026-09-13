/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Basis.Equality

namespace Ix.Theory.Certified.Basis.Nonempty

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u}

def constructor : Ordinary.Constructor β := ⟨[.bvar 0], [], []⟩
def shape : Ordinary.Shape β := ⟨1, [.sort (.param 0)], [], .zero, [constructor]⟩
def type : AExpr β := .forallE .never (.sort (.param 0)) (.sort .zero)
def applied (family : ConstRef β) (l : VLevel) (A : AExpr β) : AExpr β := .app (.const family [l]) A
def introduction (ctor : ConstRef β) (l : VLevel) (A a : AExpr β) : AExpr β :=
  .appN (.const ctor [l]) [A, a]
def introType (family : ConstRef β) : AExpr β :=
  .forallE .always (.sort (.param 0)) (.forallE .always (.bvar 0) (applied family (.param 0) (.bvar 1)))
def recType (family ctor : ConstRef β) : AExpr β :=
  .forallE .always (.sort (.param 0)) <|
  .forallE .always (.forallE .never (applied family (.param 0) (.bvar 0)) (.sort .zero)) <|
  .forallE .always
    (.forallE .always (.bvar 1)
      (.app (.bvar 1) (introduction ctor (.param 0) (.bvar 2) (.bvar 0)))) <|
  .forallE .always (applied family (.param 0) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)

structure Interface (entries : Environment β) (family ctor recursor : ConstRef β) : Prop where
  former : entries.HasType family 1 type
  introduction : entries.HasType ctor 1 (introType family)
  elimination : entries.HasType recursor 1 (recType family ctor)

instance [DecidableEq β] (entries : Environment β) (family ctor recursor : ConstRef β) :
    Decidable (Interface entries family ctor recursor) :=
  decidable_of_iff (entries.HasType family 1 type ∧ entries.HasType ctor 1 (introType family) ∧
    entries.HasType recursor 1 (recType family ctor))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.former, h.introduction, h.elimination⟩⟩

theorem shape_type : (shape : Ordinary.Shape β).type = type := rfl
theorem shape_introType (source : β) : constructor.type shape source = introType (.member source 0) := rfl
theorem shape_recType (source : β) : shape.recursorType source .small =
    recType (.member source 0) (.ctor source 0 0) := rfl

theorem Interface.of_checked [DecidableEq β] {entries : Environment β} {store : Store β} {source recursor : β}
    (h : Ordinary.CheckedBlock.{u,v} entries store source recursor shape .small) :
    Interface (shape.publishedEnvironment entries source recursor .small)
      (.member source 0) (.ctor source 0 0) (.member recursor 0) := by
  constructor
  · refine ⟨shape.familyEntry, ?_, rfl, shape_type⟩
    exact Environment.insert_old h.recursorChecked.fresh
      (Environment.overlay_old (Ordinary.Shape.constructorEntries_fresh h.shapeChecked)
        (Environment.insert_same ..))
  · refine ⟨shape.constructorEntry source constructor, ?_, rfl, shape_introType source⟩
    apply Environment.insert_old h.recursorChecked.fresh
    apply Environment.overlay_new
    simp [Ordinary.Shape.constructorEntries, shape]
  · exact ⟨shape.publishedRecursorEntry source recursor .small,
      Environment.insert_same .., rfl, shape_recType source⟩

variable {V : Type v} [SetTheory V]

noncomputable def value (constants : Assignment β V) (family : ConstRef β) (u : Nat) (A : V) : V :=
  app (constants family [u]) A
noncomputable def introValue (constants : Assignment β V) (ctor : ConstRef β) (u : Nat) (A a : V) : V :=
  app (app (constants ctor [u]) A) a

theorem type_interp (constants : Assignment β V) (u : Nat) (env : Nat → V) :
    interp constants [u] env (type : AExpr β) = piR 1 (univ u) (fun _ => univZero) := by
  simp [type, interp, VLevel.eval, univ_zero]

theorem introType_interp (constants : Assignment β V) (family : ConstRef β) (u : Nat) (env : Nat → V) :
    interp constants [u] env (introType family) =
      piR 0 (univ u) (fun A => piR 0 A (fun _ => value constants family u A)) := by
  simp [introType, applied, value, interp, VLevel.eval, Valuation.cons]

theorem recType_interp (constants : Assignment β V) (family ctor : ConstRef β) (u : Nat) (env : Nat → V) :
    interp constants [u] env (recType family ctor) =
      piR 0 (univ u) (fun A =>
        piR 0 (piR 1 (value constants family u A) (fun _ => univZero)) (fun motive =>
          piR 0 (piR 0 A (fun a => app motive (introValue constants ctor u A a)))
            (fun _ => piR 0 (value constants family u A) (fun h => app motive h)))) := by
  simp [recType, applied, introduction, value, introValue, AExpr.appN, interp,
    VLevel.eval, Valuation.cons, univ_zero]

variable {entries : Environment β} {family ctor recursor : ConstRef β}
  {constants : Assignment β V}

theorem value_mem_univZero (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {u : Nat} {A : V} (hA : A ∈ˢ univ u) : value constants family u A ∈ˢ univZero := by
  have ht := h.former.member hM (levels := [u]) rfl (fun _ => empty)
  rw [type_interp] at ht
  exact app_mem_piR_pos (by decide : 1 ≠ 0) ht hA

theorem introValue_mem (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {u : Nat} {A a : V} (hA : A ∈ˢ univ u) (ha : a ∈ˢ A) :
    introValue constants ctor u A a ∈ˢ value constants family u A := by
  have ht := h.introduction.member hM (levels := [u]) rfl (fun _ => empty)
  rw [introType_interp] at ht
  have h1 := app_mem_piR ht hA (fun _ _ _ => piR_zero_mem_univZero)
  exact app_mem_piR h1 ha (fun _ _ _ => value_mem_univZero h hM hA)

theorem exists_of_mem (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {u : Nat} {A proof : V} (hA : A ∈ˢ univ u) (hp : proof ∈ˢ value constants family u A) :
    ∃ a, a ∈ˢ A := by
  let C : V := truthVal (∃ a, a ∈ˢ A)
  let motive := lamR 1 (value constants family u A) (fun _ => C)
  have hm : motive ∈ˢ piR 1 (value constants family u A) (fun _ => univZero) :=
    lamR_mem fun _ _ => truthVal_mem_univZero _
  let minor := lamR 0 A (fun _ => pt)
  have hminor : minor ∈ˢ piR 0 A (fun a => app motive (introValue constants ctor u A a)) := by
    apply lamR_mem
    intro a ha
    rw [app_lamR_pos (by decide : 1 ≠ 0) (introValue_mem h hM hA ha)]
    exact pt_mem_truthVal ⟨a, ha⟩
  have hr := h.elimination.member hM (levels := [u]) rfl (fun _ => empty)
  rw [recType_interp] at hr
  obtain ⟨rA, hrA⟩ := Equality.exists_of_mem_piR_zero hr hA
  obtain ⟨rm, hrm⟩ := Equality.exists_of_mem_piR_zero hrA hm
  obtain ⟨ri, hri⟩ := Equality.exists_of_mem_piR_zero hrm hminor
  obtain ⟨result, hresult⟩ := Equality.exists_of_mem_piR_zero hri hp
  rw [app_lamR_pos (by decide : 1 ≠ 0) hp] at hresult
  exact of_mem_truthVal hresult

theorem value_eq_truthVal (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {u : Nat} {A : V} (hA : A ∈ˢ univ u) :
    value constants family u A = truthVal (∃ a, a ∈ˢ A) := by
  apply univZero_ext (value_mem_univZero h hM hA) (truthVal_mem_univZero _)
  · exact fun hp => pt_mem_truthVal (exists_of_mem h hM hA hp)
  · intro hp
    obtain ⟨a, ha⟩ := of_mem_truthVal hp
    have hc := introValue_mem h hM hA ha
    rwa [eq_pt_of_mem_univZero (value_mem_univZero h hM hA) hc] at hc

end Ix.Theory.Certified.Basis.Nonempty
