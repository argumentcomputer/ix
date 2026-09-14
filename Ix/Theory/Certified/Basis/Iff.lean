/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Basis.Equality

namespace Ix.Theory.Certified.Basis.Iff

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u}

def arrow (P Q : AExpr β) : AExpr β := .forallE .always P (Q.liftN 1)

def constructor : Ordinary.Constructor β :=
  ⟨[arrow (.bvar 1) (.bvar 0), arrow (.bvar 1) (.bvar 2)], [], []⟩

def shape : Ordinary.Shape β := ⟨0, [.sort .zero, .sort .zero], [], .zero, [constructor]⟩

def type : AExpr β :=
  .forallE .never (.sort .zero) (.forallE .never (.sort .zero) (.sort .zero))

def applied (family : ConstRef β) (P Q : AExpr β) : AExpr β := .appN (.const family []) [P, Q]

def introduction (ctor : ConstRef β) (P Q f g : AExpr β) : AExpr β :=
  .appN (.const ctor []) [P, Q, f, g]

def introType (family : ConstRef β) : AExpr β :=
  .forallE .always (.sort .zero) <| .forallE .always (.sort .zero) <|
  .forallE .always (arrow (.bvar 1) (.bvar 0)) <|
  .forallE .always (arrow (.bvar 1) (.bvar 2)) <|
    applied family (.bvar 3) (.bvar 2)

def recType (family ctor : ConstRef β) : AExpr β :=
  .forallE (.param 0) (.sort .zero) <| .forallE (.param 0) (.sort .zero) <|
  .forallE (.param 0) (.forallE .never (applied family (.bvar 1) (.bvar 0)) (.sort (.param 0))) <|
  .forallE (.param 0)
    (.forallE (.param 0) (arrow (.bvar 2) (.bvar 1))
      (.forallE (.param 0) (arrow (.bvar 2) (.bvar 3))
        (.app (.bvar 2) (introduction ctor (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))))) <|
  .forallE (.param 0) (applied family (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)

structure Interface (entries : Environment β) (family ctor recursor : ConstRef β) : Prop where
  former : entries.HasType family 0 type
  introduction : entries.HasType ctor 0 (introType family)
  elimination : entries.HasType recursor 1 (recType family ctor)

instance [DecidableEq β] (entries : Environment β) (family ctor recursor : ConstRef β) :
    Decidable (Interface entries family ctor recursor) :=
  decidable_of_iff (entries.HasType family 0 type ∧ entries.HasType ctor 0 (introType family) ∧
    entries.HasType recursor 1 (recType family ctor))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.former, h.introduction, h.elimination⟩⟩

theorem shape_type : (shape : Ordinary.Shape β).type = type := rfl
theorem shape_introType (source : β) : constructor.type shape source = introType (.member source 0) := rfl
theorem shape_recType (source : β) : shape.recursorType source .large =
    recType (.member source 0) (.ctor source 0 0) := rfl

theorem Interface.of_checked [DecidableEq β] {entries : Environment β} {store : Store β} {source recursor : β}
    (h : Ordinary.CheckedBlock.{u,v} entries store source recursor shape .large) :
    Interface (shape.publishedEnvironment entries source recursor .large)
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
  · exact ⟨shape.publishedRecursorEntry source recursor .large,
      Environment.insert_same .., rfl, shape_recType source⟩

variable {V : Type v} [SetTheory V]

noncomputable def implication (P Q : V) : V := piR 0 P (fun _ => Q)
noncomputable def value (constants : Assignment β V) (family : ConstRef β) (P Q : V) : V :=
  app (app (constants family []) P) Q
noncomputable def introValue (constants : Assignment β V) (ctor : ConstRef β) (P Q f g : V) : V :=
  app (app (app (app (constants ctor []) P) Q) f) g

theorem type_interp (constants : Assignment β V) (env : Nat → V) :
    interp constants [] env (type : AExpr β) =
      piR 1 univZero (fun _ => piR 1 univZero (fun _ => univZero)) := by
  simp [type, interp, VLevel.eval, univ_zero]

theorem introType_interp (constants : Assignment β V) (family : ConstRef β) (env : Nat → V) :
    interp constants [] env (introType family) =
      piR 0 univZero (fun P => piR 0 univZero (fun Q =>
        piR 0 (implication P Q) (fun _ => piR 0 (implication Q P) (fun _ => value constants family P Q)))) := by
  simp [introType, arrow, applied, implication, value, AExpr.appN, AExpr.liftN, liftVar,
    interp, VLevel.eval, Valuation.cons, univ_zero]

theorem recType_zero_interp (constants : Assignment β V) (family ctor : ConstRef β) (env : Nat → V) :
    interp constants [0] env (recType family ctor) =
      piR 0 univZero (fun P => piR 0 univZero (fun Q =>
        piR 0 (piR 1 (value constants family P Q) (fun _ => univZero)) (fun motive =>
          piR 0 (piR 0 (implication P Q) (fun f => piR 0 (implication Q P)
            (fun g => app motive (introValue constants ctor P Q f g))))
          (fun _ => piR 0 (value constants family P Q) (fun h => app motive h))))) := by
  simp [recType, arrow, applied, introduction, implication, value, introValue,
    AExpr.appN, AExpr.liftN, liftVar, interp, VLevel.eval, Valuation.cons, regime,
    PropWhen.param, PropWhen.always, PropWhen.holds, univ_zero]

variable {entries : Environment β} {family ctor recursor : ConstRef β}
  {constants : Assignment β V}

theorem value_mem_univZero (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {P Q : V} (hP : P ∈ˢ univZero) (hQ : Q ∈ˢ univZero) :
    value constants family P Q ∈ˢ univZero := by
  have ht := h.former.member hM (levels := []) rfl (fun _ => empty)
  rw [type_interp] at ht
  have h1 : app (constants family []) P ∈ˢ piR 1 univZero (fun _ => univZero) :=
    app_mem_piR_pos (by decide : 1 ≠ 0) ht hP
  exact app_mem_piR_pos (by decide : 1 ≠ 0) h1 hQ

theorem introValue_mem (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {P Q f g : V} (hP : P ∈ˢ univZero) (hQ : Q ∈ˢ univZero)
    (hf : f ∈ˢ implication P Q) (hg : g ∈ˢ implication Q P) :
    introValue constants ctor P Q f g ∈ˢ value constants family P Q := by
  have ht := h.introduction.member hM (levels := []) rfl (fun _ => empty)
  rw [introType_interp] at ht
  have h1 := app_mem_piR ht hP (fun _ _ _ => piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hQ (fun _ _ _ => piR_zero_mem_univZero)
  have h3 := app_mem_piR h2 hf (fun _ _ _ => piR_zero_mem_univZero)
  exact app_mem_piR h3 hg (fun _ _ _ => value_mem_univZero h hM hP hQ)

theorem eliminate (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {P Q C proof : V} (hP : P ∈ˢ univZero) (hQ : Q ∈ˢ univZero) (hC : C ∈ˢ univZero)
    (minor : ∀ f, f ∈ˢ implication P Q → ∀ g, g ∈ˢ implication Q P → (pt : V) ∈ˢ C)
    (hp : proof ∈ˢ value constants family P Q) : (pt : V) ∈ˢ C := by
  let motive := lamR 1 (value constants family P Q) (fun _ => C)
  have hm : motive ∈ˢ piR 1 (value constants family P Q) (fun _ => univZero) :=
    lamR_mem fun _ _ => hC
  let minorValue := lamR 0 (implication P Q) (fun _ => lamR 0 (implication Q P) (fun _ => pt))
  have hminor : minorValue ∈ˢ piR 0 (implication P Q) (fun f => piR 0 (implication Q P)
      (fun g => app motive (introValue constants ctor P Q f g))) := by
    apply lamR_mem
    intro f hf
    apply lamR_mem
    intro g hg
    rw [app_lamR_pos (by decide : 1 ≠ 0) (introValue_mem h hM hP hQ hf hg)]
    exact minor f hf g hg
  have hr := h.elimination.member hM (levels := [0]) rfl (fun _ => empty)
  rw [recType_zero_interp] at hr
  obtain ⟨rP, hrP⟩ := Equality.exists_of_mem_piR_zero hr hP
  obtain ⟨rQ, hrQ⟩ := Equality.exists_of_mem_piR_zero hrP hQ
  obtain ⟨rm, hrm⟩ := Equality.exists_of_mem_piR_zero hrQ hm
  obtain ⟨ri, hri⟩ := Equality.exists_of_mem_piR_zero hrm hminor
  obtain ⟨result, hresult⟩ := Equality.exists_of_mem_piR_zero hri hp
  rw [app_lamR_pos (by decide : 1 ≠ 0) hp] at hresult
  rwa [eq_pt_of_mem_univZero hC hresult] at hresult

theorem eq_of_mem (h : Interface entries family ctor recursor) (hM : Realizes constants entries)
    {P Q proof : V} (hP : P ∈ˢ univZero) (hQ : Q ∈ˢ univZero)
    (hp : proof ∈ˢ value constants family P Q) : P = Q := by
  have hf : (pt : V) ∈ˢ implication P Q := eliminate h hM hP hQ piR_zero_mem_univZero
    (fun f hf _ _ => by rwa [eq_pt_of_mem_piR_zero hf] at hf) hp
  have hg : (pt : V) ∈ˢ implication Q P := eliminate h hM hP hQ piR_zero_mem_univZero
    (fun _ _ g hg => by rwa [eq_pt_of_mem_piR_zero hg] at hg) hp
  apply univZero_ext hP hQ
  · intro hpt
    simpa only [app_pt] using app_mem_piR hf hpt (fun _ _ _ => hQ)
  · intro hpt
    simpa only [app_pt] using app_mem_piR hg hpt (fun _ _ _ => hP)

end Ix.Theory.Certified.Basis.Iff
