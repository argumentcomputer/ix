/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Structure.Value

namespace Ix.Theory.Certified.Structure

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

theorem FieldsFormed.field_reading {entries : Environment β} {w : VLevel} {Γ : Context β}
    {fields : List (Field β)} (h : FieldsFormed.{u,v} entries w Γ fields)
    (constants : Assignment β V) (hM : Realizes constants entries) (levels : List Nat)
    {env : Nat → V} (hΓ : Γ.Valid constants levels env) {xs : List V}
    (hxs : FitsS (Telescope.interpret constants levels env (fields.map Field.domain)) xs)
    {i : Nat} {field : Field β} (hf : fields[i]? = some field) :
    WellDenoted constants levels (Telescope.extend env (xs.take i)) field.domain ∧
      interp constants levels (Telescope.extend env (xs.take i)) field.domain ∈ˢ
        (univ (field.level.eval levels) : V) ∧
      xs.getD i empty ∈ˢ interp constants levels (Telescope.extend env (xs.take i)) field.domain := by
  induction h generalizing env xs i with
  | nil => simp at hf
  | @cons Γ head rest hA hz htail ih =>
    cases xs with
    | nil => exact hxs.elim
    | cons x xs =>
      have ht := hA V constants hM levels env hΓ
      cases i with
      | zero =>
        cases Option.some.inj hf
        exact ⟨ht.1, ht.2.2, hxs.1⟩
      | succ i =>
        exact ih (hΓ.push ht.1 hxs.1) hxs.2 hf

theorem projections_interp (source : β) (count : Nat) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    (projections source count).map (interp constants levels env) = projectValues count (env 0) := by
  apply List.ext_get (by simp [projections, projectValues_length])
  intro i hi hj
  have hic : i < count := by simpa [projections] using hi
  simpa only [List.get_eq_getElem, projections, List.getElem_map, List.getElem_range, interp, projectValue, projectValues] using
    (projList_get count i (ssnd (sfst (env 0))) hic).symm

theorem projectionValuation (env : Nat → V) (x : V) (i : Nat) :
    Valuation.skip 1 i (Telescope.extend (Valuation.cons x env) (projectValues i x)) =
      Telescope.extend env (projectValues i x) := by
  simpa only [projectValues_length, Nat.add_zero, Valuation.skip_succ_cons, Valuation.skip_zero] using
    Telescope.skip_extend_at (Valuation.cons x env) (projectValues i x) 1 0

theorem fieldResult_interp (source : β) (i : Nat) (field : Field β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (x : V) :
    interp constants levels (Valuation.cons x env) (fieldResult source i field) =
      interp constants levels (Telescope.extend env (projectValues i x)) field.domain := by
  rw [fieldResult, AExpr.interp_instRev, projections_interp, interp_liftN]
  exact congrArg (fun env => interp constants levels env field.domain) (projectionValuation env x i)

theorem fieldResult_wellDenoted (source : β) (i : Nat) (field : Field β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (x : V)
    (hf : WellDenoted constants levels (Telescope.extend env (projectValues i x)) field.domain) :
    WellDenoted constants levels (Valuation.cons x env) (fieldResult source i field) := by
  apply AExpr.wellDenoted_instRev
  · intro e he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    trivial
  · rw [projections_interp, wellDenoted_liftN]
    simpa only [Valuation.cons, projectionValuation] using hf

namespace Description

variable {d : Description β} {entries : Environment β} {store : Store β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat}

/-- The dependent result uses the projections of the very same major value.
Its formation is derived from the checked field telescope in the old model. -/
theorem fieldResult_meaning (h : Ordinary.CheckedShape.{u,v} entries store source d.ordinary)
    (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hr : Ordinary.FamilyReading entries d.ordinary source constants reading)
    (hM : Realizes constants entries) {env : Nat → V}
    (hΓ : d.ordinary.parameterContext.Valid constants levels env) {i : Nat} {field : Field β}
    (hi : d.fields[i]? = some field) {x : V}
    (hx : x ∈ˢ app (d.ordinary.carrier constants levels env) pt) :
    WellDenoted reading levels (Valuation.cons x env) (fieldResult source i field) ∧
      interp reading levels (Valuation.cons x env) (fieldResult source i field) ∈ˢ
        (univ (field.level.eval levels) : V) ∧
      projectValue i x ∈ˢ interp reading levels (Valuation.cons x env) (fieldResult source i field) := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  have hxs := d.projections_fit h hF hM hΓ hx
  have ht := hF.field_reading constants hM levels hΓ hxs hi
  rw [projectValues_take _ _ _ (Nat.le_of_lt hib), projectValues_getD _ _ _ hib] at ht
  have href : field.domain.ReferencesIn entries :=
    (h.constructors d.constructor (by simp [ordinary])).1 field.domain
      (by simpa [constructor] using List.mem_map.mpr ⟨field, List.mem_of_getElem? hi, rfl⟩)
  refine ⟨fieldResult_wellDenoted source i field reading levels env x ?_, ?_, ?_⟩
  · exact (hr.agrees.wellDenoted href levels _).mpr ht.1
  · rw [fieldResult_interp, hr.agrees.interp href]
    exact ht.2.1
  · rw [fieldResult_interp, hr.agrees.interp href]
    exact ht.2.2

theorem projection_meaning (h : Ordinary.CheckedShape.{u,v} entries store source d.ordinary)
    (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hr : Ordinary.FamilyReading entries d.ordinary source constants reading)
    (hM : Realizes constants entries) (hn : levels.length = d.universes)
    {stage : Environment β} (hstage : Realizes reading stage)
    (hD : Telescope.Formed.{u,v} stage [] (d.projectionDomains source))
    {i : Nat} {field : Field β} (hi : d.fields[i]? = some field)
    (hs : (d.projection source i field).Scope d.universes 0 ∧
      (d.projectionType source i field).Scope d.universes 0) (env : Nat → V) :
    (ConstantFact.typed (d.projection source i field) (d.projectionType source i field)).Meaning
      reading (.member source 0) levels env := by
  obtain ⟨_, _, ht⟩ := hD.lamN_semantics reading hstage levels
    (.proj (.member source 0) i (.bvar 0)) (fieldResult source i field) field.level
  have hm := ht (fun _ => empty) (Context.valid_nil reading levels (fun _ => empty)) (by
    intro args hargs
    obtain ⟨ps, zs, rfl, hps, hzs⟩ := (Telescope.fits_append_iff reading levels (fun _ => empty)
      d.parameters [d.ordinary.familyApp source 0 []] args).mp hargs
    have hp := hr.agrees.telescope (fun A hA => h.references A (by simpa [ordinary] using hA)) levels (fun _ => empty)
    rw [hp] at hps
    cases zs with
    | nil => exact hzs.elim
    | cons x rest =>
      cases rest with
      | cons _ _ => exact hzs.2.elim
      | nil =>
        have he := Ordinary.Shape.familyApp_interp hr hn (extra := []) (indices := []) hps (by trivial)
        have hx : x ∈ˢ app (d.ordinary.carrier constants levels (Telescope.extend (fun _ => empty) ps)) pt := by
          simpa only [List.length_nil, List.map_nil, mkTower, Telescope.extend] using he ▸ hzs.1
        have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
        have ht := d.fieldResult_meaning h hF hr hM hΓ hi hx
        simpa only [Telescope.extend_append, Telescope.extend, interp, Valuation.cons_zero, WellDenoted] using
          (show True ∧ WellDenoted reading levels (Valuation.cons x (Telescope.extend (fun _ => empty) ps))
              (fieldResult source i field) ∧
            projectValue i x ∈ˢ interp reading levels (Valuation.cons x (Telescope.extend (fun _ => empty) ps))
              (fieldResult source i field) ∧
            interp reading levels (Valuation.cons x (Telescope.extend (fun _ => empty) ps))
              (fieldResult source i field) ∈ˢ (univ (field.level.eval levels) : V) from
            ⟨trivial, ht.1, ht.2.2, ht.2.1⟩))
  refine ⟨(wellDenoted_closed _ reading levels hs.1 (fun _ => empty) env).mp hm.1,
    (wellDenoted_closed _ reading levels hs.2 (fun _ => empty) env).mp hm.2.1, ?_⟩
  rw [← interp_closed _ reading levels hs.1 (fun _ => empty) env,
    ← interp_closed _ reading levels hs.2 (fun _ => empty) env]
  exact hm.2.2.1

end Description
end Ix.Theory.Certified.Structure
