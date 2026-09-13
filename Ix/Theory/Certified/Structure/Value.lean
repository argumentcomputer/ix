/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Structure.Syntax

namespace Ix.Theory.Certified.Structure

open Model Model.SetTheory Model.SetTheory.Tower

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def projectValues (count : Nat) (x : V) : List V :=
  projList count (ssnd (sfst x))

theorem projectValues_length (count : Nat) (x : V) :
    (projectValues count x).length = count := projList_length ..

theorem projectValues_getD (count i : Nat) (x : V) (hi : i < count) :
    (projectValues count x).getD i empty = projectValue i x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
    (show i < (projectValues count x).length by simpa only [projectValues_length] using hi), Option.getD_some]
  exact projList_get count i (ssnd (sfst x)) hi

theorem projectValues_take (count i : Nat) (x : V) (hi : i ≤ count) :
    (projectValues count x).take i = projectValues i x := projList_take count i _ hi

theorem projectValues_node (count : Nat) (xs : List V) (hlen : xs.length = count) (g : V) :
    projectValues count (spair (inj 0 (mkTower xs)) g) = xs := by
  simp only [projectValues, sfst_spair, ssnd_inj, projList_mkTower _ _ hlen]

theorem projectValues_pt (count : Nat) :
    projectValues count (pt : V) = List.replicate count pt := by
  simp only [projectValues, sfst_pt, ssnd_pt, projList_pt]

namespace Description

variable (d : Description β) (constants : Assignment β V) (levels : List Nat) (env : Nat → V)

theorem positions_empty (xs : List V) (hlen : xs.length = d.constructor.fields.length) :
    d.ordinary.positions constants levels env (inj 0 (mkTower xs)) = empty := by
  apply ext
  intro p
  constructor
  · intro hp
    obtain ⟨j, field, _, hj, _, _⟩ := Ordinary.Shape.mem_positions
      (show d.ordinary.constructors[0]? = some d.constructor from rfl) hlen hp
    simp [constructor] at hj
  · intro hp
    exact (not_mem_empty p hp).elim

theorem branches_empty (xs : List V) (hlen : xs.length = d.constructor.fields.length) :
    d.ordinary.branches constants levels env d.constructor 0 xs [] = empty := by
  rw [Ordinary.Shape.branches, d.positions_empty constants levels env xs hlen]
  apply ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, _⟩ := mem_graph.mp hp
    exact (not_mem_empty x hx).elim
  · intro hp
    exact (not_mem_empty p hp).elim

theorem constructorValue_eq (xs : List V) (hlen : xs.length = d.constructor.fields.length) :
    d.ordinary.constructorValue constants levels env d.constructor 0 xs [] =
      IndexedContainer.node (d.level.eval levels) (inj 0 (mkTower xs)) empty := by
  rw [Ordinary.Shape.constructorValue, d.branches_empty constants levels env xs hlen]
  rfl

variable {d constants levels env} {entries : Environment β} {store : Store β} {source : β}

theorem carrier_member (h : Ordinary.CheckedShape.{u,v} entries store source d.ordinary)
    (hM : Realizes constants entries) (hΓ : d.ordinary.parameterContext.Valid constants levels env)
    {x : V} (hx : x ∈ˢ app (d.ordinary.carrier constants levels env) pt) :
    ∃ xs, FitsS (Telescope.interpret constants levels env d.constructor.fields) xs ∧
      x = IndexedContainer.node (d.level.eval levels) (inj 0 (mkTower xs)) empty := by
  rw [Ordinary.Shape.carrier, IndexedContainer.carrier_eq (Ordinary.Shape.container_wf h hM hΓ)
    (show (pt : V) ∈ˢ (d.ordinary.container constants levels env).indices from pt_mem_unitSet)] at hx
  obtain ⟨a, ha, g, hg, rfl⟩ := IndexedContainer.mem_fibre.mp hx
  obtain ⟨i, ctor, xs, hc, hxs, rfl⟩ := Ordinary.Shape.mem_allShapes (mem_sep.mp ha).1
  have hi : i = 0 := by
    have hi := (List.getElem?_eq_some_iff.mp hc).1
    simp only [ordinary, List.length_singleton] at hi
    omega
  subst i
  have he : ctor = d.constructor := by simpa only [ordinary, List.getElem?_cons_zero, Option.some.injEq] using hc.symm
  subst ctor
  have hg' : g = empty := by
    change g ∈ˢ piSet (d.ordinary.positions constants levels env _) _ at hg
    rw [d.positions_empty constants levels env xs (FitsS.length_eq hxs)] at hg
    rw [← eq_graph_app_of_mem_piSet hg]
    apply ext
    intro p
    constructor
    · intro hp
      obtain ⟨x, hx, _⟩ := mem_graph.mp hp
      exact (not_mem_empty x hx).elim
    · intro hp
      exact (not_mem_empty p hp).elim
  exact ⟨xs, hxs, congrArg (IndexedContainer.node (d.level.eval levels) (inj 0 (mkTower xs))) hg'⟩

theorem projections_fit (h : Ordinary.CheckedShape.{u,v} entries store source d.ordinary)
    (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hM : Realizes constants entries) (hΓ : d.ordinary.parameterContext.Valid constants levels env)
    {x : V} (hx : x ∈ˢ app (d.ordinary.carrier constants levels env) pt) :
    FitsS (Telescope.interpret constants levels env d.constructor.fields) (projectValues d.fields.length x) := by
  obtain ⟨xs, hxs, rfl⟩ := carrier_member h hM hΓ hx
  have hlen : xs.length = d.fields.length := by simpa [constructor] using FitsS.length_eq hxs
  by_cases hw : d.level.eval levels = 0
  · rw [IndexedContainer.node, if_pos hw, projectValues_pt]
    simpa only [constructor, List.length_map] using fitsS_replicate_of_prop (hF.prop V constants hM levels env hΓ hw) hxs
  · rw [IndexedContainer.node, if_neg hw, projectValues_node _ xs hlen]
    exact hxs

theorem constructor_eta (h : Ordinary.CheckedShape.{u,v} entries store source d.ordinary)
    (hM : Realizes constants entries) (hΓ : d.ordinary.parameterContext.Valid constants levels env)
    {x : V} (hx : x ∈ˢ app (d.ordinary.carrier constants levels env) pt) :
    d.ordinary.constructorValue constants levels env d.constructor 0 (projectValues d.fields.length x) [] = x := by
  obtain ⟨xs, hxs, rfl⟩ := carrier_member h hM hΓ hx
  rw [d.constructorValue_eq constants levels env _ (by simp [constructor, projectValues_length])]
  by_cases hw : d.level.eval levels = 0
  · simp only [IndexedContainer.node, if_pos hw]
  · simp only [IndexedContainer.node, if_neg hw,
      projectValues_node _ xs (by simpa [constructor] using FitsS.length_eq hxs)]

theorem constructor_iota (hF : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields)
    (hM : Realizes constants entries) (hΓ : d.ordinary.parameterContext.Valid constants levels env)
    {xs : List V} (hxs : FitsS (Telescope.interpret constants levels env d.constructor.fields) xs) :
    projectValues d.fields.length (d.ordinary.constructorValue constants levels env d.constructor 0 xs []) = xs := by
  have hlen := FitsS.length_eq hxs
  rw [d.constructorValue_eq constants levels env xs hlen]
  by_cases hw : d.level.eval levels = 0
  · rw [IndexedContainer.node, if_pos hw, projectValues_pt]
    exact Telescope.fits_unique_of_prop (hF.prop V constants hM levels env hΓ hw)
      (by simpa only [List.length_map] using fitsS_replicate_of_prop (hF.prop V constants hM levels env hΓ hw) hxs) hxs
  · rw [IndexedContainer.node, if_neg hw, projectValues_node _ xs (by simpa [constructor] using hlen)]

end Description
end Ix.Theory.Certified.Structure
