/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Eliminator

namespace Ix.Theory.Certified.Ordinary.Shape

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Model.InductiveCodes

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def recursiveCall (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (minors : List V)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    (xs fs : List V) (j : Nat) (field : RecursiveField β) : V :=
  Telescope.curry v (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) fun ys =>
    Telescope.applyN (shape.largeValue constants levels env v m minors hD hlarge)
      (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys)) ++
        [Telescope.applyN (fs.getD j empty) ys])

noncomputable def recursiveCalls (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (minors : List V)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    (ctor : Constructor β) (xs fs : List V) : List V :=
  ctor.recursive.zipIdx.map fun (field, j) =>
    shape.recursiveCall constants levels env v m minors hD hlarge xs fs j field

variable {entries : Environment β} {store : Store β} {source : β} {shape : Shape β}
  {constants : Assignment β V} {levels : List Nat} {env : Nat → V}

theorem ihValue_childResults (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    {i j : Nat} {ctor : Constructor β} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs)
    {index : V} (hi : index ∈ˢ shape.indexSet constants levels env)
    (ha : inj i (mkTower xs) ∈ˢ (shape.container constants levels env).shapes index)
    {g : V} (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p)))
    (he : g = shape.branches constants levels env ctor i xs fs) :
    shape.ihValue constants levels env v xs j field
      (IndexedContainer.childResults hD hi ha hg
        (IndexedContainer.fold hD hlarge (shape.algebra constants levels env v m minors))) =
      shape.recursiveCall constants levels env v m minors hD hlarge xs fs j field := by
  subst g
  have hctor := h.constructors ctor (List.mem_of_getElem? hc)
  have hfield := hctor.2.2.2.2 field (List.mem_of_getElem? hf)
  apply Telescope.curry_congr
  intro ys hy
  have hp := inj_mem_positions hc hf (FitsS.length_eq hx) hy
  have ht := recursiveTarget_fits hctor hfield hM hΓ hx hy
  have hchild := Telescope.applyN_mem _ (hfs.get hf) hy (recursiveResult_zero hctor hfield hM hΓ hx)
  rw [IndexedContainer.app_childResults hD hi ha hg _ hp,
    largeValue_apply h hM hΓ hm hminors hD hlarge ht hchild,
    IndexedContainer.foldAt_eq hD hlarge _ (mkTower_mem (by decide : 1 ≠ 0) ht) hchild]
  apply congrArg (IndexedContainer.fold hD hlarge (shape.algebra constants levels env v m minors))
  apply Subtype.ext
  simp only [IndexedContainer.child, container,
    targetIndex_inj constants levels env hc hf (FitsS.length_eq hx) (FitsS.length_eq hy),
    app_branches hc hf (FitsS.length_eq hx) hy]

theorem ihValues_childResults (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs)
    {index : V} (hi : index ∈ˢ shape.indexSet constants levels env)
    (ha : inj i (mkTower xs) ∈ˢ (shape.container constants levels env).shapes index)
    {g : V} (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p)))
    (he : g = shape.branches constants levels env ctor i xs fs) :
    shape.ihValues constants levels env v ctor xs
      (IndexedContainer.childResults hD hi ha hg
        (IndexedContainer.fold hD hlarge (shape.algebra constants levels env v m minors))) =
      shape.recursiveCalls constants levels env v m minors hD hlarge ctor xs fs := by
  apply List.ext_getElem?
  intro j
  simp only [ihValues, recursiveCalls, List.getElem?_map, List.getElem?_zipIdx]
  cases hf : ctor.recursive[j]? with
  | none => rfl
  | some field =>
    simp only [Option.map_some, Nat.zero_add]
    exact congrArg some (ihValue_childResults h hM hΓ hm hminors hD hlarge hc hf hx hfs hi ha hg he)

/-- Semantic iota at the original constructor's result indices, with one
recursive call for each source field and every functional argument. -/
theorem largeValue_iota (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    Telescope.applyN (shape.largeValue constants levels env v m minors hD hlarge)
      (ctor.indices.map (interp constants levels (Telescope.extend env xs)) ++
        [shape.constructorValue constants levels env ctor i xs fs]) =
      Telescope.applyN (minors.getD i empty)
        (xs ++ fs ++ shape.recursiveCalls constants levels env v m minors hD hlarge ctor xs fs) := by
  have hctor := h.constructors ctor (List.mem_of_getElem? hc)
  have ht := constructorResult_fits hctor hM hΓ hx
  have hi := constructorResult_mem hctor hM hΓ hx
  have ha : inj i (mkTower xs) ∈ˢ (shape.container constants levels env).shapes
      (mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs)))) :=
    mem_sep.mpr ⟨inj_mem_allShapes hc hx, resultIndex_inj constants levels env hc (FitsS.length_eq hx)⟩
  have hg := branches_mem hc hctor hM hΓ hx hfs
  have hx' := constructorValue_mem h hM hΓ hc hx hfs
  rw [largeValue_apply h hM hΓ hm hminors hD hlarge ht hx',
    IndexedContainer.foldAt_eq hD hlarge _ hi hx']
  change IndexedContainer.fold hD hlarge _ ⟨(_, IndexedContainer.node _ _ _), _⟩ = _
  rw [IndexedContainer.fold_node hD hlarge _ hi ha hg]
  simp only [algebra, tag_inj, hc, ordinaryValues_inj _ (FitsS.length_eq hx)]
  rw [decodeFields_branches hc hctor hM hΓ hx hfs,
    ihValues_childResults h hM hΓ hm hminors hD hlarge hc hx hfs hi ha hg rfl]

end Ix.Theory.Certified.Ordinary.Shape
