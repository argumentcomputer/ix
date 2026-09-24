/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/Container.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Shape
import Ix.Kernel.Model.Inductive.Container
import Ix.Kernel.Model.Inductive.Codes

/-!
Construct the indexed container from the exact checked source description.
Shapes contain a constructor tag and its ordinary fields. Positions contain
a recursive-field tag and that function field's arguments. Indices are
dependent tuple codes. No carrier, closed member, or semantic law is supplied
by the witness.
-/

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.InductiveCodes

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

namespace Shape

noncomputable def indexSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : V := towerSet 1 (Telescope.interpret constants levels env shape.indices)

noncomputable def ordinaryValues (ctor : Constructor β) (a : V) : List V :=
  projList ctor.fields.length (ssnd a)

noncomputable def ordinaryEnv (ctor : Constructor β) (env : Nat → V) (a : V) : Nat → V :=
  Telescope.extend env (ordinaryValues ctor a)

noncomputable def ordinaryFibre (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (i : Nat) : V :=
  match shape.constructors[i]? with
  | none => empty
  | some ctor => towerSet 1 (Telescope.interpret constants levels env ctor.fields)

noncomputable def allShapes (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) : V := sumSet 1 (shape.ordinaryFibre constants levels env)

noncomputable def resultIndex (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (a : V) : V :=
  match shape.constructors[tag a]? with
  | none => empty
  | some ctor => mkTower (ctor.indices.map (interp constants levels (ordinaryEnv ctor env a)))

noncomputable def positionFibre (ctor : Constructor β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (a : V) (i : Nat) : V :=
  match ctor.recursive[i]? with
  | none => empty
  | some field => towerSet 1 (Telescope.interpret constants levels (ordinaryEnv ctor env a) field.domains)

noncomputable def positions (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (a : V) : V :=
  match shape.constructors[tag a]? with
  | none => empty
  | some ctor => sumSet 1 (positionFibre ctor constants levels env a)

noncomputable def targetIndex (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) (a p : V) : V :=
  match shape.constructors[tag a]? with
  | none => empty
  | some ctor =>
    match ctor.recursive[tag p]? with
    | none => empty
    | some field =>
      let args := projList field.domains.length (ssnd p)
      let extended := Telescope.extend (ordinaryEnv ctor env a) args
      mkTower (field.indices.map (interp constants levels extended))

noncomputable def container (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) : IndexedContainer V where
  indices := shape.indexSet constants levels env
  shapes i := sep (shape.allShapes constants levels env)
    (fun a => shape.resultIndex constants levels env a = i)
  positions := shape.positions constants levels env
  target := shape.targetIndex constants levels env

theorem ordinaryValues_inj {ctor : Constructor β} (i : Nat) {xs : List V}
    (hlen : xs.length = ctor.fields.length) :
    ordinaryValues ctor (inj i (mkTower xs)) = xs := by
  simp only [ordinaryValues, ssnd_inj, projList_mkTower _ _ hlen]

theorem ordinaryEnv_inj {ctor : Constructor β} (env : Nat → V) (i : Nat) {xs : List V}
    (hlen : xs.length = ctor.fields.length) :
    ordinaryEnv ctor env (inj i (mkTower xs)) = Telescope.extend env xs := by
  rw [ordinaryEnv, ordinaryValues_inj i hlen]

theorem resultIndex_inj {shape : Shape β} (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor)
    {xs : List V} (hlen : xs.length = ctor.fields.length) :
    shape.resultIndex constants levels env (inj i (mkTower xs)) =
      mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs))) := by
  simp only [resultIndex, tag_inj, hc, ordinaryEnv_inj env i hlen]

theorem positions_inj {shape : Shape β} (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) (x : V) :
    shape.positions constants levels env (inj i x) =
      sumSet 1 (positionFibre ctor constants levels env (inj i x)) := by
  simp only [positions, tag_inj, hc]

theorem targetIndex_inj {shape : Shape β} (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) {i j : Nat} {ctor : Constructor β} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    {xs ys : List V} (hx : xs.length = ctor.fields.length) (hy : ys.length = field.domains.length) :
    shape.targetIndex constants levels env (inj i (mkTower xs)) (inj j (mkTower ys)) =
      mkTower (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys))) := by
  simp only [targetIndex, tag_inj, hc, hf, ssnd_inj,
    projList_mkTower _ _ hy, ordinaryEnv_inj env i hx]

theorem mem_allShapes {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {a : V} (ha : a ∈ˢ shape.allShapes constants levels env) :
    ∃ i ctor xs, shape.constructors[i]? = some ctor ∧
      FitsS (Telescope.interpret constants levels env ctor.fields) xs ∧ a = inj i (mkTower xs) := by
  obtain ⟨i, x, hx, rfl⟩ := sumSet_elim (by decide : 1 ≠ 0) ha
  cases hc : shape.constructors[i]? with
  | none =>
    simp only [ordinaryFibre, hc] at hx
    exact (not_mem_empty x hx).elim
  | some ctor =>
    simp only [ordinaryFibre, hc] at hx
    obtain ⟨hfit, he⟩ := towerSet_elim (by decide : 1 ≠ 0) _ hx
    exact ⟨i, ctor, _, hc, hfit, congrArg (inj i) he⟩

theorem mem_positions {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor)
    {xs : List V} (hx : xs.length = ctor.fields.length) {p : V}
    (hp : p ∈ˢ shape.positions constants levels env (inj i (mkTower xs))) :
    ∃ j field ys, ctor.recursive[j]? = some field ∧
      FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys ∧
      p = inj j (mkTower ys) := by
  rw [positions_inj constants levels env hc] at hp
  obtain ⟨j, y, hy, rfl⟩ := sumSet_elim (by decide : 1 ≠ 0) hp
  cases hf : ctor.recursive[j]? with
  | none =>
    simp only [positionFibre, hf] at hy
    exact (not_mem_empty y hy).elim
  | some field =>
    simp only [positionFibre, hf, ordinaryEnv_inj env i hx] at hy
    obtain ⟨hfit, he⟩ := towerSet_elim (by decide : 1 ≠ 0) _ hy
    exact ⟨j, field, _, hf, hfit, congrArg (inj j) he⟩

theorem inj_mem_allShapes {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor)
    {xs : List V} (hxs : FitsS (Telescope.interpret constants levels env ctor.fields) xs) :
    inj i (mkTower xs) ∈ˢ shape.allShapes constants levels env := by
  apply inj_mem (by decide : 1 ≠ 0)
  simpa only [ordinaryFibre, hc] using mkTower_mem (by decide : 1 ≠ 0) hxs

theorem inj_mem_positions {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {i j : Nat} {ctor : Constructor β} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    {xs ys : List V} (hx : xs.length = ctor.fields.length)
    (hys : FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys) :
    inj j (mkTower ys) ∈ˢ shape.positions constants levels env (inj i (mkTower xs)) := by
  rw [positions_inj constants levels env hc]
  apply inj_mem (by decide : 1 ≠ 0)
  simpa only [positionFibre, hf, ordinaryEnv_inj env i hx] using
    mkTower_mem (by decide : 1 ≠ 0) hys

variable {entries : Environment β} {shape : Shape β} {constants : Assignment β V}
  {levels : List Nat} {env : Nat → V}

theorem constructorResult_fits {ctor : Constructor β}
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) :
    FitsS (Telescope.interpret constants levels env shape.indices)
      (ctor.indices.map (interp constants levels (Telescope.extend env xs))) := by
  have hΓ' := h.2.1.valid constants hM levels hΓ hx
  have ht := h.2.2.2.1 V constants hM levels (Telescope.extend env xs) hΓ'
  have ht' := (Telescope.fits_lift constants levels (Telescope.extend env xs)
    ctor.fields.length shape.indices 0 _).mp ht
  rw [← FitsS.length_eq hx, Telescope.skip_extend] at ht'
  exact ht'

theorem constructorResult_mem {ctor : Constructor β}
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) :
    mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs))) ∈ˢ
      shape.indexSet constants levels env :=
  mkTower_mem (by decide : 1 ≠ 0) (constructorResult_fits h hM hΓ hx)

theorem recursiveTarget_fits {ctor : Constructor β} {field : RecursiveField β}
    (h : ConstructorEvidence.{u,v} entries shape ctor)
    (hr : RecursiveEvidence.{u,v} entries shape ctor field) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs ys : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hy : FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys) :
    FitsS (Telescope.interpret constants levels env shape.indices)
      (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys))) := by
  have hΓ' := h.2.1.valid constants hM levels hΓ hx
  have hΓ'' := hr.2.1.valid constants hM levels hΓ' hy
  have ht := hr.2.2.2 V constants hM levels _ hΓ''
  have ht' := (Telescope.fits_lift constants levels (Telescope.extend (Telescope.extend env xs) ys)
    (ctor.fields.length + field.domains.length) shape.indices 0 _).mp ht
  rw [← Telescope.extend_append, ← FitsS.length_eq hx, ← FitsS.length_eq hy,
    ← List.length_append, Telescope.skip_extend] at ht'
  simpa only [Telescope.extend_append] using ht'

theorem recursiveTarget_mem {ctor : Constructor β} {field : RecursiveField β}
    (h : ConstructorEvidence.{u,v} entries shape ctor)
    (hr : RecursiveEvidence.{u,v} entries shape ctor field) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs ys : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hy : FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys) :
    mkTower (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys))) ∈ˢ
      shape.indexSet constants levels env :=
  mkTower_mem (by decide : 1 ≠ 0) (recursiveTarget_fits h hr hM hΓ hx hy)

theorem allShapes_mem
    (h : ∀ ctor ∈ shape.constructors, ConstructorEvidence.{u,v} entries shape ctor)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    (hw : shape.level.eval levels ≠ 0) :
    shape.allShapes constants levels env ∈ˢ (univ (shape.level.eval levels) : V) := by
  apply sum_graph_mem hw
  intro i
  cases hc : shape.constructors[i]? with
  | none => simpa only [ordinaryFibre, hc] using empty_mem_univ (V := V) (shape.level.eval levels)
  | some ctor =>
    simp only [ordinaryFibre, hc]
    apply Telescope.tower_graph_mem hw
    exact (h ctor (List.mem_of_getElem? hc)).2.2.1 shape.level rfl V constants hM levels env hΓ hw

/-- Every fixed-point premise is produced from checked field sorts and
dependent index applications. In particular, target-index membership is not
an assumed container property of the input. -/
theorem container_wf {source : β}
    (h : CheckedShape.{u,v} entries source shape) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) :
    (shape.container constants levels env).WF (shape.level.eval levels) := by
  constructor
  · intro hw i hi
    exact univ_sep_mem (allShapes_mem h.constructors hM hΓ hw)
  · intro hw i a hi ha
    obtain ⟨ha, _⟩ := mem_sep.mp ha
    obtain ⟨j, ctor, xs, hc, hxs, rfl⟩ := mem_allShapes ha
    change shape.positions constants levels env _ ∈ˢ _
    rw [positions_inj constants levels env hc]
    apply sum_graph_mem hw
    intro k
    cases hf : ctor.recursive[k]? with
    | none => simpa only [positionFibre, hf] using empty_mem_univ (V := V) (shape.level.eval levels)
    | some field =>
      simp only [positionFibre, hf, ordinaryEnv_inj env j (FitsS.length_eq hxs)]
      apply Telescope.tower_graph_mem hw
      have hctor := h.constructors ctor (List.mem_of_getElem? hc)
      have hfield := hctor.2.2.2.2 field (List.mem_of_getElem? hf)
      exact hfield.2.2.1 shape.level rfl V constants hM levels _
        (hctor.2.1.valid constants hM levels hΓ hxs) hw
  · intro i a p hi ha hp
    obtain ⟨ha, _⟩ := mem_sep.mp ha
    obtain ⟨j, ctor, xs, hc, hxs, rfl⟩ := mem_allShapes ha
    obtain ⟨k, field, ys, hf, hys, rfl⟩ := mem_positions hc (FitsS.length_eq hxs) hp
    change shape.targetIndex constants levels env _ _ ∈ˢ shape.indexSet constants levels env
    rw [targetIndex_inj constants levels env hc hf (FitsS.length_eq hxs) (FitsS.length_eq hys)]
    have hctor := h.constructors ctor (List.mem_of_getElem? hc)
    exact recursiveTarget_mem hctor (hctor.2.2.2.2 field (List.mem_of_getElem? hf)) hM hΓ hxs hys

end Shape
end Ix.Kernel.Certified.Ordinary
