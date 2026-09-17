/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/Constructors.lean
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

import Ix.Kernel.Certified.Ordinary.Container

namespace Ix.Kernel.Certified.Ordinary.Shape

open Model Model.SetTheory Model.SetTheory.Tower Model.InductiveCodes

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def carrier (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : V := (shape.container constants levels env).carrier (shape.level.eval levels)

noncomputable def recursiveSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (xs : List V) (field : RecursiveField β) : V :=
  Telescope.piN (shape.level.eval levels)
    (Telescope.interpret constants levels (Telescope.extend env xs) field.domains)
    (fun ys => app (shape.carrier constants levels env)
      (mkTower (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys)))))

def RecursiveValuesFit (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ctor : Constructor β) (xs fs : List V) : Prop :=
  FitsS (Telescope.simple (ctor.recursive.map (shape.recursiveSet constants levels env xs))) fs

noncomputable def branchBody (ctor : Constructor β) (fs : List V) (p : V) : V :=
  match ctor.recursive[tag p]? with
  | none => empty
  | some field => Telescope.applyN (fs.getD (tag p) empty) (projList field.domains.length (ssnd p))

noncomputable def branches (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ctor : Constructor β) (i : Nat) (xs fs : List V) : V :=
  graph (branchBody ctor fs) (shape.positions constants levels env (inj i (mkTower xs)))

noncomputable def constructorValue (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ctor : Constructor β) (i : Nat) (xs fs : List V) : V :=
  IndexedContainer.node (shape.level.eval levels) (inj i (mkTower xs))
    (shape.branches constants levels env ctor i xs fs)

theorem RecursiveValuesFit.get {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {ctor : Constructor β} {xs fs : List V}
    (h : shape.RecursiveValuesFit constants levels env ctor xs fs)
    {j : Nat} {field : RecursiveField β} (hf : ctor.recursive[j]? = some field) :
    fs.getD j empty ∈ˢ shape.recursiveSet constants levels env xs field := by
  apply Telescope.fits_simple_getD h
  simp only [List.getElem?_map, hf, Option.map_some]

theorem app_branches {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {ctor : Constructor β} {field : RecursiveField β} {i j : Nat}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    {xs ys fs : List V} (hx : xs.length = ctor.fields.length)
    (hy : FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys) :
    app (shape.branches constants levels env ctor i xs fs) (inj j (mkTower ys)) =
      Telescope.applyN (fs.getD j empty) ys := by
  rw [branches, app_graph (inj_mem_positions hc hf hx hy)]
  simp only [branchBody, tag_inj, hf, ssnd_inj, projList_mkTower _ _ (FitsS.length_eq hy)]

variable {entries : Environment β} {shape : Shape β} {constants : Assignment β V}
  {levels : List Nat} {env : Nat → V} {ctor : Constructor β}

theorem recursiveSet_mem_univ {field : RecursiveField β}
    (h : ConstructorEvidence.{u,v} entries shape ctor)
    (hr : RecursiveEvidence.{u,v} entries shape ctor field) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) :
    shape.recursiveSet constants levels env xs field ∈ˢ (univ (shape.level.eval levels) : V) := by
  apply Telescope.piN_mem_univ
  · exact fun hw => hr.2.2.1 shape.level rfl V constants hM levels _
      (h.2.1.valid constants hM levels hΓ hx) hw
  · intro ys hy
    exact (shape.container constants levels env).carrier_fibre_mem (shape.level.eval levels)
      (recursiveTarget_mem h hr hM hΓ hx hy)

theorem recursiveResult_zero {field : RecursiveField β}
    (h : ConstructorEvidence.{u,v} entries shape ctor)
    (hr : RecursiveEvidence.{u,v} entries shape ctor field) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hw : shape.level.eval levels = 0) :
    ∀ ys, FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys →
      app (shape.carrier constants levels env)
        (mkTower (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys))))
          ∈ˢ (univZero : V) := by
  intro ys hy
  have hm := (shape.container constants levels env).carrier_fibre_mem (shape.level.eval levels)
    (recursiveTarget_mem h hr hM hΓ hx hy)
  simpa only [hw, univ_zero, carrier] using hm

theorem branches_mem {i : Nat} (hc : shape.constructors[i]? = some ctor)
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    shape.branches constants levels env ctor i xs fs ∈ˢ
      piSet (shape.positions constants levels env (inj i (mkTower xs)))
        (fun p => app (shape.carrier constants levels env)
          (shape.targetIndex constants levels env (inj i (mkTower xs)) p)) := by
  apply graph_mem_piSet
  intro p hp
  obtain ⟨j, field, ys, hf, hy, rfl⟩ := mem_positions hc (FitsS.length_eq hx) hp
  simp only [branchBody, tag_inj, hf, ssnd_inj, projList_mkTower _ _ (FitsS.length_eq hy),
    targetIndex_inj constants levels env hc hf (FitsS.length_eq hx) (FitsS.length_eq hy)]
  exact Telescope.applyN_mem _ (hfs.get hf) hy
    (recursiveResult_zero h (h.2.2.2.2 field (List.mem_of_getElem? hf)) hM hΓ hx)

theorem constructorValue_mem {source : β}
    (h : CheckedShape.{u,v} entries source shape) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {i : Nat}
    (hc : shape.constructors[i]? = some ctor) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    shape.constructorValue constants levels env ctor i xs fs ∈ˢ
      app (shape.carrier constants levels env)
        (mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs)))) := by
  have hctor := h.constructors ctor (List.mem_of_getElem? hc)
  apply IndexedContainer.node_mem_carrier (container_wf h hM hΓ)
    (constructorResult_mem hctor hM hΓ hx)
  · exact mem_sep.mpr ⟨inj_mem_allShapes hc hx, resultIndex_inj constants levels env hc (FitsS.length_eq hx)⟩
  · exact branches_mem hc hctor hM hΓ hx hfs

/-- Reconstruct one recursive function from the container's branch graph.
Eta will recover the original source function, including at Prop. -/
noncomputable def decodeField (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (xs : List V) (j : Nat) (field : RecursiveField β) (g : V) : V :=
  Telescope.curry (shape.level.eval levels)
    (Telescope.interpret constants levels (Telescope.extend env xs) field.domains)
    (fun ys => app g (inj j (mkTower ys)))

noncomputable def decodeFields (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ctor : Constructor β) (xs : List V) (g : V) : List V :=
  ctor.recursive.zipIdx.map fun (field, j) => shape.decodeField constants levels env xs j field g

theorem getD_decodeFields (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ctor : Constructor β) (xs : List V) (g : V) {j : Nat} {field : RecursiveField β}
    (hf : ctor.recursive[j]? = some field) :
    (shape.decodeFields constants levels env ctor xs g).getD j empty =
      shape.decodeField constants levels env xs j field g := by
  simp only [decodeFields, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_zipIdx, hf, Option.map_some, Nat.zero_add, Option.getD_some]

theorem decodeField_mem {i j : Nat} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    {xs : List V} (hx : xs.length = ctor.fields.length) {g : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p))) :
    shape.decodeField constants levels env xs j field g ∈ˢ shape.recursiveSet constants levels env xs field := by
  apply Telescope.curry_mem
  intro ys hy
  have hp := app_mem_of_mem_piSet hg (inj_mem_positions hc hf hx hy)
  rwa [targetIndex_inj constants levels env hc hf hx (FitsS.length_eq hy)] at hp

theorem decodeFields_fit {i : Nat} (hc : shape.constructors[i]? = some ctor)
    {xs : List V} (hx : xs.length = ctor.fields.length) {g : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p))) :
    shape.RecursiveValuesFit constants levels env ctor xs (shape.decodeFields constants levels env ctor xs g) := by
  apply Telescope.fits_simple_map
  · simp only [decodeFields, List.length_map, List.length_zipIdx]
  · intro j field hf
    rw [getD_decodeFields _ _ _ _ _ _ _ hf]
    exact decodeField_mem hc hf hx hg

theorem applyN_decodeField {i j : Nat} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs ys : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hy : FitsS (Telescope.interpret constants levels (Telescope.extend env xs) field.domains) ys) {g : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p))) :
    Telescope.applyN (shape.decodeField constants levels env xs j field g) ys = app g (inj j (mkTower ys)) := by
  apply Telescope.applyN_curry _ hy
  · intro zs hz
    have hm := app_mem_of_mem_piSet hg (inj_mem_positions hc hf (FitsS.length_eq hx) hz)
    rwa [targetIndex_inj constants levels env hc hf (FitsS.length_eq hx) (FitsS.length_eq hz)] at hm
  · exact recursiveResult_zero h (h.2.2.2.2 field (List.mem_of_getElem? hf)) hM hΓ hx

theorem decodeField_branches {i j : Nat} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field)
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    shape.decodeField constants levels env xs j field (shape.branches constants levels env ctor i xs fs) =
      fs.getD j empty := by
  change Telescope.curry _ _ _ = _
  calc
    _ = Telescope.curry (shape.level.eval levels)
        (Telescope.interpret constants levels (Telescope.extend env xs) field.domains)
        (Telescope.applyN (fs.getD j empty)) := by
      apply Telescope.curry_congr
      exact fun ys hy => app_branches hc hf (FitsS.length_eq hx) hy
    _ = _ := Telescope.curry_applyN _ (hfs.get hf)
      (recursiveResult_zero h (h.2.2.2.2 field (List.mem_of_getElem? hf)) hM hΓ hx)

theorem decodeFields_branches {i : Nat} (hc : shape.constructors[i]? = some ctor)
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    shape.decodeFields constants levels env ctor xs (shape.branches constants levels env ctor i xs fs) = fs := by
  apply List.ext_getElem
  · simpa only [decodeFields, List.length_map, List.length_zipIdx] using (FitsS.length_eq hfs).symm
  · intro j hj hj'
    have hjc : j < ctor.recursive.length := by
      simpa only [decodeFields, List.length_map, List.length_zipIdx] using hj
    have hf := List.getElem?_eq_getElem (l := ctor.recursive) hjc
    have he := (getD_decodeFields shape constants levels env ctor xs _ hf).trans
      (decodeField_branches hc hf h hM hΓ hx hfs)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj', Option.getD_some] using he

theorem branches_decodeFields {i : Nat} (hc : shape.constructors[i]? = some ctor)
    (h : ConstructorEvidence.{u,v} entries shape ctor) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants levels env) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) {g : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p))) :
    shape.branches constants levels env ctor i xs (shape.decodeFields constants levels env ctor xs g) = g := by
  apply eq_of_mem_piSet_app_eq (branches_mem hc h hM hΓ hx (decodeFields_fit hc (FitsS.length_eq hx) hg)) hg
  intro p hp
  obtain ⟨j, field, ys, hf, hy, rfl⟩ := mem_positions hc (FitsS.length_eq hx) hp
  rw [app_branches hc hf (FitsS.length_eq hx) hy, getD_decodeFields _ _ _ _ _ _ _ hf]
  apply Telescope.applyN_curry _ hy
  · intro zs hz
    have hm := app_mem_of_mem_piSet hg (inj_mem_positions hc hf (FitsS.length_eq hx) hz)
    rwa [targetIndex_inj constants levels env hc hf (FitsS.length_eq hx) (FitsS.length_eq hz)] at hm
  · exact recursiveResult_zero h (h.2.2.2.2 field (List.mem_of_getElem? hf)) hM hΓ hx

end Ix.Kernel.Certified.Ordinary.Shape
