/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.LargeElim

namespace Ix.Theory.Certified.Ordinary.Shape

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Model.InductiveCodes

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def motiveSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (motiveLevel : Nat) : V :=
  Telescope.piN 1 (Telescope.interpret constants levels env shape.indices)
    (fun is => piR 1 (app (shape.carrier constants levels env) (mkTower is))
      (fun _ => univ motiveLevel))

noncomputable def motive (shape : Shape β) (m : V) (i x : V) : V :=
  app (Telescope.applyN m (projList shape.indices.length i)) x

theorem motive_mem {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {v : Nat} {m i x : V}
    (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hi : i ∈ˢ shape.indexSet constants levels env)
    (hx : x ∈ˢ app (shape.carrier constants levels env) i) :
    shape.motive m i x ∈ˢ (univ v : V) := by
  obtain ⟨hfit, he⟩ := towerSet_elim (by decide : 1 ≠ 0) _ hi
  have ht := Telescope.applyN_mem _ hm hfit (fun h => (by omega : False).elim)
  rw [← he] at ht
  exact app_mem_piR_pos (by decide : 1 ≠ 0) ht hx

noncomputable def ihSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (xs fs : List V) (j : Nat) (field : RecursiveField β) : V :=
  Telescope.piN v (Telescope.interpret constants levels (Telescope.extend env xs) field.domains)
    (fun ys => shape.motive m
      (mkTower (field.indices.map (interp constants levels (Telescope.extend (Telescope.extend env xs) ys))))
      (Telescope.applyN (fs.getD j empty) ys))

noncomputable def ihTypes (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (ctor : Constructor β) (xs fs : List V) : List V :=
  ctor.recursive.zipIdx.map fun (field, j) => shape.ihSet constants levels env v m xs fs j field

def IHValuesFit (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (ctor : Constructor β) (xs fs hs : List V) : Prop :=
  FitsS (Telescope.simple (shape.ihTypes constants levels env v m ctor xs fs)) hs

noncomputable def minorSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (i : Nat) (ctor : Constructor β) : V :=
  Telescope.piN v (Telescope.interpret constants levels env ctor.fields) fun xs =>
    Telescope.piN v (Telescope.simple (ctor.recursive.map (shape.recursiveSet constants levels env xs))) fun fs =>
      Telescope.piN v (Telescope.simple (shape.ihTypes constants levels env v m ctor xs fs)) fun _ =>
        shape.motive m (mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs))))
          (shape.constructorValue constants levels env ctor i xs fs)

noncomputable def minorTypes (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) : List V :=
  shape.constructors.zipIdx.map fun (ctor, i) => shape.minorSet constants levels env v m i ctor

def MinorValuesFit (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (minors : List V) : Prop :=
  FitsS (Telescope.simple (shape.minorTypes constants levels env v m)) minors

theorem MinorValuesFit.get {shape : Shape β} {constants : Assignment β V} {levels : List Nat}
    {env : Nat → V} {v : Nat} {m : V} {minors : List V}
    (h : shape.MinorValuesFit constants levels env v m minors)
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) :
    minors.getD i empty ∈ˢ shape.minorSet constants levels env v m i ctor := by
  apply Telescope.fits_simple_getD h
  simp only [minorTypes, List.getElem?_map, List.getElem?_zipIdx, hc, Option.map_some, Nat.zero_add]

variable {entries : Environment β} {store : Store β} {source : β} {shape : Shape β}
  {constants : Assignment β V} {levels : List Nat} {env : Nat → V}

theorem minorResult_mem_univ (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) {xs fs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs) :
    shape.motive m (mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs))))
      (shape.constructorValue constants levels env ctor i xs fs) ∈ˢ (univ v : V) :=
  motive_mem hm (constructorResult_mem (h.constructors ctor (List.mem_of_getElem? hc)) hM hΓ hx)
    (constructorValue_mem h hM hΓ hc hx hfs)

theorem minor_apply_mem (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m minor : V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor)
    (hminor : minor ∈ˢ shape.minorSet constants levels env v m i ctor) {xs fs hs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels env ctor xs fs)
    (hhs : shape.IHValuesFit constants levels env v m ctor xs fs hs) :
    Telescope.applyN minor (xs ++ fs ++ hs) ∈ˢ
      shape.motive m (mkTower (ctor.indices.map (interp constants levels (Telescope.extend env xs))))
        (shape.constructorValue constants levels env ctor i xs fs) := by
  simp only [Telescope.applyN_append]
  have hxstep := Telescope.applyN_mem _ hminor hx (fun hv ys hy => by
    subst v
    apply Telescope.piN_zero_mem
    intro gs hgs
    apply Telescope.piN_zero_mem
    intro _ _
    simpa only [univ_zero] using minorResult_mem_univ h hM hΓ hm hc hy hgs)
  have hfsstep := Telescope.applyN_mem _ hxstep hfs (fun hv gs hgs => by
    subst v
    apply Telescope.piN_zero_mem
    intro _ _
    simpa only [univ_zero] using minorResult_mem_univ h hM hΓ hm hc hx hgs)
  exact Telescope.applyN_mem _ hfsstep hhs (fun hv _ _ => by
    simpa only [hv, univ_zero] using minorResult_mem_univ h hM hΓ hm hc hx hfs)

noncomputable def ihValue (_shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (xs : List V) (j : Nat) (field : RecursiveField β) (ih : V) : V :=
  Telescope.curry v (Telescope.interpret constants levels (Telescope.extend env xs) field.domains)
    (fun ys => app ih (inj j (mkTower ys)))

noncomputable def ihValues (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (ctor : Constructor β) (xs : List V) (ih : V) : List V :=
  ctor.recursive.zipIdx.map fun (field, j) => shape.ihValue constants levels env v xs j field ih

theorem ihValue_mem (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {i j : Nat} {ctor : Constructor β} {field : RecursiveField β}
    (hc : shape.constructors[i]? = some ctor) (hf : ctor.recursive[j]? = some field) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) {g ih : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p)))
    (hih : ih ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => shape.motive m (shape.targetIndex constants levels env (inj i (mkTower xs)) p) (app g p))) :
    shape.ihValue constants levels env v xs j field ih ∈ˢ
      shape.ihSet constants levels env v m xs (shape.decodeFields constants levels env ctor xs g) j field := by
  apply Telescope.curry_mem
  intro ys hy
  have hm := app_mem_of_mem_piSet hih (inj_mem_positions hc hf (FitsS.length_eq hx) hy)
  rw [targetIndex_inj constants levels env hc hf (FitsS.length_eq hx) (FitsS.length_eq hy)] at hm
  rw [getD_decodeFields _ _ _ _ _ _ _ hf,
    applyN_decodeField hc hf (h.constructors ctor (List.mem_of_getElem? hc)) hM hΓ hx hy hg]
  exact hm

theorem ihValues_fit (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {xs : List V}
    (hx : FitsS (Telescope.interpret constants levels env ctor.fields) xs) {g ih : V}
    (hg : g ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => app (shape.carrier constants levels env)
        (shape.targetIndex constants levels env (inj i (mkTower xs)) p)))
    (hih : ih ∈ˢ piSet (shape.positions constants levels env (inj i (mkTower xs)))
      (fun p => shape.motive m (shape.targetIndex constants levels env (inj i (mkTower xs)) p) (app g p))) :
    shape.IHValuesFit constants levels env v m ctor xs (shape.decodeFields constants levels env ctor xs g)
      (shape.ihValues constants levels env v ctor xs ih) := by
  apply Telescope.fits_simple_of_getD
  · simp only [ihValues, ihTypes, List.length_map, List.length_zipIdx]
  · intro j A hA
    simp only [ihTypes, List.getElem?_map, List.getElem?_zipIdx] at hA
    cases hf : ctor.recursive[j]? with
    | none => simp [hf] at hA
    | some field =>
      simp only [hf, Option.map_some, Nat.zero_add, Option.some.injEq] at hA
      subst A
      simp only [ihValues, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_zipIdx, hf, Option.map_some, Nat.zero_add, Option.getD_some]
      exact ihValue_mem h hM hΓ hc hf hx hg hih

noncomputable def algebra (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (_m : V) (minors : List V) (_i a g ih : V) : V :=
  match shape.constructors[tag a]? with
  | none => empty
  | some ctor =>
    let xs := ordinaryValues ctor a
    let fs := shape.decodeFields constants levels env ctor xs g
    let hs := shape.ihValues constants levels env v ctor xs ih
    Telescope.applyN (minors.getD (tag a) empty) (xs ++ fs ++ hs)

theorem algebra_typing (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors) :
    (shape.container constants levels env).AlgebraTyping (shape.level.eval levels)
      (shape.motive m) (shape.algebra constants levels env v m minors) := by
  intro i hi a ha g hg ih hih
  obtain ⟨has, hresult⟩ := mem_sep.mp ha
  obtain ⟨j, ctor, xs, hc, hx, rfl⟩ := mem_allShapes has
  rw [resultIndex_inj constants levels env hc (FitsS.length_eq hx)] at hresult
  have hctor := h.constructors ctor (List.mem_of_getElem? hc)
  have hfs := decodeFields_fit hc (FitsS.length_eq hx) hg
  have hhs := ihValues_fit (v := v) h hM hΓ hc hx hg hih
  have hstep := minor_apply_mem h hM hΓ hm hc (hminors.get hc) hx hfs hhs
  rw [constructorValue, branches_decodeFields hc hctor hM hΓ hx hg, hresult] at hstep
  simpa only [algebra, tag_inj, hc, ordinaryValues_inj _ (FitsS.length_eq hx)] using hstep

noncomputable def recursorSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) : V :=
  Telescope.piN v (Telescope.interpret constants levels env shape.indices) fun is =>
    piR v (app (shape.carrier constants levels env) (mkTower is)) (shape.motive m (mkTower is))

noncomputable def largeValue (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (v : Nat) (m : V) (minors : List V)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels)) : V :=
  Telescope.curry v (Telescope.interpret constants levels env shape.indices) fun is =>
    lamR v (app (shape.carrier constants levels env) (mkTower is)) fun x =>
      IndexedContainer.foldAt hD hlarge (shape.algebra constants levels env v m minors) (mkTower is) x

theorem largeValue_mem (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels)) :
    shape.largeValue constants levels env v m minors hD hlarge ∈ˢ shape.recursorSet constants levels env v m := by
  apply Telescope.curry_mem
  intro is his
  apply lamR_mem
  intro x hx
  exact IndexedContainer.foldAt_mem hD hlarge (algebra_typing h hM hΓ hm hminors)
    (mkTower_mem (by decide : 1 ≠ 0) his) hx

theorem largeValue_apply (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {v : Nat} {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env v)
    (hminors : shape.MinorValuesFit constants levels env v m minors)
    (hD : (shape.container constants levels env).WF (shape.level.eval levels))
    (hlarge : (shape.container constants levels env).LargeElim (shape.level.eval levels))
    {is : List V} (his : FitsS (Telescope.interpret constants levels env shape.indices) is)
    {x : V} (hx : x ∈ˢ app (shape.carrier constants levels env) (mkTower is)) :
    Telescope.applyN (shape.largeValue constants levels env v m minors hD hlarge) (is ++ [x]) =
      IndexedContainer.foldAt hD hlarge (shape.algebra constants levels env v m minors) (mkTower is) x := by
  have hi := mkTower_mem (by decide : 1 ≠ 0) his
  have hleaf ys hys y hy := IndexedContainer.foldAt_mem hD hlarge (algebra_typing h hM hΓ hm hminors)
    (mkTower_mem (by decide : 1 ≠ 0) hys) (i := mkTower ys) (x := y) hy
  have hlam ys hys := lamR_mem (v := v) (hleaf ys hys)
  rw [Telescope.applyN_append]
  change app (Telescope.applyN (Telescope.curry v _ _) is) x = _
  simp only [carrier]
  rw [Telescope.applyN_curry (w := v) _ his hlam (fun hv ys hys => by
    subst v
    exact piR_zero_mem_univZero)]
  exact app_lamR hx (hleaf is his) (fun hv y hy => by
    simpa only [hv, univ_zero] using motive_mem hm hi hy)

/-- Small elimination constructs the proof point by structural induction.
It applies equally to empty, singleton, and many-constructor Prop families. -/
theorem pt_mem_smallRecursorSet (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (hΓ : shape.parameterContext.Valid constants levels env)
    {m : V} {minors : List V} (hm : m ∈ˢ shape.motiveSet constants levels env 0)
    (hminors : shape.MinorValuesFit constants levels env 0 m minors) :
    (pt : V) ∈ˢ shape.recursorSet constants levels env 0 m := by
  have helim := IndexedContainer.small_elim (container_wf h hM hΓ)
    (fun i hi x hx => by simpa only [univ_zero] using motive_mem hm hi hx)
    (algebra_typing h hM hΓ hm hminors)
  have hvalue := Telescope.curry_mem (w := 0)
    (Telescope.interpret constants levels env shape.indices)
    (R := fun is => piR 0 (app (shape.carrier constants levels env) (mkTower is))
      (shape.motive m (mkTower is)))
    (f := fun _ => (pt : V)) (fun is his =>
      pt_mem_piR_zero_of (fun x hx => helim (mkTower is) (mkTower_mem (by decide : 1 ≠ 0) his) x hx))
  rwa [Telescope.curry_point] at hvalue

end Ix.Theory.Certified.Ordinary.Shape
