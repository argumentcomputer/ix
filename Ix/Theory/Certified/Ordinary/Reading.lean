/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Family

namespace Ix.Theory.Model

open SetTheory SetTheory.Tower

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

theorem Assignment.AgreesOn.telescope {entries : Environment β} {constants constants' : Assignment β V}
    (h : Assignment.AgreesOn entries constants constants') {domains : List (AExpr β)}
    (hrefs : ∀ A ∈ domains, A.ReferencesIn entries) (levels : List Nat) (env : Nat → V) :
    Telescope.interpret constants' levels env domains = Telescope.interpret constants levels env domains := by
  induction domains generalizing env with
  | nil => rfl
  | cons A rest ih =>
    simp only [Telescope.interpret, h.interp (hrefs A (List.mem_cons_self ..))]
    congr 1
    funext x
    exact ih (fun D hd => hrefs D (List.mem_cons_of_mem A hd)) _

end Ix.Theory.Model

namespace Ix.Theory.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

/-- Interface preserved while signatures are staged. The initial producer
installs the constructed family; subsequent fresh members preserve it. -/
structure FamilyReading (entries : Environment β) (shape : Shape β) (source : β)
    (constants reading : Assignment β V) : Prop where
  agrees : Assignment.AgreesOn entries constants reading
  family : ∀ levels, levels.length = shape.universes →
    reading (.member source 0) levels = shape.familyValue constants levels

theorem Shape.familyAssignment_reading [DecidableEq β] {entries : Environment β} {store : Store β}
    {source : β} {shape : Shape β} (h : CheckedShape.{u,v} entries store source shape)
    (constants : Assignment β V) :
    FamilyReading entries shape source constants (shape.familyAssignment constants source) :=
  ⟨Shape.familyAssignment_agrees h constants, fun _ _ => Assignment.insert_same ..⟩

namespace Shape

variable {entries : Environment β} {shape : Shape β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat}

theorem familyApp_interp (h : FamilyReading entries shape source constants reading)
    (hn : levels.length = shape.universes) {ps extra : List V} {indices : List (AExpr β)}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (his : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) shape.indices)
      (indices.map (interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra)))) :
    interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra)
      (shape.familyApp source extra.length indices) =
      app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps))
        (mkTower (indices.map (interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra)))) := by
  have hp : (parameterVars extra.length shape.parameters.length).map
      (interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra)) = ps := by
    rw [interp_parameterVars_skip, Telescope.skip_extend, ← FitsS.length_eq hps,
      interp_parameterVars_extend]
  rw [familyApp, AExpr.interp_appN]
  simp only [interp, eval_params hn, h.family levels hn, List.map_append, hp]
  exact familyValue_apply shape constants levels hps his

theorem recursiveType_interp {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} {field : RecursiveField β}
    (hc : ctor ∈ shape.constructors) (hf : field ∈ ctor.recursive) {ps xs previous : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs) :
    interp reading levels (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) previous)
      ((field.type shape source ctor.fields.length).liftN previous.length) =
      shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs field := by
  have hctor := h.constructors ctor hc
  have hfield := hctor.2.2.2.2 field hf
  have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
  rw [interp_liftN, Telescope.skip_extend, RecursiveField.type, AExpr.interp_forallN,
    hr.agrees.telescope (fun A ha => hfield.1 A (List.mem_append_left _ ha))]
  apply Telescope.piN_zero_agree (regime_zeroCondition shape.level levels)
  intro ys hys
  have he : field.indices.map (interp reading levels
        (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) ys)) =
      field.indices.map (interp constants levels
        (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) ys)) :=
    List.map_congr_left fun e he => hr.agrees.interp (hfield.1 e (List.mem_append_right _ he)) levels _
  have hit := recursiveTarget_fits hctor hfield hM hΓ hxs hys
  have hit' : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) shape.indices)
      (field.indices.map (interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) (xs ++ ys)))) := by
    simpa only [Telescope.extend_append, he] using hit
  have happ := familyApp_interp hr hn hps hit'
  simpa only [List.length_append, FitsS.length_eq hxs, FitsS.length_eq hys,
    Telescope.extend_append, he] using happ

theorem recursiveForall_interp {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {fields : List (RecursiveField β)} (hf : ∀ field ∈ fields, field ∈ ctor.recursive) {ps xs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (previous : List V) (B : AExpr β) :
    interp reading levels (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) previous)
      (.forallN (zeroCondition shape.level)
        (recursiveTypesFrom shape source ctor.fields.length fields previous.length) B) =
      Telescope.piN (shape.level.eval levels)
        (Telescope.simple (fields.map (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs)))
        (fun fs => interp reading levels
          (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) previous) fs) B) := by
  induction fields generalizing previous with
  | nil => rfl
  | cons field fields ih =>
    simp only [recursiveTypesFrom, List.zipIdx_cons, List.map_cons, AExpr.forallN, interp]
    rw [recursiveType_interp h hr hM hn hc (hf field (List.mem_cons_self ..)) hps hxs]
    apply piR_zero_agree (regime_zeroCondition shape.level levels)
    intro x _
    have htail := ih (fun f hm => hf f (List.mem_cons_of_mem field hm)) (previous ++ [x])
    simpa only [recursiveTypesFrom, List.length_append, List.length_singleton,
      Telescope.extend_append, Telescope.extend] using htail

theorem piN_recursiveTypes {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {fields : List (RecursiveField β)} (hf : ∀ field ∈ fields, field ∈ ctor.recursive) {ps xs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (previous : List V) (w : Nat) (R : List V → V) :
    Telescope.piN w (Telescope.interpret reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) previous)
      (recursiveTypesFrom shape source ctor.fields.length fields previous.length)) R =
      Telescope.piN w
        (Telescope.simple (fields.map (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs))) R := by
  induction fields generalizing previous R with
  | nil => rfl
  | cons field fields ih =>
    change piR w (interp reading levels _ ((field.type shape source ctor.fields.length).liftN previous.length)) _ =
      piR w (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs field) _
    rw [recursiveType_interp h hr hM hn hc (hf field (List.mem_cons_self ..)) hps hxs]
    congr 1
    funext f
    have ht := ih (fun f hf' => hf f (List.mem_cons_of_mem field hf')) (previous ++ [f]) (fun fs => R (f :: fs))
    have hlen : (previous ++ [f]).length = previous.length + 1 := by simp
    rw [hlen] at ht
    simpa only [recursiveTypesFrom, List.length_append, List.length_singleton,
      Telescope.extend_append, Telescope.extend] using ht

theorem curry_recursiveTypes {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {fields : List (RecursiveField β)} (hf : ∀ field ∈ fields, field ∈ ctor.recursive) {ps xs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (previous : List V) (w : Nat) (f : List V → V) :
    Telescope.curry w (Telescope.interpret reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) previous)
      (recursiveTypesFrom shape source ctor.fields.length fields previous.length)) f =
      Telescope.curry w
        (Telescope.simple (fields.map (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs))) f := by
  induction fields generalizing previous f with
  | nil => rfl
  | cons field fields ih =>
    change lamR w (interp reading levels _ ((field.type shape source ctor.fields.length).liftN previous.length)) _ =
      lamR w (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs field) _
    rw [recursiveType_interp h hr hM hn hc (hf field (List.mem_cons_self ..)) hps hxs]
    congr 1
    funext x
    have ht := ih (fun f hf' => hf f (List.mem_cons_of_mem field hf')) (previous ++ [x]) (fun xs => f (x :: xs))
    have hlen : (previous ++ [x]).length = previous.length + 1 := by simp
    rw [hlen] at ht
    simpa only [recursiveTypesFrom, List.length_append, List.length_singleton,
      Telescope.extend_append, Telescope.extend] using ht

theorem constructorResult_interp {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {ps xs fs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hlen : fs.length = ctor.recursive.length) :
    interp reading levels (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) fs)
      (shape.familyApp source (ctor.fields.length + ctor.recursive.length)
        (ctor.indices.map (AExpr.liftN ctor.recursive.length ·))) =
      app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps))
        (mkTower (ctor.indices.map (interp constants levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)))) := by
  have hctor := h.constructors ctor hc
  have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
  have he : (ctor.indices.map (AExpr.liftN ctor.recursive.length ·)).map
      (interp reading levels (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) fs)) =
      ctor.indices.map (interp constants levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp_def, interp_liftN, ← hlen, Telescope.skip_extend,
      hr.agrees.interp (hctor.1 e (List.mem_append_right _ he))]
  have hit := constructorResult_fits hctor hM hΓ hxs
  have hit' : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) shape.indices)
      ((ctor.indices.map (AExpr.liftN ctor.recursive.length ·)).map
        (interp reading levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) (xs ++ fs)))) := by
    simpa only [Telescope.extend_append, he] using hit
  have happ := familyApp_interp hr hn hps hit'
  simpa only [List.length_append, FitsS.length_eq hxs, hlen, Telescope.extend_append, he] using happ

noncomputable def constructorSet (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (ctor : Constructor β) : V :=
  Telescope.piN (shape.level.eval levels)
    (Telescope.interpret constants levels (fun _ => empty) shape.parameters) fun ps =>
      Telescope.piN (shape.level.eval levels)
        (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) fun xs =>
          Telescope.piN (shape.level.eval levels)
            (Telescope.simple (ctor.recursive.map (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs)))
            (fun _ => app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps))
              (mkTower (ctor.indices.map (interp constants levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)))))

theorem constructorType_interp {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors) :
    interp reading levels (fun _ => empty) (ctor.type shape source) = shape.constructorSet constants levels ctor := by
  have hctor := h.constructors ctor hc
  rw [Constructor.type, AExpr.interp_forallN,
    hr.agrees.telescope (fun A hA => h.references A (List.mem_append_left _ hA))]
  apply Telescope.piN_zero_agree (regime_zeroCondition shape.level levels)
  intro ps hps
  rw [AExpr.interp_forallN,
    hr.agrees.telescope (fun A hA => hctor.1 A (List.mem_append_left _ hA))]
  apply Telescope.piN_zero_agree (regime_zeroCondition shape.level levels)
  intro xs hxs
  rw [Constructor.recursiveTypes]
  have ht := recursiveForall_interp h hr hM hn hc (fun _ h => h) hps hxs []
    (shape.familyApp source (ctor.fields.length + ctor.recursive.length)
      (ctor.indices.map (AExpr.liftN ctor.recursive.length ·)))
  simp only [Telescope.extend, List.length_nil] at ht
  rw [ht]
  apply Telescope.piN_congr
  intro fs hfs
  exact constructorResult_interp h hr hM hn hc hps hxs (by simpa using FitsS.length_eq hfs)

noncomputable def constructorClosedValue (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (i : Nat) (ctor : Constructor β) : V :=
  Telescope.curry (shape.level.eval levels)
    (Telescope.interpret constants levels (fun _ => empty) shape.parameters) fun ps =>
      Telescope.curry (shape.level.eval levels)
        (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) fun xs =>
          Telescope.curry (shape.level.eval levels)
            (Telescope.simple (ctor.recursive.map (shape.recursiveSet constants levels (Telescope.extend (fun _ => empty) ps) xs)))
            (fun fs => shape.constructorValue constants levels (Telescope.extend (fun _ => empty) ps) ctor i xs fs)

theorem constructorClosedValue_mem {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) :
    shape.constructorClosedValue constants levels i ctor ∈ˢ shape.constructorSet constants levels ctor := by
  apply Telescope.curry_mem
  intro ps hps
  apply Telescope.curry_mem
  intro xs hxs
  apply Telescope.curry_mem
  intro fs hfs
  have hΓ := h.parameters.valid constants hM levels (Context.valid_nil constants levels (fun _ => empty)) hps
  exact constructorValue_mem h hM hΓ hc hxs hfs

theorem constructorClosedValue_mem_source {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) :
    shape.constructorClosedValue constants levels i ctor ∈ˢ interp reading levels (fun _ => empty) (ctor.type shape source) := by
  rw [constructorType_interp h hr hM hn (List.mem_of_getElem? hc)]
  exact constructorClosedValue_mem h hM hc

theorem constructorClosedValue_apply {store : Store β} (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants levels (Telescope.extend (fun _ => empty) ps) ctor xs fs) :
    Telescope.applyN (shape.constructorClosedValue constants levels i ctor) (ps ++ xs ++ fs) =
      shape.constructorValue constants levels (Telescope.extend (fun _ => empty) ps) ctor i xs fs := by
  have hresult (ps : List V) hps xs hxs fs hfs := constructorValue_mem h hM
    (h.parameters.valid constants hM levels (xs := ps) (Context.valid_nil constants levels (fun _ => empty)) hps)
    hc (xs := xs) hxs (fs := fs) hfs
  have hbound (ps : List V) hps xs hxs :
      app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps))
        (mkTower (ctor.indices.map (interp constants levels (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs))))
        ∈ˢ (univ (shape.level.eval levels) : V) :=
    (shape.container constants levels (Telescope.extend (fun _ => empty) ps)).carrier_fibre_mem _
      (constructorResult_mem (h.constructors ctor (List.mem_of_getElem? hc)) hM
        (h.parameters.valid constants hM levels (xs := ps) (Context.valid_nil constants levels (fun _ => empty)) hps) hxs)
  have hrec ps hps xs hxs := Telescope.curry_mem (w := shape.level.eval levels) _ (hresult ps hps xs hxs)
  have hfields ps hps := Telescope.curry_mem (w := shape.level.eval levels) _ (hrec ps hps)
  rw [constructorClosedValue, Telescope.applyN_append, Telescope.applyN_append,
    Telescope.applyN_curry _ hps hfields (fun hw ps hps => by
      rw [hw]
      apply Telescope.piN_zero_mem
      intro xs hxs
      apply Telescope.piN_zero_mem
      intro _ _
      simpa only [hw, univ_zero] using hbound ps hps xs hxs),
    Telescope.applyN_curry _ hxs (hrec ps hps) (fun hw xs hxs => by
      rw [hw]
      apply Telescope.piN_zero_mem
      intro _ _
      simpa only [hw, univ_zero] using hbound ps hps xs hxs)]
  exact Telescope.applyN_curry _ hfs (hresult ps hps xs hxs)
    (fun hw _ _ => by simpa only [hw, univ_zero] using hbound ps hps xs hxs)

end Shape
end Ix.Theory.Certified.Ordinary
