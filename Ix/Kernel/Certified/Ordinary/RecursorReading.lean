/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RecursorReading.lean
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

import Ix.Kernel.Certified.Ordinary.RecursorSyntax

namespace Ix.Kernel.Inductive.ElimMode

theorem sourceLevels_eval (mode : ElimMode) {levels : List Nat} {sourceUvars : Nat}
    (h : levels.length = mode.recUvars sourceUvars) :
    (mode.sourceLevels sourceUvars).map (VLevel.eval levels) = mode.sourceArgs levels := by
  apply List.ext_get (by simp [sourceLevels, sourceArgs_length mode h])
  intro i hi _
  have hi' : i < sourceUvars := by simpa [sourceLevels] using hi
  have bound : i + mode.offset < levels.length := by rw [h, recUvars]; omega
  simp [sourceLevels, VLevel.params', VLevel.eval, sourceArgs,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Nat.add_comm]

end Ix.Kernel.Inductive.ElimMode

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Inductive

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

structure ConstructorReading (entries : Environment β) (shape : Shape β) (source : β)
    (constants reading : Assignment β V) : Prop extends FamilyReading entries shape source constants reading where
  constructor : ∀ levels, levels.length = shape.universes → ∀ i ctor,
    shape.constructors[i]? = some ctor →
    reading (.ctor source 0 i) levels = shape.constructorClosedValue constants levels i ctor

namespace Shape

variable {entries : Environment β} {shape : Shape β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat} {mode : ElimMode}

theorem motiveType_interp (hr : FamilyReading entries shape source constants reading)
    (hn : levels.length = mode.recUvars shape.universes) {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hrefs : ∀ A ∈ shape.indices, A.ReferencesIn entries) :
    interp reading levels (Telescope.extend (fun _ => empty) ps) (shape.motiveType source mode) =
      shape.motiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) := by
  rw [motiveType, AExpr.interp_forallN, Telescope.piN_instL, mode.sourceLevels_eval hn,
    hr.agrees.telescope hrefs]
  apply Telescope.piN_congr
  intro is his
  have hvars := interp_parameterVars_extend reading (mode.sourceArgs levels)
    (Telescope.extend (fun _ => empty) ps) is
  rw [FitsS.length_eq his] at hvars
  have hit : FitsS (Telescope.interpret constants (mode.sourceArgs levels)
      (Telescope.extend (fun _ => empty) ps) shape.indices)
      ((parameterVars 0 shape.indices.length).map
        (interp reading (mode.sourceArgs levels)
          (Telescope.extend (Telescope.extend (fun _ => empty) ps) is))) := by
    simpa only [hvars] using his
  have happ := familyApp_interp hr (mode.sourceArgs_length hn) hps hit
  simp only [interp, regime_never, interp_instL, mode.sourceLevels_eval hn,
    FitsS.length_eq his, hvars] at happ ⊢
  rw [happ]

theorem minorFields_piN (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (m : V) (w : Nat) (R : List V → V) :
    Telescope.piN w (Telescope.interpret reading levels
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (shape.minorFields source mode ctor)) R =
      Telescope.piN w
        (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields)
        (fun xs => Telescope.piN w
          (Telescope.simple (ctor.recursive.map
            (shape.recursiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) xs)))
          (fun fs => R (xs ++ fs))) := by
  rw [minorFields, Telescope.piN_lift, Valuation.skip_succ_cons, Valuation.skip_zero,
    Telescope.piN_instL, mode.sourceLevels_eval hn, Telescope.piN_append,
    hr.agrees.telescope (fun A ha => (h.constructors ctor hc).1 A (List.mem_append_left _ ha))]
  apply Telescope.piN_congr
  intro xs hxs
  have ht := piN_recursiveTypes h hr hM (mode.sourceArgs_length hn) hc (fun _ h => h) hps hxs [] w
    (fun fs => R (xs ++ fs))
  simpa only [Constructor.recursiveTypes, List.length_nil, Telescope.extend] using ht

theorem ihType_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {j : Nat} {field : RecursiveField β} (hf : ctor.recursive[j]? = some field)
    {ps xs fs : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : fs.length = ctor.recursive.length) (m : V) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs)
      (shape.ihType mode ctor j field) =
      shape.ihSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m xs fs j field := by
  have hctor := h.constructors ctor hc
  have hfield := hctor.2.2.2.2 field (List.mem_of_getElem? hf)
  have hΓ := h.parameters.valid constants hM (mode.sourceArgs levels)
    (Context.valid_nil constants (mode.sourceArgs levels) (fun _ => empty)) hps
  have hxlen := FitsS.length_eq hxs
  have hskip : Valuation.skip 1 ctor.fields.length
      (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) =
      Telescope.extend (Telescope.extend (fun _ => empty) ps) xs := by
    simpa only [List.length_singleton, Telescope.extend, hxlen] using
      Telescope.skip_middle (Telescope.extend (fun _ => empty) ps) [m] xs
  rw [ihType, AExpr.interp_forallN, Telescope.piN_lift, ← hfs, Telescope.skip_extend,
    Telescope.piN_lift, hskip, Telescope.piN_instL, mode.sourceLevels_eval hn,
    hr.agrees.telescope (fun A ha => hfield.1 A (List.mem_append_left _ ha))]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro ys hys
  have hylen := FitsS.length_eq hys
  have hit := recursiveTarget_fits hctor hfield hM hΓ hxs hys
  have hidx : field.indices.map (fun e => interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend
        (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) ys)
      (((e.instL (mode.sourceLevels shape.universes)).liftN 1
        (ctor.fields.length + field.domains.length)).liftN ctor.recursive.length field.domains.length)) =
      field.indices.map (interp constants (mode.sourceArgs levels)
        (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) ys)) := by
    apply List.map_congr_left
    intro e he
    rw [interp_liftN, ← hfs, ← hylen, Telescope.skip_middle, interp_liftN]
    rw [show ctor.fields.length + ys.length = ys.length + ctor.fields.length by omega,
      Telescope.skip_extend_at, hskip, interp_instL, mode.sourceLevels_eval hn,
      hr.agrees.interp (hfield.1 e (List.mem_append_right _ he))]
  have hmvar : Telescope.extend (Telescope.extend (Telescope.extend
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) ys
      (ctor.fields.length + ctor.recursive.length + field.domains.length) = m := by
    rw [← hxlen, ← hfs, ← hylen]
    have ht := Telescope.extend_beyond (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (xs ++ fs ++ ys) 0
    simpa only [List.length_append, Nat.add_zero, Telescope.extend_append, Valuation.cons_zero] using ht
  have hfvar : Telescope.extend (Telescope.extend (Telescope.extend
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) ys
      (ctor.recursive.length - 1 - j + field.domains.length) = fs.getD j empty := by
    rw [← hfs, ← hylen, Nat.add_comm, Telescope.extend_beyond,
      Telescope.extend_getD _ _ j (by
        rw [hfs]
        exact (List.getElem?_eq_some_iff.mp hf).1)]
  have hvars := interp_parameterVars_extend reading levels
    (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) ys
  rw [hylen] at hvars
  simp only [hfs, AExpr.interp_appN, interp, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, Telescope.applyN_append, Telescope.applyN, hmvar, hfvar, hvars, hidx]
  rw [motive, projList_mkTower _ _ (FitsS.length_eq hit)]

theorem ihTypes_piN (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {ps xs fs : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : fs.length = ctor.recursive.length) (m : V) (w : Nat) (R : List V → V) :
    Telescope.piN w (Telescope.interpret reading levels
      (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs)
      (shape.ihTypesSyntax mode ctor)) R =
      Telescope.piN w (Telescope.simple (shape.ihTypes constants (mode.sourceArgs levels)
        (Telescope.extend (fun _ => empty) ps) (mode.motiveLevel.eval levels) m ctor xs fs)) R := by
  have ht := Telescope.piN_independent reading levels
    (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs)
    (ctor.recursive.zipIdx.map fun (field, j) => shape.ihType mode ctor j field) [] w R
  simp only [List.length_nil, Telescope.extend] at ht
  rw [ihTypesSyntax, ht]
  have he : ((ctor.recursive.zipIdx.map fun (field, j) => shape.ihType mode ctor j field).map
      (interp reading levels (Telescope.extend
        (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs))) =
      shape.ihTypes constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m ctor xs fs := by
    apply List.ext_getElem?
    intro j
    simp only [ihTypes, List.getElem?_map, List.getElem?_zipIdx]
    cases hf : ctor.recursive[j]? with
    | none => rfl
    | some field =>
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (ihType_interp h hr hM hn hc hf hps hxs hfs m)
  rw [he]

theorem constructorVars_interp (hr : ConstructorReading entries shape source constants reading)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) (ps extra fields tail : List V)
    (hps : ps.length = shape.parameters.length) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra) fields) tail)
      (.appN (.const (.ctor source 0 i) (mode.sourceLevels shape.universes))
        (parameterVars (extra.length + fields.length + tail.length) shape.parameters.length ++
          parameterVars tail.length fields.length)) =
      Telescope.applyN (shape.constructorClosedValue constants (mode.sourceArgs levels) i ctor) (ps ++ fields) := by
  have hp := interp_parameterVars_middle reading levels (fun _ => empty) ps (extra ++ fields ++ tail)
  simp only [List.length_append, hps, Telescope.extend_append] at hp
  have hf := interp_parameterVars_middle reading levels
    (Telescope.extend (Telescope.extend (fun _ => empty) ps) extra) fields tail
  simp only [AExpr.interp_appN, interp, mode.sourceLevels_eval hn,
    hr.constructor _ (mode.sourceArgs_length hn) i ctor hc, List.map_append, hp, hf]

theorem minorResult_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs hs : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor xs fs)
    (hhs : hs.length = ctor.recursive.length) (m : V) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend
        (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) hs)
      (shape.minorResult source mode i ctor) =
      shape.motive m
        (mkTower (ctor.indices.map (interp constants (mode.sourceArgs levels)
          (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs))))
        (shape.constructorValue constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor i xs fs) := by
  have hxlen := FitsS.length_eq hxs
  have hflen : fs.length = ctor.recursive.length := by simpa using FitsS.length_eq hfs
  have hctor := h.constructors ctor (List.mem_of_getElem? hc)
  have hΓ := h.parameters.valid constants hM (mode.sourceArgs levels)
    (Context.valid_nil constants (mode.sourceArgs levels) (fun _ => empty)) hps
  have hit := constructorResult_fits hctor hM hΓ hxs
  have hcv := constructorVars_interp hr hn hc ps [m] (xs ++ fs) hs (FitsS.length_eq hps)
  rw [← List.append_assoc, constructorClosedValue_apply h hM hc hps hxs hfs] at hcv
  simp only [List.length_singleton, List.length_append, hxlen, hflen, hhs,
    Telescope.extend_append, Telescope.extend, Nat.add_assoc] at hcv
  have hidx : ctor.indices.map (fun e => interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend
        (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) hs)
      (((e.instL (mode.sourceLevels shape.universes)).liftN 1 ctor.fields.length).liftN
        (ctor.recursive.length + ctor.recursive.length))) =
      ctor.indices.map (interp constants (mode.sourceArgs levels)
        (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)) := by
    apply List.map_congr_left
    intro e he
    rw [interp_liftN, show ctor.recursive.length + ctor.recursive.length = (fs ++ hs).length by simp [hflen, hhs],
      ← Telescope.extend_append, Telescope.skip_extend, interp_liftN, ← hxlen]
    have ht := Telescope.skip_middle (Telescope.extend (fun _ => empty) ps) [m] xs
    simp only [List.length_singleton, Telescope.extend] at ht
    rw [ht, interp_instL, mode.sourceLevels_eval hn,
      hr.agrees.interp (hctor.1 e (List.mem_append_right _ he))]
  have hmvar : Telescope.extend (Telescope.extend (Telescope.extend
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) xs) fs) hs
      (ctor.fields.length + ctor.recursive.length + ctor.recursive.length) = m := by
    have ht := Telescope.extend_beyond (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (xs ++ fs ++ hs) 0
    simpa only [List.length_append, Nat.add_zero, Telescope.extend_append, Valuation.cons_zero,
      hxlen, hflen, hhs] using ht
  simp only [Nat.add_assoc] at hmvar
  rw [minorResult, AExpr.interp_appN]
  simp only [interp, hmvar, List.map_append, List.map_map, Function.comp_def, hidx,
    List.map_cons, List.map_nil, Telescope.applyN_append, Telescope.applyN, Nat.add_assoc, hcv]
  rw [motive, projList_mkTower _ _ (FitsS.length_eq hit)]

theorem minorType_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (m : V) :
    interp reading levels (Valuation.cons m (Telescope.extend (fun _ => empty) ps))
      (shape.minorType source mode i ctor) =
      shape.minorSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m i ctor := by
  rw [minorType, AExpr.interp_forallN, minorFields_piN h hr.toFamilyReading hM hn
    (List.mem_of_getElem? hc) hps]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro xs hxs
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro fs hfs
  have hflen : fs.length = ctor.recursive.length := by simpa using FitsS.length_eq hfs
  rw [Telescope.extend_append, AExpr.interp_forallN,
    ihTypes_piN h hr.toFamilyReading hM hn (List.mem_of_getElem? hc) hps hxs hflen]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro hs hhs
  exact minorResult_interp h hr hM hn hc hps hxs hfs
    (by simpa only [ihTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hhs) m

theorem minorTypes_piN (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (m : V) (w : Nat) (R : List V → V) :
    Telescope.piN w (Telescope.interpret reading levels
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (shape.minorTypesSyntax source mode)) R =
      Telescope.piN w (Telescope.simple (shape.minorTypes constants (mode.sourceArgs levels)
        (Telescope.extend (fun _ => empty) ps) (mode.motiveLevel.eval levels) m)) R := by
  have ht := Telescope.piN_independent reading levels
    (Valuation.cons m (Telescope.extend (fun _ => empty) ps))
    (shape.constructors.zipIdx.map fun (ctor, i) => shape.minorType source mode i ctor) [] w R
  simp only [List.length_nil, Telescope.extend] at ht
  rw [minorTypesSyntax, ht]
  have he : ((shape.constructors.zipIdx.map fun (ctor, i) => shape.minorType source mode i ctor).map
      (interp reading levels (Valuation.cons m (Telescope.extend (fun _ => empty) ps)))) =
      shape.minorTypes constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m := by
    apply List.ext_getElem?
    intro i
    simp only [minorTypes, List.getElem?_map, List.getElem?_zipIdx]
    cases hc : shape.constructors[i]? with
    | none => rfl
    | some ctor =>
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (minorType_interp h hr hM hn hc hps m)
  rw [he]

theorem minorTypes_curry (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (m : V) (w : Nat) (f : List V → V) :
    Telescope.curry w (Telescope.interpret reading levels
      (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (shape.minorTypesSyntax source mode)) f =
      Telescope.curry w (Telescope.simple (shape.minorTypes constants (mode.sourceArgs levels)
        (Telescope.extend (fun _ => empty) ps) (mode.motiveLevel.eval levels) m)) f := by
  have ht := Telescope.curry_independent reading levels
    (Valuation.cons m (Telescope.extend (fun _ => empty) ps))
    (shape.constructors.zipIdx.map fun (ctor, i) => shape.minorType source mode i ctor) [] w f
  simp only [List.length_nil, Telescope.extend] at ht
  rw [minorTypesSyntax, ht]
  have he : ((shape.constructors.zipIdx.map fun (ctor, i) => shape.minorType source mode i ctor).map
      (interp reading levels (Valuation.cons m (Telescope.extend (fun _ => empty) ps)))) =
      shape.minorTypes constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m := by
    apply List.ext_getElem?
    intro i
    simp only [minorTypes, List.getElem?_map, List.getElem?_zipIdx]
    cases hc : shape.constructors[i]? with
    | none => rfl
    | some ctor =>
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (minorType_interp h hr hM hn hc hps m)
  rw [he]

theorem recursorTail_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading)
    (hn : levels.length = mode.recUvars shape.universes) {ps minors : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hlen : minors.length = shape.constructors.length) (m : V) :
    interp reading levels (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors)
      (shape.recursorTail source mode) =
      shape.recursorSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
        (mode.motiveLevel.eval levels) m := by
  have hcommon : 1 + shape.constructors.length = (m :: minors).length := by simp [hlen, Nat.add_comm]
  have hskip : Valuation.skip (1 + shape.constructors.length) 0
      (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors) =
      Telescope.extend (fun _ => empty) ps := by
    simpa only [← hcommon, Telescope.extend] using
      Telescope.skip_extend (Telescope.extend (fun _ => empty) ps) (m :: minors)
  rw [recursorTail, AExpr.interp_forallN, Telescope.piN_lift, hskip,
    Telescope.piN_instL, mode.sourceLevels_eval hn,
    hr.agrees.telescope (fun A ha => h.references A (List.mem_append_right _ ha))]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro is his
  have hil := FitsS.length_eq his
  have hvars := interp_parameterVars_extend reading (mode.sourceArgs levels)
    (Telescope.extend (fun _ => empty) ps) is
  rw [hil] at hvars
  have hit : FitsS (Telescope.interpret constants (mode.sourceArgs levels)
      (Telescope.extend (fun _ => empty) ps) shape.indices)
      ((parameterVars 0 shape.indices.length).map
        (interp reading (mode.sourceArgs levels)
          (Telescope.extend (Telescope.extend (fun _ => empty) ps) is))) := by
    simpa only [hvars] using his
  have happ := familyApp_interp hr (mode.sourceArgs_length hn) hps hit
  simp only [hil, hvars] at happ
  have hskip' : Valuation.skip (1 + shape.constructors.length) shape.indices.length
      (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors) is) =
      Telescope.extend (Telescope.extend (fun _ => empty) ps) is := by
    simpa only [← hcommon, Telescope.extend, hil] using
      Telescope.skip_middle (Telescope.extend (fun _ => empty) ps) (m :: minors) is
  rw [interp, interp_liftN, hskip', interp_instL, mode.sourceLevels_eval hn, happ]
  apply piR_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro x _
  have hmvar : Valuation.cons x
      (Telescope.extend (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors) is)
      (shape.constructors.length + shape.indices.length + 1) = m := by
    rw [Valuation.cons_succ]
    have ht := Telescope.extend_beyond (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) (minors ++ is) 0
    simpa only [List.length_append, Nat.add_zero, hlen, hil, Telescope.extend_append, Valuation.cons_zero] using ht
  have hisvars := interp_parameterVars_middle reading levels
    (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors) is [x]
  simp only [List.length_singleton, hil, Telescope.extend] at hisvars
  simp only [AExpr.interp_appN, interp, hmvar, List.map_append, hisvars, List.map_cons,
    List.map_nil, Valuation.cons_zero, Telescope.applyN_append, Telescope.applyN]
  rw [motive, projList_mkTower _ _ hil]

noncomputable def closedRecursorSet (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (mode : ElimMode) : V :=
  let ls := mode.sourceArgs levels
  let v := mode.motiveLevel.eval levels
  Telescope.piN v (Telescope.interpret constants ls (fun _ => empty) shape.parameters) fun ps =>
    piR v (shape.motiveSet constants ls (Telescope.extend (fun _ => empty) ps) v) fun m =>
      Telescope.piN v (Telescope.simple (shape.minorTypes constants ls (Telescope.extend (fun _ => empty) ps) v m))
        (fun _ => shape.recursorSet constants ls (Telescope.extend (fun _ => empty) ps) v m)

theorem recursorType_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) :
    interp reading levels (fun _ => empty) (shape.recursorType source mode) =
      shape.closedRecursorSet constants levels mode := by
  rw [recursorType, AExpr.interp_forallN, Telescope.piN_instL, mode.sourceLevels_eval hn,
    hr.agrees.telescope (fun A ha => h.references A (List.mem_append_left _ ha))]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro ps hps
  rw [interp, motiveType_interp hr.toFamilyReading hn hps
    (fun A ha => h.references A (List.mem_append_right _ ha))]
  apply piR_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro m _
  rw [AExpr.interp_forallN, minorTypes_piN h hr hM hn hps]
  apply Telescope.piN_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro minors hminors
  exact recursorTail_interp h hr.toFamilyReading hn hps
    (by simpa only [minorTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hminors) m

end Shape
end Ix.Kernel.Certified.Ordinary
