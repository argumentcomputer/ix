/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RuleReading.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block, so the bare `recursor` address parameter is
the family's `source`.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RuleChecks

namespace Ix.Kernel.Model

open SetTheory

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

theorem Assignment.AgreesOn.interp_inserted {entries : Environment β}
    {constants reading : Assignment β V} (h : Assignment.AgreesOn entries constants reading)
    (levels : List Nat) (sourceLevels : List VLevel) (env : Nat → V)
    (shared xs fs ys : List V) {e : AExpr β} (hrefs : e.ReferencesIn entries) :
    Model.interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend env shared) xs) fs) ys)
      (((e.instL sourceLevels).liftN shared.length (xs.length + ys.length)).liftN fs.length ys.length) =
      Model.interp constants (sourceLevels.map (VLevel.eval levels)) (Telescope.extend (Telescope.extend env xs) ys) e := by
  rw [interp_liftN, Telescope.skip_middle, interp_liftN,
    show xs.length + ys.length = ys.length + xs.length by omega,
    Telescope.skip_extend_at, Telescope.skip_middle, interp_instL, h.interp hrefs]

end Ix.Kernel.Model

namespace Ix.Kernel.Certified.Ordinary.Shape

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Inductive

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def recursorCall (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (mode : ElimMode) (m : V) (minors xs fs : List V) (j : Nat) (field : RecursiveField β) : V :=
  Telescope.curry (mode.motiveLevel.eval levels)
    (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend env xs) field.domains) fun ys =>
      Telescope.applyN (shape.recursorAt constants levels env mode m minors)
        (field.indices.map (interp constants (mode.sourceArgs levels) (Telescope.extend (Telescope.extend env xs) ys)) ++
          [Telescope.applyN (fs.getD j empty) ys])

noncomputable def recursorCalls (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (mode : ElimMode) (m : V) (minors : List V) (ctor : Constructor β) (xs fs : List V) : List V :=
  ctor.recursive.zipIdx.map fun (field, j) => shape.recursorCall constants levels env mode m minors xs fs j field

theorem recursorCall_large (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (m : V) (minors xs fs : List V) (j : Nat) (field : RecursiveField β)
    (hD : (shape.container constants (ElimMode.large.sourceArgs levels) env).WF
      (shape.level.eval (ElimMode.large.sourceArgs levels)))
    (hlarge : (shape.container constants (ElimMode.large.sourceArgs levels) env).LargeElim
      (shape.level.eval (ElimMode.large.sourceArgs levels))) :
    shape.recursorCall constants levels env .large m minors xs fs j field =
      shape.recursiveCall constants (ElimMode.large.sourceArgs levels) env
        (ElimMode.large.motiveLevel.eval levels) m minors hD hlarge xs fs j field := by
  simp only [recursorCall, recursiveCall, recursorAt_large _ _ _ _ _ _ hD hlarge]

variable {entries : Environment β} {shape : Shape β} {source : β}
  {constants reading : Assignment β V} {levels : List Nat} {mode : ElimMode}

theorem ruleCall_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source mode constants reading)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    {j : Nat} {field : RecursiveField β} (hf : ctor.recursive[j]? = some field)
    {ps xs fs minors : List V} {m : V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : fs.length = ctor.recursive.length)
    (hm : m ∈ˢ shape.motiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels) m minors) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleCall source mode ctor j field) =
      shape.recursorCall constants levels (Telescope.extend (fun _ => empty) ps) mode m minors xs fs j field := by
  have hctor := h.constructors ctor hc
  have hfield := hctor.2.2.2.2 field (List.mem_of_getElem? hf)
  have hplen := FitsS.length_eq hps
  have hxlen := FitsS.length_eq hxs
  have hmlen : minors.length = shape.constructors.length := by
    simpa only [minorTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hminors
  have hcommon : 1 + shape.constructors.length = (m :: minors).length := by simp [hmlen, Nat.add_comm]
  have hskip : Valuation.skip (1 + shape.constructors.length) ctor.fields.length
      (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) =
      Telescope.extend (Telescope.extend (fun _ => empty) ps) xs := by
    simpa only [← hcommon, hxlen] using Telescope.skip_middle (Telescope.extend (fun _ => empty) ps) (m :: minors) xs
  rw [ruleCall, AExpr.interp_lamN, Telescope.curry_lift, ← hfs, Telescope.skip_extend,
    Telescope.curry_lift, hskip, Telescope.curry_instL, mode.sourceLevels_eval hn,
    hr.agrees.telescope (fun A ha => hfield.1 A (List.mem_append_left _ ha))]
  apply Telescope.curry_zero_agree (regime_zeroCondition mode.motiveLevel levels)
  intro ys hys
  have hylen := FitsS.length_eq hys
  have hprefix := interp_parameterVars_middle reading levels (fun _ => empty) (ps ++ [m] ++ minors) (xs ++ fs ++ ys)
  simp only [List.length_append, List.length_singleton, Telescope.extend_append, Telescope.extend,
    hplen, hxlen, hfs, hmlen, hylen, Nat.add_assoc] at hprefix
  have hidx : field.indices.map (fun e => interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps)
        (m :: minors)) xs) fs) ys)
      (((e.instL (mode.sourceLevels shape.universes)).liftN (1 + shape.constructors.length)
        (ctor.fields.length + field.domains.length)).liftN ctor.recursive.length field.domains.length)) =
      field.indices.map (interp constants (mode.sourceArgs levels)
        (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs) ys)) := by
    apply List.map_congr_left
    intro e he
    have ht := hr.agrees.interp_inserted levels (mode.sourceLevels shape.universes)
      (Telescope.extend (fun _ => empty) ps) (m :: minors) xs fs ys (hfield.1 e (List.mem_append_right _ he))
    simpa only [mode.sourceLevels_eval hn, ← hcommon, hxlen, hfs, hylen] using ht
  have hfvar : Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps)
      (m :: minors)) xs) fs) ys (ctor.recursive.length - 1 - j + field.domains.length) = fs.getD j empty := by
    rw [← hfs, ← hylen, Nat.add_comm, Telescope.extend_beyond,
      Telescope.extend_getD _ _ j (by rw [hfs]; exact (List.getElem?_eq_some_iff.mp hf).1)]
  have hvars := interp_parameterVars_extend reading levels
    (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs) ys
  rw [hylen] at hvars
  simp only [Telescope.extend] at hidx hfvar hvars
  simp only [hfs, AExpr.interp_appN, interp, ElimMode.recLevels, eval_params hn,
    hr.recursor _ hn, List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, hidx, hfvar, hvars, Nat.add_assoc, Telescope.extend, hprefix]
  rw [Telescope.applyN_append, Telescope.applyN_append, closedRecursorValue_apply h hmode hM hps hm hminors,
    Telescope.applyN_append]

theorem ruleConstructor_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : ConstructorReading entries shape source constants reading) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs minors : List V} (m : V)
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor xs fs)
    (hmlen : minors.length = shape.constructors.length) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleConstructor source mode i ctor) =
      shape.constructorValue constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor i xs fs := by
  have hflen : fs.length = ctor.recursive.length := by simpa using FitsS.length_eq hfs
  have ht := constructorVars_interp hr hn hc ps (m :: minors) (xs ++ fs) [] (FitsS.length_eq hps)
  rw [← List.append_assoc, constructorClosedValue_apply h hM hc hps hxs hfs] at ht
  simpa only [ruleConstructor, List.length_cons, List.length_nil, List.length_append,
    hmlen, FitsS.length_eq hxs, hflen, Nat.add_zero, Nat.zero_add, Telescope.extend_append, Telescope.extend,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem ruleIndices_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : FamilyReading entries shape source constants reading)
    (hn : levels.length = mode.recUvars shape.universes) {ctor : Constructor β} (hc : ctor ∈ shape.constructors)
    (ps xs fs minors : List V) (m : V) (hxlen : xs.length = ctor.fields.length)
    (hflen : fs.length = ctor.recursive.length) (hmlen : minors.length = shape.constructors.length) :
    (shape.ruleIndices mode ctor).map (interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)) =
      ctor.indices.map (interp constants (mode.sourceArgs levels)
        (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)) := by
  rw [ruleIndices, List.map_map]
  apply List.map_congr_left
  intro e he
  have ht := hr.agrees.interp_inserted levels (mode.sourceLevels shape.universes)
    (Telescope.extend (fun _ => empty) ps) (m :: minors) xs fs []
    ((h.constructors ctor hc).1 e (List.mem_append_right _ he))
  simpa only [mode.sourceLevels_eval hn, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
    hxlen, hflen, hmlen, Telescope.extend, Nat.add_comm, Function.comp_def] using ht

theorem ruleLhsBody_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source mode constants reading)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs minors : List V} {m : V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor xs fs)
    (hm : m ∈ˢ shape.motiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels) m minors) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleLhsBody source mode i ctor) =
      Telescope.applyN (shape.recursorAt constants levels (Telescope.extend (fun _ => empty) ps) mode m minors)
        (ctor.indices.map (interp constants (mode.sourceArgs levels) (Telescope.extend (Telescope.extend (fun _ => empty) ps) xs)) ++
          [shape.constructorValue constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor i xs fs]) := by
  have hflen : fs.length = ctor.recursive.length := by simpa using FitsS.length_eq hfs
  have hmlen : minors.length = shape.constructors.length := by
    simpa only [minorTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hminors
  have hprefix := interp_parameterVars_middle reading levels (fun _ => empty) (ps ++ [m] ++ minors) (xs ++ fs)
  simp only [List.length_append, List.length_singleton, Telescope.extend_append, Telescope.extend,
    FitsS.length_eq hps, FitsS.length_eq hxs, hflen, hmlen] at hprefix
  have hcv := ruleConstructor_interp h hr.toConstructorReading hM hn hc m hps hxs hfs hmlen
  have hidx := ruleIndices_interp h hr.toFamilyReading hn (List.mem_of_getElem? hc)
    ps xs fs minors m (FitsS.length_eq hxs) hflen hmlen
  simp only [Telescope.extend] at hcv hidx
  rw [ruleLhsBody, AExpr.interp_appN]
  simp only [interp, ElimMode.recLevels, eval_params hn, hr.recursor _ hn, List.map_append,
    List.map_cons, List.map_nil, hcv, hidx, Telescope.extend, hprefix]
  rw [Telescope.applyN_append, Telescope.applyN_append, closedRecursorValue_apply h hmode hM hps hm hminors,
    Telescope.applyN_append]

theorem ruleRhsBody_interp (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source mode constants reading)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs minors : List V} {m : V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor xs fs)
    (hm : m ∈ˢ shape.motiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels) m minors) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleRhsBody source mode i ctor) =
      Telescope.applyN (minors.getD i empty)
        (xs ++ fs ++ shape.recursorCalls constants levels (Telescope.extend (fun _ => empty) ps) mode m minors ctor xs fs) := by
  have hflen : fs.length = ctor.recursive.length := by simpa using FitsS.length_eq hfs
  have hmlen : minors.length = shape.constructors.length := by
    simpa only [minorTypes, List.length_map, List.length_zipIdx] using FitsS.length_eq hminors
  have hmvar : Telescope.extend
      (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs
      (shape.constructors.length - 1 - i + ctor.fields.length + ctor.recursive.length) = minors.getD i empty := by
    have ht := (Telescope.extend_beyond (Telescope.extend (Valuation.cons m (Telescope.extend (fun _ => empty) ps)) minors)
      (xs ++ fs) (minors.length - 1 - i)).trans
      (Telescope.extend_getD _ minors i (by rw [hmlen]; exact (List.getElem?_eq_some_iff.mp hc).1))
    simpa only [List.length_append, hmlen, FitsS.length_eq hxs, hflen,
      Telescope.extend_append, Telescope.extend, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using ht
  have hfields := interp_parameterVars_extend reading levels
    (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) (xs ++ fs)
  simp only [List.length_append, FitsS.length_eq hxs, hflen, Telescope.extend_append] at hfields
  have hcalls : (ctor.recursive.zipIdx.map fun (field, j) => shape.ruleCall source mode ctor j field).map
      (interp reading levels (Telescope.extend
        (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)) =
      shape.recursorCalls constants levels (Telescope.extend (fun _ => empty) ps) mode m minors ctor xs fs := by
    apply List.ext_getElem?
    intro j
    simp only [recursorCalls, List.getElem?_map, List.getElem?_zipIdx]
    cases hf : ctor.recursive[j]? with
    | none => rfl
    | some field =>
      simp only [Option.map_some, Nat.zero_add]
      exact congrArg some (ruleCall_interp h hr hmode hM hn (List.mem_of_getElem? hc) hf hps hxs hflen hm hminors)
  rw [ruleRhsBody, AExpr.interp_appN]
  simp only [interp, hmvar, List.map_append, hfields, hcalls]

theorem large_ruleBody_eq (h : CheckedShape.{u,v} entries source shape)
    (hr : RecursorReading entries shape source .large constants reading)
    (hmode : ModeEvidence.{u,v} entries shape .large) (hM : Realizes constants entries)
    (hn : levels.length = ElimMode.large.recUvars shape.universes) {i : Nat} {ctor : Constructor β}
    (hc : shape.constructors[i]? = some ctor) {ps xs fs minors : List V} {m : V}
    (hps : FitsS (Telescope.interpret constants (ElimMode.large.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    (hxs : FitsS (Telescope.interpret constants (ElimMode.large.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor.fields) xs)
    (hfs : shape.RecursiveValuesFit constants (ElimMode.large.sourceArgs levels) (Telescope.extend (fun _ => empty) ps) ctor xs fs)
    (hm : m ∈ˢ shape.motiveSet constants (ElimMode.large.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (ElimMode.large.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (ElimMode.large.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (ElimMode.large.motiveLevel.eval levels) m minors) :
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleLhsBody source .large i ctor) =
    interp reading levels
      (Telescope.extend (Telescope.extend (Telescope.extend (Telescope.extend (fun _ => empty) ps) (m :: minors)) xs) fs)
      (shape.ruleRhsBody source .large i ctor) := by
  rw [ruleLhsBody_interp h hr hmode hM hn hc hps hxs hfs hm hminors,
    ruleRhsBody_interp h hr hmode hM hn hc hps hxs hfs hm hminors]
  have hΓ := h.parameters.valid constants hM (ElimMode.large.sourceArgs levels)
    (Context.valid_nil constants (ElimMode.large.sourceArgs levels) (fun _ => empty)) hps
  have hD := container_wf h hM hΓ
  have hlarge := container_large hmode hM hΓ
  rw [recursorAt_large _ _ _ _ _ _ hD hlarge]
  simp only [recursorCalls, recursorCall_large _ _ _ _ _ _ _ _ _ _ hD hlarge]
  exact largeValue_iota h hM hΓ hm hminors hD hlarge hc hxs hfs

end Ix.Kernel.Certified.Ordinary.Shape
