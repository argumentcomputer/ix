/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/Family.lean
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

import Ix.Kernel.Certified.Ordinary.Computation
import Ix.Kernel.Model.Extension

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

theorem eval_params {n : Nat} {levels : List Nat} (h : levels.length = n) :
    (VLevel.params n).map (VLevel.eval levels) = levels := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  simp only [VLevel.params, List.getElem_map, List.getElem_range, VLevel.eval,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem interp_parameterVars_skip (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (offset count : Nat) :
    (parameterVars offset count).map (interp constants levels env) =
      (parameterVars 0 count).map (interp constants levels (Valuation.skip offset 0 env)) := by
  induction count <;> simp_all [parameterVars, interp, Valuation.skip]

theorem interp_parameterVars_extend (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (xs : List V) :
    (parameterVars 0 xs.length).map (interp constants levels (Telescope.extend env xs)) = xs := by
  induction xs generalizing env with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, parameterVars, Nat.zero_add, List.map_cons, interp,
      Telescope.extend, ih]
    have he := Telescope.extend_beyond (Valuation.cons x env) xs 0
    simpa only [Nat.add_zero, Valuation.cons_zero] using congrArg (· :: xs) he

theorem interp_parameterVars_middle (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (xs tail : List V) :
    (parameterVars tail.length xs.length).map
      (interp constants levels (Telescope.extend (Telescope.extend env xs) tail)) = xs := by
  rw [interp_parameterVars_skip, Telescope.skip_extend, interp_parameterVars_extend]

namespace Shape

noncomputable def familyValue (shape : Shape β) (constants : Assignment β V) (levels : List Nat) : V :=
  Telescope.curry 1 (Telescope.interpret constants levels (fun _ => empty) shape.parameters) fun ps =>
    Telescope.curry 1 (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) shape.indices)
      (fun is => app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps)) (mkTower is))

theorem type_typing {entries : Environment β} {source : β} {shape : Shape β}
    (h : CheckedShape.{u,v} entries source shape) :
    ∃ l, TypingClaim.{u,v} entries [] shape.type (.sort l) := by
  obtain ⟨l, _, hl⟩ := (h.parameters.append h.indices).forallN (TypingClaim.sort shape.level)
  exact ⟨l, hl⟩

theorem type_references {entries : Environment β} {source : β} {shape : Shape β}
    (h : CheckedShape.{u,v} entries source shape) : shape.type.ReferencesIn entries :=
  AExpr.ReferencesIn.forallN h.references (by simp [AExpr.ReferencesIn, AExpr.references])

theorem familyValue_mem (shape : Shape β) (constants : Assignment β V) (levels : List Nat) :
    shape.familyValue constants levels ∈ˢ interp constants levels (fun _ => empty) shape.type := by
  simp only [type, AExpr.forallN_append, AExpr.interp_forallN, regime_never, interp]
  apply Telescope.curry_mem
  intro ps hps
  apply Telescope.curry_mem
  intro is his
  exact (shape.container constants levels (Telescope.extend (fun _ => empty) ps)).carrier_fibre_mem
    (shape.level.eval levels) (mkTower_mem (by decide : 1 ≠ 0) his)

theorem familyValue_apply (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    {ps is : List V}
    (hps : FitsS (Telescope.interpret constants levels (fun _ => empty) shape.parameters) ps)
    (his : FitsS (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) ps) shape.indices) is) :
    Telescope.applyN (shape.familyValue constants levels) (ps ++ is) =
      app (shape.carrier constants levels (Telescope.extend (fun _ => empty) ps)) (mkTower is) := by
  have hresult xs ys hys :=
    (shape.container constants levels (Telescope.extend (fun _ => empty) xs)).carrier_fibre_mem
      (shape.level.eval levels) (i := mkTower ys) (mkTower_mem (by decide : 1 ≠ 0) hys)
  have hinner xs := Telescope.curry_mem (w := 1)
    (Telescope.interpret constants levels (Telescope.extend (fun _ => empty) xs) shape.indices) (hresult xs)
  simp only [familyValue, carrier]
  rw [Telescope.applyN_append,
    Telescope.applyN_curry (w := 1) _ hps (fun xs _ => hinner xs) (fun h => (by omega : False).elim)]
  exact Telescope.applyN_curry _ his (hresult ps) (fun h => (by omega : False).elim)

def familyEntry (shape : Shape β) : ConstantEntry β := ⟨shape.universes, shape.type, none, [], []⟩

def familyEnvironment [DecidableEq β] (shape : Shape β) (entries : Environment β) (source : β) : Environment β :=
  entries.insert (.member source 0) shape.familyEntry

noncomputable def familyAssignment [DecidableEq β] (shape : Shape β) (constants : Assignment β V)
    (source : β) : Assignment β V := constants.insert (.member source 0) (shape.familyValue constants)

theorem familyEnvironment_wf [DecidableEq β] {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF) :
    (shape.familyEnvironment entries source).WF :=
  hE.insert h.scope (by simp [familyEntry]) (type_references h) (by simp [familyEntry])
    (by simp [familyEntry]) (by simp [familyEntry])
    (by simp [familyEntry]) (by simp [familyEntry])

theorem familyAssignment_agrees [DecidableEq β] {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (shape.familyAssignment constants source) :=
  Assignment.insert_agrees (h.fresh _ (List.mem_cons_self ..)) constants (shape.familyValue constants)

/-- The family signature receives its constructed carrier before constructor
or recursor checking. This is an internal stage with no reduction equations. -/
theorem familyAssignment_realizes [DecidableEq β] {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.familyAssignment constants source) (shape.familyEnvironment entries source) := by
  have hagree := familyAssignment_agrees h constants
  have hrefs := type_references h
  obtain ⟨l, htype⟩ := type_typing h
  apply (hM.of_agrees hE hagree).insert
  constructor
  · intro levels hn env
    exact (hagree.wellDenoted hrefs levels env).mpr
      (htype V constants hM levels env (Context.valid_nil constants levels env)).1
  · intro levels hn env
    change shape.familyAssignment constants source (.member source 0) levels ∈ˢ
      interp (shape.familyAssignment constants source) levels env shape.type
    rw [hagree.interp hrefs levels env, familyAssignment, Assignment.insert_same]
    have hm := shape.familyValue_mem constants levels
    rwa [interp_closed shape.type constants levels h.scope (fun _ => empty) env] at hm
  · intro body hb
    cases hb
  · intro body hb
    cases hb
  · intro law hl
    simp only [familyEntry, List.not_mem_nil] at hl
  · intro fact hf
    simp only [familyEntry, List.not_mem_nil] at hf

end Shape
end Ix.Kernel.Certified.Ordinary
