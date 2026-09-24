/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Natural/Publish.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store, its exact-source facts, the `EntrySource` provenance, and
the pin parameter are removed; the recursor is member 1 of the family's block;
`succApp` proves the successor's function membership for the fact's meaning.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Natural.Checked

namespace Ix.Kernel.Certified.Natural

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel

universe u v
variable {β : Type u} [DecidableEq β] {entries : Environment β} {source : β} {mode : Inductive.ElimMode}

theorem family_lookup (h : Checked.{u,v} entries source mode) :
    shape.publishedEnvironment entries source mode (.member source 0) = some (shape : Ordinary.Shape β).familyEntry := by
  apply Environment.insert_old h.block.recursorChecked.fresh
  simp [Ordinary.Shape.constructorEnvironment, Environment.overlay, Ordinary.Shape.constructorEntries,
    Ordinary.Shape.familyEnvironment]

theorem succ_lookup (h : Checked.{u,v} entries source mode) :
    shape.publishedEnvironment entries source mode (.ctor source 0 1) =
      some ((shape : Ordinary.Shape β).constructorEntry source succConstructor) := by
  apply Environment.insert_old h.block.recursorChecked.fresh
  simp [Ordinary.Shape.constructorEnvironment, Environment.overlay, Ordinary.Shape.constructorEntries, shape]

theorem environment_wf (h : Checked.{u,v} entries source mode) (hE : entries.WF) :
    (environment entries source mode).WF := by
  have hb := Ordinary.Shape.publishedEnvironment_wf h.block hE
  exact hb.insert (hb.typeScope _ (shape : Ordinary.Shape β).familyEntry (family_lookup h))
    (by simp [entry, Ordinary.Shape.familyEntry])
    (hb.typeReferences _ (shape : Ordinary.Shape β).familyEntry (family_lookup h))
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, Ordinary.Shape.familyEntry])
    (by simp [entry, fact, ConstantFact.Scope, shape, Ordinary.Shape.familyEntry])
    (by simpa only [entry, List.mem_singleton, forall_eq] using h.references)

theorem environment_old (h : Checked.{u,v} entries source mode)
    {r : ConstRef β} {old : ConstantEntry β} (hr : entries r = some old) :
    environment entries source mode r = some old := by
  simp only [environment, Environment.insert,
    if_neg (fresh_ne (h.block.shapeChecked.fresh _ (List.mem_cons_self ..)) hr)]
  exact Ordinary.Shape.publishedEnvironment_old h.block hr

variable {V : Type v} [SetTheory V]

/-- The successor constructor is a function on the carrier, which contains
every numeral: the meaning of `natural` needed for literal unfolding. -/
theorem succApp (h : Checked.{u,v} entries source mode) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) (n : Nat) :
    ∃ (v : Nat) (A : V) (B : V → V),
      shape.recursorAssignment constants source mode (.ctor source 0 1) [] ∈ˢ piR v A B ∧
        Numeral.value n ∈ˢ A ∧ ∀ x, x ∈ˢ A → B x ∈ˢ univ v := by
  have hb := Ordinary.Shape.publishedAssignment_realizes h.block hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.block.shapeChecked h.block.recursorChecked constants
  have hmem := hb.member _ _ (succ_lookup h) [] rfl (fun _ => empty)
  have hfam := hb.member _ _ (family_lookup h) [] rfl (fun _ => empty)
  refine ⟨1, shape.recursorAssignment constants source mode (.member source 0) [],
    fun _ => shape.recursorAssignment constants source mode (.member source 0) [], ?_, ?_, ?_⟩
  · simpa [Ordinary.Shape.constructorEntry, Ordinary.Constructor.type, Ordinary.Constructor.recursiveTypes,
      Ordinary.recursiveTypesFrom, Ordinary.RecursiveField.type, Ordinary.Shape.familyApp,
      Ordinary.parameterVars, shape, succConstructor, AExpr.forallN, AExpr.appN, AExpr.liftN, VLevel.params,
      List.range_zero, List.map_nil, interp, zeroCondition] using hmem
  · rw [hr.family [] rfl]
    exact value_mem h.block.shapeChecked hM n
  · intro x _
    simpa [Ordinary.Shape.familyEntry, Ordinary.Shape.type, shape, AExpr.forallN, interp, VLevel.eval] using hfam

theorem assignment_realizes (h : Checked.{u,v} entries source mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.recursorAssignment constants source mode) (environment entries source mode) := by
  have hb := Ordinary.Shape.publishedAssignment_realizes h.block hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.block.shapeChecked h.block.recursorChecked constants
  apply hb.insert
  constructor
  · exact hb.typeValid _ (shape : Ordinary.Shape β).familyEntry (family_lookup h)
  · exact hb.member _ (shape : Ordinary.Shape β).familyEntry (family_lookup h)
  · intro body hbody; cases hbody
  · intro body hbody; cases hbody
  · intro law hl; cases hl
  · intro f hf levels hn _
    cases List.mem_singleton.mp hf
    have he : levels = [] := List.eq_nil_of_length_eq_zero hn
    subst levels
    exact ⟨rfl, meaning h.block.shapeChecked hr.toConstructorReading hM (succApp h hE constants hM)⟩

end Ix.Kernel.Certified.Natural
