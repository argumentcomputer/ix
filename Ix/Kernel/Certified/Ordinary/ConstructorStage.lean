/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/ConstructorStage.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `checkConstructorTypes` infers instead of
validating witnesses.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RecursorValue
import Ix.Kernel.Model.Signature

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel

universe u v
variable {β : Type u} [DecidableEq β]

namespace Shape

def constructorEntry (shape : Shape β) (source : β) (ctor : Constructor β) : ConstantEntry β :=
  ⟨shape.universes, ctor.type shape source, none, [], []⟩

def constructorEntries (shape : Shape β) (source : β) : Environment β
  | .ctor b 0 i => if b = source then (shape.constructors[i]?).map (shape.constructorEntry source) else none
  | _ => none

theorem constructorEntries_some {shape : Shape β} {source : β} {r : ConstRef β} {entry : ConstantEntry β}
    (h : shape.constructorEntries source r = some entry) :
    ∃ i ctor, r = .ctor source 0 i ∧ shape.constructors[i]? = some ctor ∧ entry = shape.constructorEntry source ctor := by
  cases r with
  | member _ _ => simp [constructorEntries] at h
  | ctor b member i =>
    cases member with
    | succ _ => simp [constructorEntries] at h
    | zero =>
      by_cases hb : b = source
      · subst b
        simp only [constructorEntries, ↓reduceIte] at h
        obtain ⟨ctor, hc, he⟩ := Option.map_eq_some_iff.mp h
        exact ⟨i, ctor, rfl, hc, he.symm⟩
      · simp [constructorEntries, hb] at h

def constructorEnvironment (shape : Shape β) (entries : Environment β) (source : β) : Environment β :=
  (shape.familyEnvironment entries source).overlay (shape.constructorEntries source)

theorem constructorEntries_fresh {entries : Environment β} {source : β} {shape : Shape β}
    (h : CheckedShape.{u,v} entries source shape) :
    (shape.familyEnvironment entries source).Fresh (shape.constructorEntries source) := by
  intro r entry hr
  obtain ⟨i, ctor, rfl, hc, _⟩ := constructorEntries_some hr
  have hf := h.fresh (.ctor source 0 i) (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1, rfl⟩))
  simpa [familyEnvironment, Environment.insert] using hf

def ConstructorFormation (entries : Environment β) (shape : Shape β) (source : β) : Prop :=
  ∀ ctor ∈ shape.constructors,
    EntryClosed (shape.familyEnvironment entries source) (shape.constructorEntry source ctor) ∧
    ∃ l, TypingClaim.{u,v} (shape.familyEnvironment entries source) [] (ctor.type shape source) (.sort l)

def checkConstructorTypes (fuel : Nat) (entries : Environment β) (shape : Shape β) (source : β) :
    (ctors : List (Constructor β)) →
      Option (CheckedClaim.{u} (∀ ctor ∈ ctors,
        EntryClosed (shape.familyEnvironment entries source) (shape.constructorEntry source ctor) ∧
        ∃ l, TypingClaim.{u,v} (shape.familyEnvironment entries source) [] (ctor.type shape source) (.sort l)))
  | [] => some ⟨by simp⟩
  | ctor :: ctors =>
    if hs : (ctor.type shape source).Scope shape.universes 0 then
      if hr : (ctor.type shape source).ReferencesIn (shape.familyEnvironment entries source) then do
        let ⟨l, ht⟩ ← checkSort.{u,v} fuel (shape.familyEnvironment entries source) [] (ctor.type shape source)
        let rest ← checkConstructorTypes fuel entries shape source ctors
        return ⟨by
          intro ctor' hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨⟨hs, by simp [constructorEntry], hr, by simp [constructorEntry],
              by simp [constructorEntry], by simp [constructorEntry],
              by simp [constructorEntry], by simp [constructorEntry]⟩, l, ht⟩
          · exact rest.down ctor' hc⟩
      else none
    else none

theorem constructorEnvironment_wf {entries : Environment β} {source : β} {shape : Shape β}
    (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF)
    (hT : ConstructorFormation.{u,v} entries shape source) :
    (shape.constructorEnvironment entries source).WF := by
  apply (familyEnvironment_wf h hE).overlay
  intro r entry hr
  obtain ⟨i, ctor, rfl, hc, rfl⟩ := constructorEntries_some hr
  exact (hT ctor (List.mem_of_getElem? hc)).1

variable {V : Type v} [SetTheory V]

noncomputable def constructorValues (shape : Shape β) (constants : Assignment β V) : Assignment β V
  | .ctor _ 0 i, levels =>
    match shape.constructors[i]? with
    | some ctor => shape.constructorClosedValue constants levels i ctor
    | none => empty
  | _, _ => empty

noncomputable def constructorAssignment (shape : Shape β) (constants : Assignment β V) (source : β) : Assignment β V :=
  (shape.familyAssignment constants source).overlay (shape.constructorValues constants) (shape.constructorEntries source)

theorem constructorAssignment_agreesFamily {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (constants : Assignment β V) :
    Assignment.AgreesOn (shape.familyEnvironment entries source) (shape.familyAssignment constants source)
      (shape.constructorAssignment constants source) :=
  Assignment.overlay_agrees (constructorEntries_fresh h) _ _

theorem constructorAssignment_reading {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (constants : Assignment β V) :
    ConstructorReading entries shape source constants (shape.constructorAssignment constants source) where
  agrees := by
    intro r entry hr levels
    exact (constructorAssignment_agreesFamily h constants r entry
      (Environment.insert_old (h.fresh _ (List.mem_cons_self ..)) hr) levels).trans
      (familyAssignment_agrees h constants r entry hr levels)
  family := by
    intro levels _
    simp only [constructorAssignment, Assignment.overlay, constructorEntries,
      familyAssignment, Assignment.insert_same]
  constructor := by
    intro levels _ i ctor hc
    simp only [constructorAssignment, Assignment.overlay, constructorEntries,
      ↓reduceIte, hc, Option.map_some, constructorValues]

theorem constructorAssignment_realizes {entries : Environment β} {source : β}
    {shape : Shape β} (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF)
    (hT : ConstructorFormation.{u,v} entries shape source)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.constructorAssignment constants source) (shape.constructorEnvironment entries source) := by
  have hr := constructorAssignment_reading h constants
  have hbase := (familyAssignment_realizes h hE constants hM).of_agrees
    (familyEnvironment_wf h hE) (constructorAssignment_agreesFamily h constants)
  apply hbase.overlay
  intro r entry hentry
  obtain ⟨i, ctor, rfl, hc, rfl⟩ := constructorEntries_some hentry
  obtain ⟨hclosed, l, htype⟩ := hT ctor (List.mem_of_getElem? hc)
  constructor
  · intro levels hn env
    exact (htype V _ hbase levels env (Context.valid_nil _ _ _)).1
  · intro levels hn env
    rw [hr.constructor levels hn i ctor hc]
    have hm := constructorClosedValue_mem_source h hr.toFamilyReading hM hn hc
    rwa [interp_closed (ctor.type shape source) _ levels hclosed.typeScope (fun _ => empty) env] at hm
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; simp only [constructorEntry, List.not_mem_nil] at hl
  · intro fact hf; simp only [constructorEntry, List.not_mem_nil] at hf

end Shape
end Ix.Kernel.Certified.Ordinary
