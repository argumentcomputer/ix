/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Structure/Publish.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store, its exact-source facts, and the `EntrySource` provenance
are removed and the recursor is member 1 of the family's block; the published
entry and environment are defined in `Checked` (rules are typed in the
published environment); the family entry carries the `structure` arity fact.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Structure.Checked

namespace Ix.Kernel.Certified.Structure

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

theorem ordinary_family_lookup {entries : Environment β}
    {source : β} {shape : Ordinary.Shape β} {mode : Inductive.ElimMode}
    (h : Ordinary.CheckedBlock.{u,v} entries source shape mode) :
    shape.publishedEnvironment entries source mode (.member source 0) = some shape.familyEntry := by
  apply Environment.insert_old h.recursorChecked.fresh
  simp [Ordinary.Shape.constructorEnvironment, Environment.overlay, Ordinary.Shape.constructorEntries,
    Ordinary.Shape.familyEnvironment]

/-- References survive replacing the entry at one key. -/
theorem _root_.Ix.Kernel.Model.AExpr.ReferencesIn.insertReplace {E : Environment β} {r : ConstRef β}
    {a b : ConstantEntry β} {e : AExpr β} (h : e.ReferencesIn (E.insert r a)) :
    e.ReferencesIn (E.insert r b) := by
  intro q hq
  have hv := h q hq
  by_cases hqr : q = r
  · subst hqr; simp
  · simpa [Environment.insert, hqr] using hv

namespace Description

variable {d : Description β} {entries : Environment β} {source : β} {mode : Inductive.ElimMode}

theorem factEnvironment_wf (h : FactsChecked.{u,v} entries d source mode) (hE : entries.WF) :
    (d.factEnvironment entries source mode).WF := by
  have hbase := Ordinary.Shape.publishedEnvironment_wf h.block hE
  have hfam := ordinary_family_lookup h.block
  exact hbase.insert (hbase.typeScope _ d.ordinary.familyEntry hfam) (by simp [factEntry, Ordinary.Shape.familyEntry])
    (hbase.typeReferences _ d.ordinary.familyEntry hfam) (by simp [factEntry, Ordinary.Shape.familyEntry])
    (by simp [factEntry, Ordinary.Shape.familyEntry]) (by simp [factEntry, Ordinary.Shape.familyEntry])
    (by
      intro fact hf
      simp only [factEntry, List.mem_cons] at hf
      rcases hf with rfl | hf
      · trivial
      · exact h.scope fact hf)
    (by
      intro fact hf
      simp only [factEntry, List.mem_cons] at hf
      rcases hf with rfl | hf
      · intro q hq; simp [ConstantFact.references, structureFact] at hq
      · exact h.references fact hf)

theorem publishedEnvironment_wf (h : Checked.{u,v} entries d source mode) (hE : entries.WF) :
    (d.publishedEnvironment entries source mode).WF := by
  have hbase := d.factEnvironment_wf h.facts hE
  have hwf := hbase.insert (r := .member source 0) (entry := d.publishedEntry source)
    (hbase.typeScope _ (d.factEntry source) (Environment.insert_same ..))
    (by simp [publishedEntry, factEntry, Ordinary.Shape.familyEntry])
    (hbase.typeReferences _ (d.factEntry source) (Environment.insert_same ..))
    (by simp [publishedEntry, factEntry, Ordinary.Shape.familyEntry])
    (by
      intro law hl
      rcases List.mem_cons.mp hl with he | hrest
      · cases he; exact h.eta.scope.2
      · obtain ⟨⟨field, i⟩, hfi, he⟩ := List.mem_map.mp hrest
        cases he
        exact (h.iota field i hfi).scope.2)
    (by
      intro law hl
      rcases List.mem_cons.mp hl with he | hrest
      · cases he
        exact ⟨AExpr.ReferencesIn.insertReplace h.eta.references.2.1,
          AExpr.ReferencesIn.insertReplace h.eta.references.2.2⟩
      · obtain ⟨⟨field, i⟩, hfi, he⟩ := List.mem_map.mp hrest
        cases he
        exact ⟨AExpr.ReferencesIn.insertReplace (h.iota field i hfi).references.2.1,
          AExpr.ReferencesIn.insertReplace (h.iota field i hfi).references.2.2⟩)
    (hbase.factScope _ (d.factEntry source) (Environment.insert_same ..))
    (hbase.factReferences _ (d.factEntry source) (Environment.insert_same ..))
  simpa only [publishedEnvironment, factEnvironment, Environment.insert_replace] using hwf

theorem publishedEnvironment_old (h : Checked.{u,v} entries d source mode)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry) :
    d.publishedEnvironment entries source mode r = some entry := by
  simp only [publishedEnvironment, Environment.insert,
    if_neg (fresh_ne (h.facts.block.shapeChecked.fresh _ (List.mem_cons_self ..)) hr)]
  exact Ordinary.Shape.publishedEnvironment_old h.facts.block hr

variable {V : Type v} [SetTheory V]

theorem factAssignment_realizes (h : FactsChecked.{u,v} entries d source mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (d.ordinary.recursorAssignment constants source mode)
      (d.factEnvironment entries source mode) := by
  have hbase := Ordinary.Shape.publishedAssignment_realizes h.block hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.block.shapeChecked h.block.recursorChecked constants
  apply hbase.insert
  constructor
  · exact hbase.typeValid _ d.ordinary.familyEntry (ordinary_family_lookup h.block)
  · exact hbase.member _ d.ordinary.familyEntry (ordinary_family_lookup h.block)
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; cases hl
  · intro fact hf levels hn env
    simp only [factEntry, List.mem_cons] at hf
    rcases hf with rfl | hf
    · trivial
    obtain ⟨⟨field, i⟩, hi, rfl⟩ := List.mem_map.mp hf
    have hscope := h.scope _ (List.mem_map.mpr ⟨(field, i), hi, rfl⟩)
    exact d.projection_meaning h.block.shapeChecked h.fields hr.toFamilyReading hM hn hbase h.domains
      (List.mk_mem_zipIdx_iff_getElem?.mp hi) hscope env

theorem publishedAssignment_realizes (h : Checked.{u,v} entries d source mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (d.ordinary.recursorAssignment constants source mode)
      (d.publishedEnvironment entries source mode) := by
  have hbase := d.factAssignment_realizes h.facts hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.facts.block.shapeChecked h.facts.block.recursorChecked constants
  have hlocal : EntryRealization (d.ordinary.recursorAssignment constants source mode)
      (.member source 0) (d.publishedEntry source) := by
    constructor
    · exact hbase.typeValid _ (d.factEntry source) (Environment.insert_same ..)
    · exact hbase.member _ (d.factEntry source) (Environment.insert_same ..)
    · intro body hb; cases hb
    · intro body hb; cases hb
    · intro law hl levels hn env
      rcases List.mem_cons.mp hl with he | hrest
      · cases he
        exact (interp_closed (d.etaLhs source) _ levels h.eta.scope.2.1 (fun _ => empty) env).symm.trans
          ((d.eta_eq h.facts.block.shapeChecked h.facts.fields hr.toConstructorReading hM hn).trans
            (interp_closed (d.etaRhs source) _ levels h.eta.scope.2.2 (fun _ => empty) env))
      · obtain ⟨⟨field, i⟩, hfi, he⟩ := List.mem_map.mp hrest
        cases he
        exact (interp_closed (d.iotaLhs source i field) _ levels (h.iota field i hfi).scope.2.1 (fun _ => empty) env).symm.trans
          ((d.iota_eq h.facts.block.shapeChecked h.facts.fields hr.toConstructorReading hM hn
            (List.mk_mem_zipIdx_iff_getElem?.mp hfi)).trans
            (interp_closed (d.iotaRhs i field) _ levels (h.iota field i hfi).scope.2.2 (fun _ => empty) env))
    · exact hbase.factMeaning _ (d.factEntry source) (Environment.insert_same ..)
  simpa only [publishedEnvironment, factEnvironment, Environment.insert_replace] using hbase.insert hlocal

end Description
end Ix.Kernel.Certified.Structure
