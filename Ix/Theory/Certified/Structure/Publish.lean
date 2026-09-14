/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Structure.Checked

namespace Ix.Theory.Certified.Structure

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

theorem ordinary_family_lookup {entries : Environment β} {store : Store β}
    {source recursor : β} {shape : Ordinary.Shape β} {mode : Inductive.ElimMode}
    (h : Ordinary.CheckedBlock.{u,v} entries store source recursor shape mode) :
    shape.publishedEnvironment entries source recursor mode (.member source 0) = some shape.familyEntry := by
  apply Environment.insert_old h.recursorChecked.fresh
  simp [Ordinary.Shape.constructorEnvironment, Environment.overlay, Ordinary.Shape.constructorEntries,
    Ordinary.Shape.familyEnvironment]

namespace Description

def publishedEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.factEntry source with equations := d.equations source }

def publishedEnvironment (d : Description β) (entries : Environment β) (source recursor : β)
    (mode : Inductive.ElimMode) : Environment β :=
  (d.ordinary.publishedEnvironment entries source recursor mode).insert (.member source 0) (d.publishedEntry source)

variable {d : Description β} {entries : Environment β} {store : Store β}
  {source recursor : β} {mode : Inductive.ElimMode}

theorem iotaEnvironment_references {i : Nat} {e : AExpr β}
    (h : e.ReferencesIn (d.iotaEnvironment entries source recursor mode i)) :
    e.ReferencesIn (d.factEnvironment entries source recursor mode) := by
  intro r hr
  have he := h r hr
  by_cases heq : r = .member source 0
  · simp [factEnvironment, Environment.insert, heq]
  · simpa only [iotaEnvironment, factEnvironment, Environment.insert, if_neg heq] using he

theorem factEnvironment_wf (h : FactsChecked.{u,v} entries store d source recursor mode) (hE : entries.WF) :
    (d.factEnvironment entries source recursor mode).WF := by
  have hbase := Ordinary.Shape.publishedEnvironment_wf h.block hE
  have hfam := ordinary_family_lookup h.block
  exact hbase.insert (hbase.typeScope _ d.ordinary.familyEntry hfam) (by simp [factEntry, Ordinary.Shape.familyEntry])
    (hbase.typeReferences _ d.ordinary.familyEntry hfam) (by simp [factEntry, Ordinary.Shape.familyEntry])
    (by simp [factEntry, Ordinary.Shape.familyEntry]) (by simp [factEntry, Ordinary.Shape.familyEntry])
    h.scope h.references

theorem publishedEnvironment_wf (h : Checked.{u,v} entries store d source recursor mode) (hE : entries.WF) :
    (d.publishedEnvironment entries source recursor mode).WF := by
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
      · cases he; exact h.eta.references.2
      · obtain ⟨⟨field, i⟩, hfi, he⟩ := List.mem_map.mp hrest
        cases he
        exact ⟨iotaEnvironment_references (h.iota field i hfi).references.2.1,
          iotaEnvironment_references (h.iota field i hfi).references.2.2⟩)
    h.facts.scope (fun fact hf => (h.facts.references fact hf).insert)
  simpa only [publishedEnvironment, factEnvironment, Environment.insert_replace] using hwf

theorem publishedEnvironment_old (h : Checked.{u,v} entries store d source recursor mode)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry) :
    d.publishedEnvironment entries source recursor mode r = some entry := by
  simp only [publishedEnvironment, Environment.insert,
    if_neg (fresh_ne (h.facts.block.shapeChecked.fresh _ (List.mem_cons_self ..)) hr)]
  exact Ordinary.Shape.publishedEnvironment_old h.facts.block hr

variable {V : Type v} [SetTheory V]

theorem factAssignment_realizes (h : FactsChecked.{u,v} entries store d source recursor mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (d.ordinary.recursorAssignment constants source recursor mode)
      (d.factEnvironment entries source recursor mode) := by
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
    obtain ⟨⟨field, i⟩, hi, rfl⟩ := List.mem_map.mp hf
    have hscope := h.scope _ (List.mem_map.mpr ⟨(field, i), hi, rfl⟩)
    exact d.projection_meaning h.block.shapeChecked h.fields hr.toFamilyReading hM hn hbase h.domains
      (List.mk_mem_zipIdx_iff_getElem?.mp hi) hscope env

theorem publishedAssignment_realizes (h : Checked.{u,v} entries store d source recursor mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (d.ordinary.recursorAssignment constants source recursor mode)
      (d.publishedEnvironment entries source recursor mode) := by
  have hbase := d.factAssignment_realizes h.facts hE constants hM
  have hr := Ordinary.Shape.recursorAssignment_reading h.facts.block.shapeChecked h.facts.block.recursorChecked constants
  have hlocal : EntryRealization (d.ordinary.recursorAssignment constants source recursor mode)
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

/-- The enhanced family entry has an exact source shape and exact recursor;
the projection facts and equations are wholly computed from that shape. -/
def EntrySource (store : Store β) (r : ConstRef β) (entry : ConstantEntry β) : Prop :=
  ∃ d : Description β, ∃ source recursor mode,
    store.blocks source = some ⟨[d.ordinary.source source]⟩ ∧
    d.ordinary.RecursorSourceMatches store source recursor mode ∧
    r = .member source 0 ∧ entry = d.publishedEntry source

theorem publishedEntry_source {entries : Environment β} {store : Store β}
    {d : Description β} {source recursor : β} {mode : Inductive.ElimMode}
    (h : Checked.{u,v} entries store d source recursor mode) {r : ConstRef β} {entry : ConstantEntry β}
    (hr : d.publishedEnvironment entries source recursor mode r = some entry) :
    entries r = some entry ∨ Ordinary.EntrySource store r entry ∨ EntrySource store r entry := by
  unfold Description.publishedEnvironment Environment.insert at hr
  split at hr
  next he =>
    cases Option.some.inj hr
    exact Or.inr (Or.inr ⟨d, source, recursor, mode, h.facts.block.shapeChecked.exactSource,
      h.facts.block.recursorChecked.exactSource, he, rfl⟩)
  next =>
    rcases Ordinary.publishedEntry_source h.facts.block hr with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inl hnew)

end Ix.Theory.Certified.Structure
