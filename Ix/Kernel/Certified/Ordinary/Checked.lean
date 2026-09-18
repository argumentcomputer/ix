/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/Checked.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `BlockWitness` and the `EntrySource`
provenance are removed, `checkBlock` takes the shape and mode, and the
published recursor entry carries `recursorFact` and the typed rule facts
`ruleFacts`, with their well-formedness and realization.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RuleEquations

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Inductive

universe u v
variable {β : Type u} [DecidableEq β]

structure CheckedBlock (entries : Environment β) (source : β)
    (shape : Shape β) (mode : ElimMode) : Prop where
  shapeChecked : CheckedShape.{u,v} entries source shape
  constructors : shape.ConstructorFormation.{u,v} entries source
  recursorChecked : shape.RecursorFormation.{u,v} entries source mode
  elimination : ModeEvidence.{u,v} entries shape mode
  rules : ∀ i ctor, shape.constructors[i]? = some ctor →
    shape.RuleFormation.{u,v} (shape.recursorEnvironment entries source mode) source mode i ctor

def checkBlock (fuel : Nat) (entries : Environment β) (source : β) (shape : Shape β) (mode : ElimMode) :
    Option (CheckedClaim.{u} (CheckedBlock.{u,v} entries source shape mode)) := do
  let shapeChecked ← checkShape.{u,v} fuel entries source shape
  let modeChecked ← checkMode.{u,v} fuel entries shape mode
  let constructors ← shape.checkConstructorTypes.{u,v} fuel entries source shape.constructors
  let recursor ← shape.checkRecursorType.{u,v} fuel entries source mode
  let rules ← shape.checkRules.{u,v} fuel (shape.recursorEnvironment entries source mode) source mode
    shape.constructors.zipIdx
  return ⟨⟨shapeChecked.down, constructors.down, recursor.down, modeChecked.down, fun i ctor hc =>
    rules.down ctor i (List.mk_mem_zipIdx_iff_getElem?.mpr hc)⟩⟩

theorem checkBlock_sound {fuel : Nat} {entries : Environment β} {source : β} {shape : Shape β}
    {mode : ElimMode} {result} (_ : checkBlock.{u,v} fuel entries source shape mode = some result) :
    CheckedBlock.{u,v} entries source shape mode := result.down

namespace Shape

/-- The arities and rule constructors the kernel reads to reduce the recursor. -/
def recursorFact (shape : Shape β) (source : β) : ConstantFact β :=
  .recursor shape.parameters.length shape.constructors.length shape.indices.length
    (shape.constructors.zipIdx.map fun (ctor, i) => (.ctor source 0 i, ctor.fields.length + ctor.recursive.length))

/-- Both endpoints of every rule, typed at the rule's type; the kernel reads
them when it reduces the recursor. -/
def ruleFacts (shape : Shape β) (source : β) (mode : ElimMode) : List (ConstantFact β) :=
  shape.constructors.zipIdx.flatMap fun (ctor, i) =>
    [.typed (shape.ruleLhs source mode i ctor) (shape.ruleType source mode i ctor),
      .typed (shape.ruleRhs source mode i ctor) (shape.ruleType source mode i ctor)]

def publishedRecursorEntry (shape : Shape β) (source : β) (mode : ElimMode) : ConstantEntry β :=
  { shape.recursorEntry source mode with
    equations := shape.recursorLaws source mode
    facts := shape.recursorFact source :: shape.ruleFacts source mode }

omit [DecidableEq β] in
theorem ruleFacts_member {shape : Shape β} {source : β} {mode : ElimMode}
    {fact : ConstantFact β} (hf : fact ∈ shape.ruleFacts source mode) :
    ∃ i ctor, shape.constructors[i]? = some ctor ∧
      (fact = .typed (shape.ruleLhs source mode i ctor) (shape.ruleType source mode i ctor) ∨
        fact = .typed (shape.ruleRhs source mode i ctor) (shape.ruleType source mode i ctor)) := by
  obtain ⟨⟨ctor, i⟩, hc, hm⟩ := List.mem_flatMap.mp hf
  refine ⟨i, ctor, List.mk_mem_zipIdx_iff_getElem?.mp hc, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact hm

def publishedEnvironment (shape : Shape β) (entries : Environment β) (source : β)
    (mode : ElimMode) : Environment β :=
  (shape.constructorEnvironment entries source).insert (.member source 1)
    (shape.publishedRecursorEntry source mode)

omit [DecidableEq β] in
theorem recursorLaws_member {shape : Shape β} {source : β} {mode : ElimMode}
    {law : ConstantEquation β} (hl : law ∈ shape.recursorLaws source mode) :
    ∃ i ctor, shape.constructors[i]? = some ctor ∧
      law = ⟨shape.ruleLhs source mode i ctor, shape.ruleRhs source mode i ctor⟩ := by
  obtain ⟨⟨ctor, i⟩, hc, he⟩ := List.mem_map.mp hl
  exact ⟨i, ctor, List.mk_mem_zipIdx_iff_getElem?.mp hc, he.symm⟩

theorem publishedEnvironment_wf {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries source shape mode)
    (hE : entries.WF) : (shape.publishedEnvironment entries source mode).WF := by
  have hwf := (recursorEnvironment_wf h.shapeChecked hE h.constructors h.recursorChecked).insert
    (r := .member source 1) (entry := shape.publishedRecursorEntry source mode)
    h.recursorChecked.closed.typeScope (by simp [publishedRecursorEntry, recursorEntry])
    h.recursorChecked.closed.typeReferences.insert (by simp [publishedRecursorEntry, recursorEntry])
    (by
      intro law hl
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact (h.rules i ctor hc).scope)
    (by
      intro law hl
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact (h.rules i ctor hc).references)
    (by
      intro fact hf
      simp only [publishedRecursorEntry, List.mem_cons] at hf
      rcases hf with rfl | hf
      · trivial
      · obtain ⟨i, ctor, hc, hf | hf⟩ := ruleFacts_member hf <;> subst hf
        · exact ⟨(h.rules i ctor hc).scope.1, (h.rules i ctor hc).typeScope⟩
        · exact ⟨(h.rules i ctor hc).scope.2, (h.rules i ctor hc).typeScope⟩)
    (by
      intro fact hf
      simp only [publishedRecursorEntry, List.mem_cons] at hf
      rcases hf with rfl | hf
      · intro q hq; simp [ConstantFact.references, recursorFact] at hq
      · obtain ⟨i, ctor, hc, hf | hf⟩ := ruleFacts_member hf <;> subst hf
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact (h.rules i ctor hc).references.1 q hq
          · exact (h.rules i ctor hc).typeReferences q hq
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact (h.rules i ctor hc).references.2 q hq
          · exact (h.rules i ctor hc).typeReferences q hq)
  simpa only [publishedEnvironment, recursorEnvironment, Environment.insert_replace] using hwf

theorem publishedEnvironment_old {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries source shape mode)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry) :
    shape.publishedEnvironment entries source mode r = some entry :=
  Environment.insert_old h.recursorChecked.fresh (Environment.overlay_old
    (constructorEntries_fresh h.shapeChecked) (Environment.insert_old
      (h.shapeChecked.fresh _ (List.mem_cons_self ..)) hr))

variable {V : Type v} [SetTheory V]

theorem publishedAssignment_realizes {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries source shape mode)
    (hE : entries.WF) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.recursorAssignment constants source mode)
      (shape.publishedEnvironment entries source mode) := by
  have hstage := recursorAssignment_realizes h.shapeChecked hE h.constructors h.recursorChecked h.elimination constants hM
  have hlocal : EntryRealization (shape.recursorAssignment constants source mode) (.member source 1)
      (shape.publishedRecursorEntry source mode) := by
    constructor
    · exact hstage.typeValid (.member source 1) (shape.recursorEntry source mode) (Environment.insert_same ..)
    · exact hstage.member (.member source 1) (shape.recursorEntry source mode) (Environment.insert_same ..)
    · intro body hb; cases hb
    · intro body hb; cases hb
    · intro law hl levels hn env
      obtain ⟨i, ctor, hc, rfl⟩ := recursorLaws_member hl
      exact produced_rule_eq h.shapeChecked hE h.constructors h.recursorChecked h.elimination hM hn hc (h.rules i ctor hc) env
    · intro fact hf levels hn env
      simp only [publishedRecursorEntry, List.mem_cons] at hf
      rcases hf with rfl | hf
      · trivial
      · obtain ⟨i, ctor, hc, hf | hf⟩ := ruleFacts_member hf <;> subst hf
        · exact (h.rules i ctor hc).lhs V _ hstage levels env (Context.valid_nil _ _ _)
        · exact (h.rules i ctor hc).rhs V _ hstage levels env (Context.valid_nil _ _ _)
  have hm := hstage.insert hlocal
  simpa only [publishedEnvironment, recursorEnvironment, Environment.insert_replace] using hm

theorem publishedAssignment_agrees {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedBlock.{u,v} entries source shape mode)
    (constants : Assignment β V) :
    Assignment.AgreesOn entries constants (shape.recursorAssignment constants source mode) :=
  (recursorAssignment_reading h.shapeChecked h.recursorChecked constants).agrees

end Shape

end Ix.Kernel.Certified.Ordinary
