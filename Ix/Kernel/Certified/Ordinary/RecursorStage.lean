/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RecursorStage.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `RecursorSourceMatches` is removed,
`RecursorFormation` drops `exactSource`, and `checkRecursorType` infers
instead of validating a witness.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.ConstructorStage

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Inductive

universe u v
variable {β : Type u} [DecidableEq β]

namespace Shape

def recursorEntry (shape : Shape β) (source : β) (mode : ElimMode) : ConstantEntry β :=
  ⟨mode.recUvars shape.universes, shape.recursorType source mode, none, [], []⟩

def recursorSource (shape : Shape β) (source : β) (mode : ElimMode) (k : Bool := false) : Const β :=
  .recursor (mode.recUvars shape.universes) shape.parameters.length shape.indices.length 1
    shape.constructors.length (shape.recursorType source mode).erase
    (shape.constructors.zipIdx.map fun (ctor, i) =>
      ⟨ctor.fields.length + ctor.recursive.length, (shape.ruleRhs source mode i ctor).erase⟩)
    k .safe

/-- K metadata is supported for a singleton proposition whose constructor has
no fields. Replacing a major proof still requires a typed proof-irrelevance
certificate at the exact constructor result, followed by the admitted rule. -/
def SupportsK (shape : Shape β) : Prop :=
  shape.level = .zero ∧ ∃ ctor, shape.constructors = [ctor] ∧ ctor.fields = [] ∧ ctor.recursive = []

instance (shape : Shape β) : Decidable shape.SupportsK :=
  match h : shape.constructors with
  | [ctor] => decidable_of_iff (shape.level = .zero ∧ ctor.fields = [] ∧ ctor.recursive = []) (by
      simp [SupportsK, h])
  | [] => .isFalse (by simp [SupportsK, h])
  | _ :: _ :: _ => .isFalse (by simp [SupportsK, h])

def recursorLaws (shape : Shape β) (source : β) (mode : ElimMode) : List (ConstantEquation β) :=
  shape.constructors.zipIdx.map fun (ctor, i) =>
    ⟨shape.ruleLhs source mode i ctor, shape.ruleRhs source mode i ctor⟩

def recursorEnvironment (shape : Shape β) (entries : Environment β) (source : β)
    (mode : ElimMode) : Environment β :=
  (shape.constructorEnvironment entries source).insert (.member source 1) (shape.recursorEntry source mode)

structure RecursorFormation (entries : Environment β) (shape : Shape β)
    (source : β) (mode : ElimMode) : Prop where
  fresh : shape.constructorEnvironment entries source (.member source 1) = none
  closed : EntryClosed (shape.constructorEnvironment entries source) (shape.recursorEntry source mode)
  typing : ∃ l, TypingClaim.{u,v} (shape.constructorEnvironment entries source) []
    (shape.recursorType source mode) (.sort l)

def checkRecursorType (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (source : β) (mode : ElimMode) :
    Option (CheckedClaim.{u} (RecursorFormation.{u,v} entries shape source mode)) :=
  if hfresh : shape.constructorEnvironment entries source (.member source 1) = none then
    if hs : (shape.recursorType source mode).Scope (mode.recUvars shape.universes) 0 then
      if hr : (shape.recursorType source mode).ReferencesIn (shape.constructorEnvironment entries source) then do
        let ⟨l, ht⟩ ← checkSort.{u,v} fuel (shape.constructorEnvironment entries source) []
          (shape.recursorType source mode)
        return ⟨⟨hfresh, ⟨hs, by simp [recursorEntry], hr, by simp [recursorEntry],
          by simp [recursorEntry], by simp [recursorEntry],
          by simp [recursorEntry], by simp [recursorEntry]⟩, l, ht⟩⟩
      else none
    else none
  else none

theorem recursorEnvironment_wf {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode}
    (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF)
    (hC : ConstructorFormation.{u,v} entries shape source)
    (hR : RecursorFormation.{u,v} entries shape source mode) :
    (shape.recursorEnvironment entries source mode).WF :=
  (constructorEnvironment_wf h hE hC).insert hR.closed.typeScope hR.closed.bodyScope
    hR.closed.typeReferences hR.closed.bodyReferences hR.closed.equationScope hR.closed.equationReferences
    hR.closed.factScope hR.closed.factReferences

variable {V : Type v} [SetTheory V]

noncomputable def recursorAssignment (shape : Shape β) (constants : Assignment β V)
    (source : β) (mode : ElimMode) : Assignment β V :=
  (shape.constructorAssignment constants source).insert (.member source 1)
    (fun levels => shape.closedRecursorValue constants levels mode)

end Shape

variable {V : Type v} [SetTheory V]

structure RecursorReading (entries : Environment β) (shape : Shape β) (source : β)
    (mode : ElimMode) (constants reading : Assignment β V) : Prop
    extends ConstructorReading entries shape source constants reading where
  recursor : ∀ levels, levels.length = mode.recUvars shape.universes →
    reading (.member source 1) levels = shape.closedRecursorValue constants levels mode

namespace Shape

theorem recursorAssignment_agreesConstructors {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode}
    (hR : RecursorFormation.{u,v} entries shape source mode) (constants : Assignment β V) :
    Assignment.AgreesOn (shape.constructorEnvironment entries source) (shape.constructorAssignment constants source)
      (shape.recursorAssignment constants source mode) := Assignment.insert_agrees hR.fresh _ _

theorem recursorAssignment_reading {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode} (h : CheckedShape.{u,v} entries source shape)
    (hR : RecursorFormation.{u,v} entries shape source mode) (constants : Assignment β V) :
    RecursorReading entries shape source mode constants (shape.recursorAssignment constants source mode) := by
  have hr := constructorAssignment_reading h constants
  have ha := recursorAssignment_agreesConstructors hR constants
  constructor
  · constructor
    · constructor
      · intro r entry he levels
        exact (ha r entry (Environment.overlay_old (constructorEntries_fresh h)
          (Environment.insert_old (h.fresh _ (List.mem_cons_self ..)) he)) levels).trans (hr.agrees r entry he levels)
      · intro levels hn
        exact (ha _ _ (Environment.overlay_old (constructorEntries_fresh h) (Environment.insert_same ..)) levels).trans
          (hr.family levels hn)
    · intro levels hn i ctor hc
      exact (ha _ (shape.constructorEntry source ctor) (Environment.overlay_new (by
        simp only [constructorEntries, ↓reduceIte, hc, Option.map_some])) levels).trans (hr.constructor levels hn i ctor hc)
  · intro levels _
    exact Assignment.insert_same ..

theorem recursorAssignment_realizes {entries : Environment β} {source : β}
    {shape : Shape β} {mode : ElimMode}
    (h : CheckedShape.{u,v} entries source shape) (hE : entries.WF)
    (hC : ConstructorFormation.{u,v} entries shape source)
    (hR : RecursorFormation.{u,v} entries shape source mode)
    (hmode : ModeEvidence.{u,v} entries shape mode) (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (shape.recursorAssignment constants source mode) (shape.recursorEnvironment entries source mode) := by
  have hr := recursorAssignment_reading h hR constants
  have hbase := (constructorAssignment_realizes h hE hC constants hM).of_agrees
    (constructorEnvironment_wf h hE hC) (recursorAssignment_agreesConstructors hR constants)
  obtain ⟨l, ht⟩ := hR.typing
  apply hbase.insert
  constructor
  · intro levels hn env
    exact (ht V _ hbase levels env (Context.valid_nil _ _ _)).1
  · intro levels hn env
    rw [hr.recursor levels hn]
    have hm := closedRecursorValue_mem_source h hr.toConstructorReading hmode hM hn
    rwa [interp_closed (shape.recursorType source mode) _ levels hR.closed.typeScope (fun _ => empty) env] at hm
  · intro body hb; cases hb
  · intro body hb; cases hb
  · intro law hl; simp only [recursorEntry, List.not_mem_nil] at hl
  · intro fact hf; simp only [recursorEntry, List.not_mem_nil] at hf

end Shape
end Ix.Kernel.Certified.Ordinary
