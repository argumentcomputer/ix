/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Checker
import Ix.Theory.Certified.Prelude
import Ix.Theory.Certified.Ordinary.Checked
import Ix.Theory.Certified.Standard.Checked
import Ix.Theory.Certified.Quotient.Publish
import Ix.Theory.Certified.Structure.Publish
import Ix.Theory.Certified.Natural.Publish
import Ix.Theory.Certified.Modeled.Source

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def DefinitionReading.entry (reading : DefinitionReading β) : ConstantEntry β :=
  ⟨reading.universes, reading.type, some reading.body, [], []⟩

/-- Every published dependency has an exact source declaration in the input
store. The two exceptional forms are the completely pinned primitives. -/
def EntrySource (signature : PrimitiveSignature β) (store : Store β)
    (r : ConstRef β) (entry : ConstantEntry β) : Prop :=
  (r = signature.falseType ∧ entry = PrimitiveSignature.falseEntry ∧
    store.lookup r = some PrimitiveSignature.falseDeclaration) ∨
  (r = signature.falseElim ∧ entry = signature.falseElimEntry ∧
    store.lookup r = some signature.falseElimDeclaration) ∨
  (∃ (kind : DefKind) (body : AExpr β), entry.body = some body ∧
    entry.equations = [] ∧ entry.facts = [] ∧
    store.lookup r = some (.defn entry.universes kind entry.type.erase body.erase .safe)) ∨
  Ordinary.EntrySource store r entry ∨ Standard.EntrySource store r entry ∨
    Quotient.EntrySource store r entry ∨ Structure.EntrySource store r entry ∨
      Natural.EntrySource signature.natType store r entry ∨ Modeled.EntrySource store r entry

/-- An interface may be an explicit conditional frontier. Scope and reference
closure are checked here; existence of a realization is a separate obligation. -/
structure CheckedInterface (signature : PrimitiveSignature β) where
  entries : Environment β
  wf : entries.WF
  present : signature.Present entries

/-- The model field is produced by the initialization and admission functions,
starting with the fixed prelude and extending it with checked bodies. -/
structure AdmittedEnvironment (signature : PrimitiveSignature β) (store : Store β) where
  entries : Environment β
  wf : entries.WF
  present : signature.Present entries
  source : ∀ r entry, entries r = some entry → EntrySource signature store r entry
  model : ∀ (V : Type v) [SetTheory V], ∃ constants : Assignment β V,
    signature.Compatible entries constants

def AdmittedEnvironment.interface {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) : CheckedInterface signature :=
  ⟨state.entries, state.wf, state.present⟩

/-- An extension preserves each previously selected interpretation. -/
structure Extends (signature : PrimitiveSignature β) (entries entries' : Environment β) : Prop where
  lookup : ∀ r entry, entries r = some entry → entries' r = some entry
  models : ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    signature.Compatible entries constants → ∃ constants' : Assignment β V,
      signature.Compatible entries' constants' ∧ Assignment.AgreesOn entries constants constants'

omit [DecidableEq β] in
theorem Extends.refl (signature : PrimitiveSignature β) (entries : Environment β) :
    Extends.{u,v} signature entries entries :=
  ⟨fun _ _ h => h, fun _ _ constants h => ⟨constants, h, fun _ _ _ _ => rfl⟩⟩

omit [DecidableEq β] in
theorem Extends.trans {signature : PrimitiveSignature β} {a b c : Environment β}
    (hab : Extends.{u,v} signature a b) (hbc : Extends.{u,v} signature b c) :
    Extends.{u,v} signature a c := by
  refine ⟨fun r entry h => hbc.lookup r entry (hab.lookup r entry h), ?_⟩
  intro V _ constants hM
  obtain ⟨constants', hM', hagree⟩ := hab.models V constants hM
  obtain ⟨constants'', hM'', hagree'⟩ := hbc.models V constants' hM'
  refine ⟨constants'', hM'', ?_⟩
  intro r entry hr levels
  exact (hagree' r entry (hab.lookup r entry hr) levels).trans (hagree r entry hr levels)

/-- Admission checks and their universal extension theorem do not require a
model of a deferred frontier. Every newly published entry has a checked source;
an existing frontier entry retains its exact interface. -/
structure CheckedExtension (signature : PrimitiveSignature β) (store : Store β)
    (input : CheckedInterface signature) where
  result : CheckedInterface signature
  extension : Extends.{u,v} signature input.entries result.entries
  source : ∀ r entry, result.entries r = some entry →
    input.entries r = some entry ∨ EntrySource signature store r entry

def CheckedExtension.refl {signature : PrimitiveSignature β} {store : Store β}
    (input : CheckedInterface signature) : CheckedExtension.{u,v} signature store input :=
  ⟨input, Extends.refl signature input.entries, fun _ _ h => Or.inl h⟩

def CheckedExtension.trans {signature : PrimitiveSignature β} {store : Store β}
    {input : CheckedInterface signature} (first : CheckedExtension.{u,v} signature store input)
    (second : CheckedExtension.{u,v} signature store first.result) :
    CheckedExtension.{u,v} signature store input where
  result := second.result
  extension := first.extension.trans second.extension
  source := by
    intro r entry h
    rcases second.source r entry h with old | new
    · exact first.source r entry old
    · exact Or.inr new

/-- A closed admission uses the same checked extension and supplies the model
and source provenance constructed by its earlier successful admissions. -/
def CheckedExtension.admit {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store)
    (checked : CheckedExtension.{u,v} signature store state.interface) :
    { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } :=
  ⟨{
    entries := checked.result.entries
    wf := checked.result.wf
    present := checked.result.present
    source := by
      intro r entry h
      rcases checked.source r entry h with old | new
      · exact state.source r entry old
      · exact new
    model := by
      intro V _
      obtain ⟨constants, hM⟩ := state.model V
      obtain ⟨constants', hM', _⟩ := checked.extension.models V constants hM
      exact ⟨constants', hM'⟩
  }, checked.extension⟩

def initialize? (signature : PrimitiveSignature β) (store : Store β) :
    Option (AdmittedEnvironment.{u,v} signature store) :=
  if h : signature.validate store = true then
    some {
      entries := signature.environment
      wf := signature.environment_wf
      present := signature.present_environment
      source := by
        intro r entry hr
        have hv := (signature.validate_iff store).mp h
        unfold PrimitiveSignature.environment at hr
        split at hr
        next he =>
          subst r
          cases Option.some.inj hr
          exact Or.inl ⟨rfl, rfl, hv.1⟩
        next =>
          split at hr
          next he =>
            subst r
            cases Option.some.inj hr
            exact Or.inr (Or.inl ⟨rfl, rfl, hv.2⟩)
          next => contradiction
      model := fun V _ => ⟨signature.assignment, signature.compatible_assignment⟩
    }
  else none

structure DefinitionWitness (β : Type u) where
  ref : ConstRef β
  typeAnnotations : AnnotationTree
  bodyAnnotations : AnnotationTree
  typeLevel : VLevel
  typeWitness : TypingWitness β
  bodyWitness : TypingWitness β

def checkDefinitionExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : DefinitionWitness β) :
    Option (CheckedExtension.{u,v} signature store state) :=
  match hs : store.lookup witness.ref with
  | none => none
  | some source => do
    let reading : { reading : DefinitionReading β // reading.erase = source } ←
      readDefinition? source witness.typeAnnotations witness.bodyAnnotations
    let entry := reading.val.entry
    if fresh : state.entries witness.ref = none then
      if hTr : reading.val.type.ReferencesIn state.entries then
        if hBr : reading.val.body.ReferencesIn state.entries then do
          let hT ← verifyType.{u,v} fuel reading.val.universes state.entries []
            reading.val.type (.sort witness.typeLevel) witness.typeWitness
          let hB ← verifyType.{u,v} fuel reading.val.universes state.entries []
            reading.val.body reading.val.type witness.bodyWitness
          have extension : Extends.{u,v} signature state.entries
              (state.entries.insert witness.ref entry) := by
            refine ⟨fun _ _ h => Environment.insert_old fresh h, ?_⟩
            intro V _ constants hM
            obtain ⟨constants', hM', hagree⟩ := extend_definition (entry := entry) state.wf fresh rfl rfl rfl
              reading.val.bodyScope hTr hBr hT.down hB.down constants hM.realizes
            exact ⟨constants', hM.extend signature state.present hM' hagree, hagree⟩
          let result : CheckedInterface signature := {
            entries := state.entries.insert witness.ref entry
            wf := state.wf.insert reading.val.typeScope
              (fun body hb => by cases Option.some.inj hb; exact reading.val.bodyScope)
              hTr (fun body hb => by cases Option.some.inj hb; exact hBr)
              (by simp [entry, DefinitionReading.entry])
              (by simp [entry, DefinitionReading.entry])
              (by simp [entry, DefinitionReading.entry])
              (by simp [entry, DefinitionReading.entry])
            present := state.present.insert signature fresh
          }
          return {
            result, extension
            source := by
              intro r old h
              dsimp only [result] at h
              unfold Environment.insert at h
              split at h
              next hr =>
                subst r
                cases Option.some.inj h
                refine Or.inr (Or.inr (Or.inr (Or.inl ⟨reading.val.kind, reading.val.body, rfl, rfl, rfl, ?_⟩)))
                exact hs.trans (congrArg some reading.property.symm)
              next => exact Or.inl h
          }
        else none
      else none
    else none

def admitDefinition? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : DefinitionWitness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkDefinitionExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

def admitDefinitions? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) :
    List (DefinitionWitness β) →
      Option { result : AdmittedEnvironment.{u,v} signature store //
        Extends.{u,v} signature state.entries result.entries }
  | [] => some ⟨state, Extends.refl signature state.entries⟩
  | witness :: rest => do
    let step ← admitDefinition? fuel state witness
    let rest ← admitDefinitions? fuel step.val rest
    return ⟨rest.val, step.property.trans rest.property⟩

theorem admitDefinition?_extends {fuel : Nat} {signature : PrimitiveSignature β}
    {store : Store β} {state : AdmittedEnvironment.{u,v} signature store}
    {witness : DefinitionWitness β} {result}
    (_ : admitDefinition? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
