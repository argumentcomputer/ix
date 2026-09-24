/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Structure/Checked.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store, its exact-source facts, and the witnesses are removed;
the recursor is member 1 of the family's block; `checkFacts` and `check` take
the ordinary block's proof from the caller and infer with `Ix.Kernel.Infer`;
the check-time family entry carries the `structure` arity fact; the published
entry and environment are defined here, and every rule is typed in the
published environment instead of a staged one.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Structure.Computation
import Ix.Kernel.Certified.Signature

namespace Ix.Kernel.Certified.Structure

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def Description.factEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.ordinary.familyEntry with facts := d.structureFact :: d.facts source }

def Description.factEnvironment (d : Description β) (entries : Environment β) (source : β)
    (mode : Inductive.ElimMode) : Environment β :=
  (d.ordinary.publishedEnvironment entries source mode).insert (.member source 0) (d.factEntry source)

/-- The family entry as published: the arities, the projection facts, and the
eta and iota equations. Rules are typed in the published environment. -/
def Description.publishedEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.factEntry source with equations := d.equations source }

def Description.publishedEnvironment (d : Description β) (entries : Environment β) (source : β)
    (mode : Inductive.ElimMode) : Environment β :=
  (d.ordinary.publishedEnvironment entries source mode).insert (.member source 0) (d.publishedEntry source)

structure FactsChecked (entries : Environment β) (d : Description β)
    (source : β) (mode : Inductive.ElimMode) : Prop where
  block : Ordinary.CheckedBlock.{u,v} entries source d.ordinary mode
  fields : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields
  domains : Telescope.Formed.{u,v} (d.ordinary.publishedEnvironment entries source mode) []
    (d.projectionDomains source)
  scope : ∀ fact ∈ d.facts source, fact.Scope d.universes
  references : ∀ fact ∈ d.facts source,
    fact.ReferencesIn (d.ordinary.publishedEnvironment entries source mode)

/-- The ordinary block is already checked by the caller. -/
def checkFacts (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (mode : Inductive.ElimMode) (hb : Ordinary.CheckedBlock.{u,v} entries source d.ordinary mode) :
    Option (CheckedClaim.{u} (FactsChecked.{u,v} entries d source mode)) :=
  if hs : ∀ fact ∈ d.facts source, fact.Scope d.universes then
    if hr : ∀ fact ∈ d.facts source,
        fact.ReferencesIn (d.ordinary.publishedEnvironment entries source mode) then do
      let hf ← checkFields.{u,v} fuel entries d.level d.ordinary.parameterContext d.fields
      let hd ← checkTelescope.{u,v} fuel (d.ordinary.publishedEnvironment entries source mode) none []
        (d.projectionDomains source)
      return ⟨⟨hb, hf.down, hd.down.1, hs, hr⟩⟩
    else none
  else none

def Description.etaRule (d : Description β) (source : β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition d.level) (d.projectionDomains source)
    (d.ordinary.familyApp source 1 []), d.etaLhs source, d.etaRhs source⟩

def Description.iotaRule (d : Description β) (source : β) (i : Nat) (field : Field β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition field.level) (d.parameters ++ d.constructor.fields)
    (field.domain.liftN (d.fields.length - i)), d.iotaLhs source i field, d.iotaRhs i field⟩

structure Checked (entries : Environment β) (d : Description β)
    (source : β) (mode : Inductive.ElimMode) : Prop where
  facts : FactsChecked.{u,v} entries d source mode
  eta : Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source mode) (d.etaRule source)
  iota : ∀ field i, (field, i) ∈ d.fields.zipIdx →
    Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source mode) (d.iotaRule source i field)

def checkIota (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (mode : Inductive.ElimMode) :
    (fields : List (Field β × Nat)) →
      Option (CheckedClaim.{u} (∀ field i, (field, i) ∈ fields →
        Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source mode) (d.iotaRule source i field)))
  | [] => some ⟨by simp⟩
  | (field, i) :: fields => do
    let ht ← Signature.checkRule.{u,v} fuel (d.publishedEnvironment entries source mode) (d.iotaRule source i field)
    let rest ← checkIota fuel entries d source mode fields
    return ⟨by
      intro field' j hj
      rcases List.mem_cons.mp hj with he | hj
      · cases he; exact ht.down
      · exact rest.down field' j hj⟩

def check (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (mode : Inductive.ElimMode) (hb : Ordinary.CheckedBlock.{u,v} entries source d.ordinary mode) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries d source mode)) := do
  let facts ← checkFacts.{u,v} fuel entries d source mode hb
  let eta ← Signature.checkRule.{u,v} fuel (d.publishedEnvironment entries source mode) (d.etaRule source)
  let iota ← checkIota.{u,v} fuel entries d source mode d.fields.zipIdx
  return ⟨⟨facts.down, eta.down, iota.down⟩⟩

theorem check_sound {fuel : Nat} {entries : Environment β} {d : Description β} {source : β}
    {mode : Inductive.ElimMode} {hb : Ordinary.CheckedBlock.{u,v} entries source d.ordinary mode}
    {result} (_ : check.{u,v} fuel entries d source mode hb = some result) :
    Checked.{u,v} entries d source mode := result.down

end Ix.Kernel.Certified.Structure
