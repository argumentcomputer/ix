/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Structure/Checked.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K3: facts are checked and realized over either the constructor stage or
the stage with a recursor at its explicit reference.
K2: the input store, its exact-source facts, and the witnesses are removed;
the recursor is member 1 of the family's block; `checkFacts` and `check` take
the ordinary block's proof from the caller and infer with `Ix.Kernel.Infer`;
the check-time family entry carries the `structure` arity fact; the published
entry and environment are defined here, and every rule is typed in the
published environment instead of a staged one.
P01: bounded validators return `Search`, preserving nested exhaustion and
unresolved search; direct validation failures carry specific diagnostics.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Structure.Computation
import Ix.Kernel.Certified.Signature

import Ix.Kernel.Certified.Ordinary.Stage

namespace Ix.Kernel.Certified.Structure

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def Description.factEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.ordinary.familyEntry with facts := d.structureFact :: d.facts source }

def Description.factEnvironment (d : Description β) (entries : Environment β) (source : β)
    (stage : Ordinary.Stage β) : Environment β :=
  (stage.environment d.ordinary entries source).insert (.member source 0) (d.factEntry source)

/-- The family entry as published: the arities, the projection facts, and the
eta and iota equations. Rules are typed in the published environment. -/
def Description.publishedEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.factEntry source with equations := d.equations source }

def Description.publishedEnvironment (d : Description β) (entries : Environment β) (source : β)
    (stage : Ordinary.Stage β) : Environment β :=
  (stage.environment d.ordinary entries source).insert (.member source 0) (d.publishedEntry source)

structure FactsChecked (entries : Environment β) (d : Description β)
    (source : β) (stage : Ordinary.Stage β) : Prop where
  block : stage.Checked.{u,v} entries source d.ordinary
  fields : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields
  domains : Telescope.Formed.{u,v} (stage.environment d.ordinary entries source) []
    (d.projectionDomains source)
  scope : ∀ fact ∈ d.facts source, fact.Scope d.universes
  references : ∀ fact ∈ d.facts source,
    fact.ReferencesIn (stage.environment d.ordinary entries source)

/-- The ordinary block is already checked by the caller. -/
def checkFacts (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (stage : Ordinary.Stage β) (hb : stage.Checked.{u,v} entries source d.ordinary) :
    Search (CheckedClaim.{u} (FactsChecked.{u,v} entries d source stage)) :=
  if hs : ∀ fact ∈ d.facts source, fact.Scope d.universes then
    if hr : ∀ fact ∈ d.facts source,
        fact.ReferencesIn (stage.environment d.ordinary entries source) then do
      let hf ← checkFields.{u,v} fuel entries d.level d.ordinary.parameterContext d.fields
      let hd ← checkTelescope.{u,v} fuel (stage.environment d.ordinary entries source) none []
        (d.projectionDomains source)
      return ⟨⟨hb, hf.down, hd.down.1, hs, hr⟩⟩
    else .error (.malformed "structure fact references an uninstalled constant")
  else .error (.malformed "structure fact is not closed")

def Description.etaRule (d : Description β) (source : β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition d.level) (d.projectionDomains source)
    (d.ordinary.familyApp source 1 []), d.etaLhs source, d.etaRhs source⟩

def Description.iotaRule (d : Description β) (source : β) (i : Nat) (field : Field β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition field.level) (d.parameters ++ d.constructor.fields)
    (field.domain.liftN (d.fields.length - i)), d.iotaLhs source i field, d.iotaRhs i field⟩

structure Checked (entries : Environment β) (d : Description β)
    (source : β) (stage : Ordinary.Stage β) : Prop where
  facts : FactsChecked.{u,v} entries d source stage
  eta : Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source stage) (d.etaRule source)
  iota : ∀ field i, (field, i) ∈ d.fields.zipIdx →
    Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source stage) (d.iotaRule source i field)

def checkIota (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (stage : Ordinary.Stage β) :
    (fields : List (Field β × Nat)) →
      Search (CheckedClaim.{u} (∀ field i, (field, i) ∈ fields →
        Signature.RuleFormed.{u,v} (d.publishedEnvironment entries source stage) (d.iotaRule source i field)))
  | [] => .ok ⟨by simp⟩
  | (field, i) :: fields => do
    let ht ← Signature.checkRule.{u,v} fuel (d.publishedEnvironment entries source stage) (d.iotaRule source i field)
    let rest ← checkIota fuel entries d source stage fields
    return ⟨by
      intro field' j hj
      rcases List.mem_cons.mp hj with he | hj
      · cases he; exact ht.down
      · exact rest.down field' j hj⟩

def check (fuel : Nat) (entries : Environment β) (d : Description β) (source : β)
    (stage : Ordinary.Stage β) (hb : stage.Checked.{u,v} entries source d.ordinary) :
    Search (CheckedClaim.{u} (Checked.{u,v} entries d source stage)) := do
  let facts ← checkFacts.{u,v} fuel entries d source stage hb
  let eta ← Signature.checkRule.{u,v} fuel (d.publishedEnvironment entries source stage) (d.etaRule source)
  let iota ← checkIota.{u,v} fuel entries d source stage d.fields.zipIdx
  return ⟨⟨facts.down, eta.down, iota.down⟩⟩

theorem check_sound {fuel : Nat} {entries : Environment β} {d : Description β} {source : β}
    {stage : Ordinary.Stage β} {hb : stage.Checked.{u,v} entries source d.ordinary}
    {result} (_ : check.{u,v} fuel entries d source stage hb = .ok result) :
    Checked.{u,v} entries d source stage := result.down

end Ix.Kernel.Certified.Structure
