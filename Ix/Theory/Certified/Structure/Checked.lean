/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Structure.Computation
import Ix.Theory.Certified.Signature

namespace Ix.Theory.Certified.Structure

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def Description.factEntry (d : Description β) (source : β) : ConstantEntry β :=
  { d.ordinary.familyEntry with facts := d.facts source }

def Description.factEnvironment (d : Description β) (entries : Environment β) (source recursor : β)
    (mode : Inductive.ElimMode) : Environment β :=
  (d.ordinary.publishedEnvironment entries source recursor mode).insert (.member source 0) (d.factEntry source)

/-- Field i may use the already produced equations for earlier fields when
checking its dependent result. Its own equation is absent from this stage. -/
def Description.iotaEnvironment (d : Description β) (entries : Environment β) (source recursor : β)
    (mode : Inductive.ElimMode) (count : Nat) : Environment β :=
  (d.ordinary.publishedEnvironment entries source recursor mode).insert (.member source 0)
    { d.factEntry source with equations := ((d.equations source).drop 1).take count }

structure FactsWitness (β : Type u) where
  description : Description β
  block : Ordinary.BlockWitness β
  fields : List (TypingWitness β)
  domains : List (DomainWitness β)

structure FactsChecked (entries : Environment β) (store : Store β) (d : Description β)
    (source recursor : β) (mode : Inductive.ElimMode) : Prop where
  block : Ordinary.CheckedBlock.{u,v} entries store source recursor d.ordinary mode
  fields : FieldsFormed.{u,v} entries d.level d.ordinary.parameterContext d.fields
  domains : Telescope.Formed.{u,v} (d.ordinary.publishedEnvironment entries source recursor mode) []
    (d.projectionDomains source)
  scope : ∀ fact ∈ d.facts source, fact.Scope d.universes
  references : ∀ fact ∈ d.facts source,
    fact.ReferencesIn (d.ordinary.publishedEnvironment entries source recursor mode)

def checkFacts (fuel : Nat) (entries : Environment β) (store : Store β) (witness : FactsWitness β) :
    Option (CheckedClaim.{u} (FactsChecked.{u,v} entries store witness.description
      witness.block.source witness.block.recursor witness.block.mode)) :=
  let d := witness.description
  let block := witness.block
  if he : block.shape.shape = d.ordinary then
    if hs : ∀ fact ∈ d.facts block.source, fact.Scope d.universes then
      if hr : ∀ fact ∈ d.facts block.source,
          fact.ReferencesIn (d.ordinary.publishedEnvironment entries block.source block.recursor block.mode) then do
        let hb ← Ordinary.checkBlock.{u,v} fuel entries store block
        let hf ← checkFields.{u,v} fuel d.universes entries d.level d.ordinary.parameterContext d.fields witness.fields
        let hd ← verifyTelescope.{u,v} fuel d.universes
          (d.ordinary.publishedEnvironment entries block.source block.recursor block.mode) none []
          (d.projectionDomains block.source) witness.domains
        return ⟨⟨he ▸ hb.down, hf.down, hd.down.1, hs, hr⟩⟩
      else none
    else none
  else none

def Description.etaRule (d : Description β) (source : β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition d.level) (d.projectionDomains source)
    (d.ordinary.familyApp source 1 []), d.etaLhs source, d.etaRhs source⟩

def Description.iotaRule (d : Description β) (source : β) (i : Nat) (field : Field β) : Signature.Rule β :=
  ⟨d.universes, .forallN (zeroCondition field.level) (d.parameters ++ d.constructor.fields)
    (field.domain.liftN (d.fields.length - i)), d.iotaLhs source i field, d.iotaRhs i field⟩

structure Witness (β : Type u) where
  facts : FactsWitness β
  eta : Signature.RuleWitness β
  iota : List (Signature.RuleWitness β)

structure Checked (entries : Environment β) (store : Store β) (d : Description β)
    (source recursor : β) (mode : Inductive.ElimMode) : Prop where
  facts : FactsChecked.{u,v} entries store d source recursor mode
  eta : Signature.RuleFormed.{u,v} (d.factEnvironment entries source recursor mode) (d.etaRule source)
  iota : ∀ field i, (field, i) ∈ d.fields.zipIdx →
    Signature.RuleFormed.{u,v} (d.iotaEnvironment entries source recursor mode i) (d.iotaRule source i field)

def checkIota (fuel : Nat) (entries : Environment β) (d : Description β) (source recursor : β)
    (mode : Inductive.ElimMode) :
    (fields : List (Field β × Nat)) → List (Signature.RuleWitness β) →
      Option (CheckedClaim.{u} (∀ field i, (field, i) ∈ fields →
        Signature.RuleFormed.{u,v} (d.iotaEnvironment entries source recursor mode i) (d.iotaRule source i field)))
  | [], [] => some ⟨by simp⟩
  | (field, i) :: fields, witness :: witnesses => do
    let ht ← Signature.checkRule.{u,v} fuel (d.iotaEnvironment entries source recursor mode i) (d.iotaRule source i field) witness
    let rest ← checkIota fuel entries d source recursor mode fields witnesses
    return ⟨by
      intro field' j hj
      rcases List.mem_cons.mp hj with he | hj
      · cases he; exact ht.down
      · exact rest.down field' j hj⟩
  | _, _ => none

def check (fuel : Nat) (entries : Environment β) (store : Store β) (witness : Witness β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries store witness.facts.description
      witness.facts.block.source witness.facts.block.recursor witness.facts.block.mode)) := do
  let facts ← checkFacts.{u,v} fuel entries store witness.facts
  let d := witness.facts.description
  let block := witness.facts.block
  let stage := d.factEnvironment entries block.source block.recursor block.mode
  let eta ← Signature.checkRule.{u,v} fuel stage (d.etaRule block.source) witness.eta
  let iota ← checkIota.{u,v} fuel entries d block.source block.recursor block.mode d.fields.zipIdx witness.iota
  return ⟨⟨facts.down, eta.down, iota.down⟩⟩

theorem check_sound {fuel : Nat} {entries : Environment β} {store : Store β} {witness : Witness β}
    {result} (_ : check.{u,v} fuel entries store witness = some result) :
    Checked.{u,v} entries store witness.facts.description witness.facts.block.source
      witness.facts.block.recursor witness.facts.block.mode := result.down

end Ix.Theory.Certified.Structure
