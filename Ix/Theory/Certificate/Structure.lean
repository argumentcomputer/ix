/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.OrdinarySource
import Ix.Theory.Certificate.Quotient
import Ix.Theory.Certified.Structure.Publish

namespace Ix.Theory.Certificate.Structure

open Model Certified Certified.Structure

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def description? (block : Certified.Ordinary.BlockWitness β) : Option (Description β) := do
  let shape := block.shape.shape
  let [ctor] := shape.constructors | none
  let [witness] := block.shape.constructors | none
  if ctor.fields.length != witness.fields.length then none else
    let fields := (ctor.fields.zip witness.fields).map fun (domain, witness) => ⟨domain, witness.level⟩
    let d : Description β := ⟨shape.universes, shape.parameters, fields, shape.level⟩
    if d.ordinary = shape ∧ fields.all (checkZeroImplies shape.level ·.level) then some d else none

/-- Recover all structure data from the already source-recovered ordinary
block, then suggest whole typing checks for its dependent projections. -/
def witness? (fuel : Nat) (entries : Environment β) (block : Certified.Ordinary.BlockWitness β) :
    Option (Witness β) := do
  let d ← description? block
  let [ctor] := block.shape.constructors | none
  let domains ← Ordinary.domains? fuel d.universes
    (d.ordinary.publishedEnvironment entries block.source block.recursor block.mode) []
    (d.projectionDomains block.source)
  let facts : FactsWitness β := ⟨d, block, ctor.fields.map DomainWitness.typing, domains⟩
  let stage := d.factEnvironment entries block.source block.recursor block.mode
  let eta ← Quotient.ruleWitness? fuel stage (d.etaRule block.source)
  let iota ← d.fields.zipIdx.mapM fun (field, i) => Quotient.ruleWitness? fuel
    (d.iotaEnvironment entries block.source block.recursor block.mode i) (d.iotaRule block.source i field)
  return ⟨facts, eta, iota⟩

end Ix.Theory.Certificate.Structure
