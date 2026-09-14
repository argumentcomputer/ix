/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Natural.Value

namespace Ix.Theory.Certified.Natural

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def fact (source : β) : ConstantFact β := .natural (.ctor source 0 0) (.ctor source 0 1)
def entry (source : β) : ConstantEntry β := { (shape : Ordinary.Shape β).familyEntry with facts := [fact source] }
def environment (entries : Environment β) (source recursor : β) (mode : Inductive.ElimMode) : Environment β :=
  (shape.publishedEnvironment entries source recursor mode).insert (.member source 0) (entry source)

structure Checked (entries : Environment β) (store : Store β) (pin : ConstRef β)
    (source recursor : β) (mode : Inductive.ElimMode) : Prop where
  block : Ordinary.CheckedBlock.{u,v} entries store source recursor shape mode
  primitive : pin = .member source 0
  references : (fact source).ReferencesIn (shape.publishedEnvironment entries source recursor mode)

/-- Literal support is tied to the profile's selected Nat reference and the
whole ordinary zero/successor source, not to a diagnostic name or marker. -/
def check (fuel : Nat) (entries : Environment β) (store : Store β) (pin : ConstRef β)
    (witness : Ordinary.BlockWitness β) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries store pin witness.source witness.recursor witness.mode)) :=
  if hp : pin = .member witness.source 0 then
    if hs : witness.shape.shape = shape then
      if hr : (fact witness.source).ReferencesIn
          (shape.publishedEnvironment entries witness.source witness.recursor witness.mode) then do
        let block ← Ordinary.checkBlock.{u,v} fuel entries store witness
        return ⟨⟨hs ▸ block.down, hp, hr⟩⟩
      else none
    else none
  else none

theorem check_sound {fuel : Nat} {entries : Environment β} {store : Store β} {pin : ConstRef β}
    {witness : Ordinary.BlockWitness β} {result}
    (_ : check.{u,v} fuel entries store pin witness = some result) :
    Checked.{u,v} entries store pin witness.source witness.recursor witness.mode := result.down

end Ix.Theory.Certified.Natural
