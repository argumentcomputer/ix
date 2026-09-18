/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Natural/Checked.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store, its exact-source facts, the witness, and the pin parameter
are removed (the block is recognized by its shape); the recursor is member 1 of
the family's block; `check` takes the ordinary block's proof from the caller.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Natural.Value

namespace Ix.Kernel.Certified.Natural

open Model

universe u v
variable {β : Type u} [DecidableEq β]

def fact (source : β) : ConstantFact β := .natural (.ctor source 0 0) (.ctor source 0 1)
def entry (source : β) : ConstantEntry β :=
  { (shape : Ordinary.Shape β).familyEntry with facts := [fact source] }
def environment (entries : Environment β) (source : β) (mode : Inductive.ElimMode) : Environment β :=
  (shape.publishedEnvironment entries source mode).insert (.member source 0) (entry source)

/-- Literal support is tied to the whole ordinary zero/successor block, not to
a name or a marker. -/
structure Checked (entries : Environment β) (source : β) (mode : Inductive.ElimMode) : Prop where
  block : Ordinary.CheckedBlock.{u,v} entries source shape mode
  references : (fact source).ReferencesIn (shape.publishedEnvironment entries source mode)

def check (entries : Environment β) (source : β) (mode : Inductive.ElimMode)
    (hb : Ordinary.CheckedBlock.{u,v} entries source shape mode) :
    Option (CheckedClaim.{u} (Checked.{u,v} entries source mode)) :=
  if hr : (fact source).ReferencesIn (shape.publishedEnvironment entries source mode) then
    some ⟨⟨hb, hr⟩⟩
  else none

end Ix.Kernel.Certified.Natural
