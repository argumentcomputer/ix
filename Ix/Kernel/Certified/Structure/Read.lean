/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Structure.Syntax
import Ix.Kernel.Certified.Ordinary.Read

/-! # Reading a structure

From an ordinary reading whose shape is structure-like (no indices, one
constructor, no recursive fields), the description with each field's sort
inferred. As with the ordinary reader, nothing depends on it: the checker
compares `Description.ordinary` with the read shape and checks every field. -/

namespace Ix.Kernel.Certified.Structure

open Model Ordinary

universe u v

variable {β : Type u} [DecidableEq β]

/-- Field sorts by inference, each in the context of its predecessors. -/
def readFields (fuel : Nat) (entries : Environment β) :
    Context β → List (AExpr β) → Option (List (Field β))
  | _, [] => some []
  | Γ, D :: rest => do
    let ⟨l, _⟩ ← checkSort.{u,v} fuel entries Γ D
    let fields ← readFields fuel entries (Γ.push D) rest
    return ⟨D, l⟩ :: fields

/-- The description of a structure-like reading. -/
def readDescription (fuel : Nat) (entries : Environment β) (reading : Ordinary.Reading β) :
    Option (Description β) :=
  match reading.shape with
  | ⟨universes, parameters, [], level, [⟨domains, [], []⟩]⟩ => do
    let fields ← readFields.{u,v} fuel entries (Telescope.context [] parameters) domains
    return ⟨universes, parameters, fields, level⟩
  | _ => none

end Ix.Kernel.Certified.Structure
