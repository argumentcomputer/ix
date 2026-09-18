/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Basis/Equality.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: split from `Basis.Equality`: the shape of `Eq` and the interface of a
checked block, with the input store removed and the recursor at member 1 of
the family's block.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Basis.Equality
import Ix.Kernel.Certified.Ordinary.Checked

namespace Ix.Kernel.Certified.Basis.Equality

open Model

universe u v
variable {β : Type u}

def shape : Ordinary.Shape β :=
  ⟨1, [.sort (.param 0), .bvar 0], [.bvar 1], .zero, [⟨[], [], [.bvar 0]⟩]⟩

theorem shape_type : (shape : Ordinary.Shape β).type = type := rfl

theorem shape_reflType (source : β) :
    (⟨[], [], [.bvar 0]⟩ : Ordinary.Constructor β).type shape source =
      reflType (.member source 0) := rfl

theorem shape_recType (source : β) : shape.recursorType source .large =
    recType (.member source 0) (.ctor source 0 0) := rfl

theorem Interface.of_checked [DecidableEq β] {entries : Environment β} {source : β}
    (h : Ordinary.CheckedBlock.{u,v} entries source shape .large) :
    Interface (shape.publishedEnvironment entries source .large)
      (.member source 0) (.ctor source 0 0) (.member source 1) := by
  constructor
  · refine ⟨shape.familyEntry, ?_, rfl, shape_type⟩
    exact Environment.insert_old h.recursorChecked.fresh
      (Environment.overlay_old (Ordinary.Shape.constructorEntries_fresh h.shapeChecked)
        (Environment.insert_same ..))
  · refine ⟨shape.constructorEntry source ⟨[], [], [.bvar 0]⟩, ?_, rfl, shape_reflType source⟩
    apply Environment.insert_old h.recursorChecked.fresh
    apply Environment.overlay_new
    simp [Ordinary.Shape.constructorEntries, shape]
  · exact ⟨shape.publishedRecursorEntry source .large,
      Environment.insert_same .., rfl, shape_recType source⟩

end Ix.Kernel.Certified.Basis.Equality
