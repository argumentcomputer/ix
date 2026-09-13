/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.SetModel.TaggedSum

namespace Ix.Theory.Model

open SetTheory SetTheory.Tower

universe u
variable {V : Type u} [SetTheory V]

/-- The ordinary container stores a tagged tuple as the first component of
its node. These total destructors also fix the proof point. Ownership and
field legality are obligations of the certified projection rule. -/
noncomputable def projectValue (field : Nat) (value : V) : V :=
  projS field (ssnd (sfst value))

theorem projectValue_pt (field : Nat) : projectValue field (pt : V) = pt := by
  simp only [projectValue, sfst_pt, ssnd_pt, projS_pt]

theorem projectValue_node (field tag : Nat) (fields : List V) (branches : V) :
    projectValue field (spair (inj tag (mkTower fields)) branches) = projS field (mkTower fields) := by
  simp only [projectValue, sfst_spair, ssnd_inj]

namespace Numeral

noncomputable def zero : V := spair (inj 0 pt) empty
noncomputable def succ (n : V) : V := spair (inj 1 pt) (graph (fun _ => n) (sing (inj 0 pt)))
noncomputable def value : Nat → V
  | 0 => zero
  | n + 1 => succ (value n)

end Numeral

end Ix.Theory.Model
