/-
Adapted for Ix: shared universe semantics and additional proof support.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.VLevelLemmas
import Ix.Theory.Named.Std.Basic

/-! The order, equivalence, and well-formedness lemmas over the shared
`Ix.Theory.VLevel` live in `Ix.Theory.VLevelLemmas`. This module keeps only
the conversion from Lean's named universe parameters, which the named
specification alone uses. -/

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
export Lean (Name)
end Ix.Theory.Named

namespace Ix.Theory.VLevel
open Ix.Theory.Named

variable (ls : List Name) in
def ofLevel : Lean.Level → Option VLevel
  | .zero => return .zero
  | .succ l => return .succ (← ofLevel l)
  | .max l₁ l₂ => return .max (← ofLevel l₁) (← ofLevel l₂)
  | .imax l₁ l₂ => return .imax (← ofLevel l₁) (← ofLevel l₂)
  | .param n =>
    let i := ls.idxOf n
    if i < ls.length then some (.param i) else none
  | .mvar _ => none

theorem WF.of_ofLevel (h : ofLevel ls l = some l') : l'.WF ls.length := by
  induction l generalizing l' with simp [ofLevel, bind] at h
  | zero => cases h; trivial
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact @ih l' h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩
  | param n => exact h.2 ▸ h.1

theorem WF.of_mapM_ofLevel (h : List.mapM (VLevel.ofLevel Us) us = some us')
    (a) (hl : a ∈ us') : VLevel.WF Us.length a := by
  rw [List.mapM_eq_some] at h
  have ⟨_, _, h⟩ := h.forall_exists_r _ hl; exact .of_ofLevel h

end Ix.Theory.VLevel
