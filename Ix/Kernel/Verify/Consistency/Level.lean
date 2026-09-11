/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Level
import Ix.Theory.VLevel

open Ix.Theory (VLevel)

/-!
# Kernel universe decisions in the consistency model

The normalization proof and the set-theoretic model share `Theory.VLevel`.
This module states the production decisions directly in that model. The
comparison hypotheses are faithfulness of the compared addresses and bounds
excluding UInt64 overflow.
-/

namespace Ix.Kernel.Consistency

variable {m : Mode}

/-- Read a kernel universe structurally, without consulting its cached hash. -/
def readLevel : KUniv m → Theory.VLevel
  | .zero _ => .zero
  | .succ u _ => .succ (readLevel u)
  | .max a b _ => .max (readLevel a) (readLevel b)
  | .imax a b _ => .imax (readLevel a) (readLevel b)
  | .param index _ _ => .param index.toNat

/-- Display metadata cannot change a universe's model reading. -/
@[simp] theorem readLevel_eraseMeta (u : KUniv m) :
    readLevel u.eraseMeta = readLevel u := by
  induction u <;> simp_all [KUniv.eraseMeta, readLevel]

/-- The structural reader and the normalization proof use the same syntax. -/
theorem readLevel_eq (u : KUniv m) : readLevel u = u.toVLevel := by
  induction u <;> simp_all [readLevel, KUniv.toVLevel]

/-- The production successor constructor preserves the semantic successor. -/
@[simp] theorem readLevel_mkSucc (u : KUniv m) :
    readLevel (KUniv.mkSucc u) = .succ (readLevel u) := by
  rw [readLevel_eq, KUniv.toVLevel_mkSucc, ← readLevel_eq]

/-- The structural reader preserves universe evaluation. -/
theorem readLevel_eval (levels : List Nat) (u : KUniv m) :
    (readLevel u).eval levels = u.toVLevel.eval levels := by
  rw [readLevel_eq]

/-- Reading preserves the existing checker's universe-parameter scope. -/
theorem readLevel_wf (n : Nat) (u : KUniv m) :
    (readLevel u).WF n ↔ u.toVLevel.WF n := by
  rw [readLevel_eq]

/-- Successful production universe equality is equality in the new model. -/
theorem univEq_sound {u v : KUniv m} (faithful : u.AddrFaithful v)
    (boundU : u.size < UInt64.size) (boundV : v.size < UInt64.size)
    (accepted : Kernel.univEq u v = true) : readLevel u ≈ readLevel v := by
  apply Theory.VLevel.equiv_def.mpr
  intro levels
  rw [readLevel_eval, readLevel_eval]
  exact Ix.Theory.VLevel.equiv_def.mp
    (Kernel.univEq_sound faithful boundU boundV accepted) levels

/-- Successful production universe comparison is inclusion in the new model. -/
theorem univGeq_sound {u v : KUniv m} (faithful : u.AddrFaithful v)
    (boundU : u.size < UInt64.size) (boundV : v.size < UInt64.size)
    (accepted : Kernel.univGeq u v = true) : readLevel v ≤ readLevel u := by
  intro levels
  rw [readLevel_eval, readLevel_eval]
  exact Kernel.univGeq_sound faithful boundU boundV accepted levels

end Ix.Kernel.Consistency
