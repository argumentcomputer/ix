/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Renaming

/-! The actual deduplication pass validates its proposed transformation.
These proofs require no correctness assumption about partition refinement. -/

namespace Aiur.Bytecode.Eval

theorem validatesRenaming_sound {a b : Toplevel} {rename : FunIdx → FunIdx}
    (valid : validatesRenaming a b (boundedRenaming a rename) = true) :
    RenamedCode a b (boundedRenaming a rename) := by
  simp only [validatesRenaming, Bool.and_eq_true, decide_eq_true_eq] at valid
  have all := Array.all_eq_true.mp valid.2
  simp only [Array.size_range, Array.getElem_range] at all
  have checked (i : Nat) (hi : i < a.functions.size) :
      ∃ hj : boundedRenaming a rename i < b.functions.size,
        a.functions[i].layout = b.functions[boundedRenaming a rename i].layout ∧
        rewriteBlock (boundedRenaming a rename) a.functions[i].body =
          b.functions[boundedRenaming a rename i].body := by
    have h := all i hi
    simp only [dif_pos hi] at h
    split at h
    next hj => exact ⟨hj, by simpa only [Bool.and_eq_true, beq_iff_eq] using h⟩
    next hj => contradiction
  constructor
  · intro i
    constructor
    · intro hi
      obtain ⟨hj, _⟩ := checked i hi
      exact hj
    · intro hj
      by_cases hi : i < a.functions.size
      · exact hi
      · simp only [boundedRenaming, if_neg hi] at hj
        exact Nat.lt_of_lt_of_le hj valid.1
  · intro i hi hj
    obtain ⟨_, _, body⟩ := checked i hi
    exact body
  · intro i hi hj
    obtain ⟨_, layout, _⟩ := checked i hi
    exact congrArg FunctionLayout.inputSize layout

theorem checkedRenaming_preserves_execution (source candidate : Toplevel) (rename : FunIdx → FunIdx)
    (function : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) (result : Array G × IOBuffer) :
    runFunction source function args io fuel = .ok result ↔
      runFunction (checkedRenaming source candidate rename).1
        ((checkedRenaming source candidate rename).2 function)
        args io fuel = .ok result := by
  unfold checkedRenaming
  dsimp only
  split
  next valid => exact runFunction_renamed_iff (validatesRenaming_sound valid) function args io fuel result
  next invalid => rfl

theorem deduplicate_preserves_execution (source : Toplevel)
    (function : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) (result : Array G × IOBuffer) :
    runFunction source function args io fuel = .ok result ↔
      runFunction source.deduplicate.1 (source.deduplicate.2 function)
        args io fuel = .ok result :=
  checkedRenaming_preserves_execution source source.deduplicateCandidate.1 source.deduplicateCandidate.2
    function args io fuel result

end Aiur.Bytecode.Eval
