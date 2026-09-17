/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Inductive/Levels.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.VLevel

/-!
The universe layout shared by recursor generation and its computation rules.
Large elimination reserves the first recursor universe for the motive;
constructors and source families receive only the remaining universes.
-/

namespace Ix.Kernel

namespace VLevel

/-- `count` consecutive universe parameters beginning at `offset`. -/
def params' (count offset : Nat) : List VLevel :=
  (List.range count).map fun index => .param (index + offset)

@[simp] theorem params'_length : (params' count offset).length = count := by
  simp [params']

end VLevel

namespace Inductive

/-- Whether a recursor may eliminate into a fresh universe or only into Prop. -/
inductive ElimMode where
  | large
  | small
  deriving DecidableEq, Repr

namespace ElimMode

def ofBool : Bool → ElimMode
  | false => .small
  | true => .large

/-- Universe-slot offset occupied by the large-elimination motive. -/
def offset : ElimMode → Nat
  | .large => 1
  | .small => 0

def recUvars (mode : ElimMode) (sourceUvars : Nat) : Nat :=
  sourceUvars + mode.offset

def motiveLevel : ElimMode → VLevel
  | .large => .param 0
  | .small => .zero

def sourceLevels (mode : ElimMode) (sourceUvars : Nat) : List VLevel :=
  VLevel.params' sourceUvars mode.offset

def recLevels (mode : ElimMode) (sourceUvars : Nat) : List VLevel :=
  VLevel.params (mode.recUvars sourceUvars)

/-- Actual arguments of the source family/constructor at a recursor instance.
The recursor and its rule RHS retain the complete argument list. -/
def sourceArgs (mode : ElimMode) (levels : List α) : List α :=
  levels.drop mode.offset

@[simp] theorem large_offset : ElimMode.large.offset = 1 := rfl
@[simp] theorem small_offset : ElimMode.small.offset = 0 := rfl

@[simp] theorem large_recUvars (sourceUvars : Nat) :
    ElimMode.large.recUvars sourceUvars = sourceUvars + 1 := rfl

@[simp] theorem small_recUvars (sourceUvars : Nat) :
    ElimMode.small.recUvars sourceUvars = sourceUvars := by
  simp [recUvars, offset]

@[simp] theorem small_sourceArgs (levels : List α) :
    ElimMode.small.sourceArgs levels = levels := rfl

@[simp] theorem large_sourceArgs_cons (motive : α) (levels : List α) :
    ElimMode.large.sourceArgs (motive :: levels) = levels := rfl

@[simp] theorem map_sourceArgs (mode : ElimMode) (f : α → β) (levels : List α) :
    (mode.sourceArgs levels).map f = mode.sourceArgs (levels.map f) := by
  simp [sourceArgs]

theorem sourceArgs_length (mode : ElimMode) {levels : List α} {sourceUvars : Nat}
    (h : levels.length = mode.recUvars sourceUvars) :
    (mode.sourceArgs levels).length = sourceUvars := by
  simp [sourceArgs, h, recUvars]

theorem sourceArgs_wf (mode : ElimMode) {levels : List VLevel}
    (h : ∀ level ∈ levels, level.WF U) :
    ∀ level ∈ mode.sourceArgs levels, level.WF U := by
  intro level hl
  exact h level (List.mem_of_mem_drop hl)

theorem sourceLevels_wf (mode : ElimMode) (sourceUvars : Nat) :
    ∀ level ∈ mode.sourceLevels sourceUvars, level.WF (mode.recUvars sourceUvars) := by
  simp [sourceLevels, VLevel.params', VLevel.WF, recUvars]

/-- Generation's symbolic source map selects exactly the source arguments
of a concrete recursor instance. This also covers equal-arity small elimination. -/
theorem sourceLevels_inst (mode : ElimMode) {levels : List VLevel} {sourceUvars : Nat}
    (h : levels.length = mode.recUvars sourceUvars) :
    (mode.sourceLevels sourceUvars).map (VLevel.inst levels) = mode.sourceArgs levels := by
  apply List.ext_get (by simp [sourceLevels, sourceArgs_length mode h])
  intro i hi _
  have hi' : i < sourceUvars := by simpa [sourceLevels] using hi
  have bound : i + mode.offset < levels.length := by
    rw [h, recUvars]
    omega
  simp [sourceLevels, VLevel.params', VLevel.inst, sourceArgs,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Nat.add_comm]

theorem sourceArgs_recLevels (mode : ElimMode) (sourceUvars : Nat) :
    mode.sourceArgs (mode.recLevels sourceUvars) = mode.sourceLevels sourceUvars := by
  have h := sourceLevels_inst mode (sourceUvars := sourceUvars)
    (levels := mode.recLevels sourceUvars)
    (by simp [recLevels])
  rw [← h]
  exact (List.map_congr_left (g := id) fun level hl =>
    VLevel.inst_id (mode.sourceLevels_wf sourceUvars level hl)).trans (List.map_id _)

end ElimMode
end Inductive
end Ix.Kernel
