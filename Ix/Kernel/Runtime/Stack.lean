/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Runtime.Expr
import Ix.Kernel.Model.Context

/-! # The binder stack and its view as a model context (S1)

A `Stack` holds the types of the free variables, outermost first: entry `k`
is the type of `fvar k`, a bvar-closed runtime term that mentions only the
levels below `k` (`Stack.WF`). Pushing is O(1) and shifts nothing; the model
context the claims are stated at is its `view`, which pushes each entry,
read at its own depth, with `Context.push`
(`view_push`, `Ix.Kernel.Runtime.Close`).

## Stamps: weakening-only reuse

A claim made at a stack of depth `d_e` holds at every stack that extends it,
by weakening (`TypingClaim.weaken`), and at no other: a claim under an
uninhabited binder is vacuous, so it does not survive leaving that binder,
and a sibling binder's claims are not claims at this one (review §4 M2).
The stack therefore counts pushes per level (`epochs`, kept across pops),
and a result made at depth `d_e` is stamped `(d_e, epochs[d_e - 1])`. The
stamp is valid while the stack is at least that deep and level `d_e - 1`
has not been pushed again: any pop below `d_e` must be followed by a push at
`d_e - 1` before the depth is reached again, and that push bumps the counter.
`Stamp.valid_sound` proves that along any run of pushes and pops a valid
stamp means the stack below `d_e` is the one it was made at, and
`Stamp.valid_of_reachAbove` that it stays valid while the run never pops
below `d_e`. No free-variable range enters the test. -/

namespace Ix.Kernel.Runtime

open Model

universe u

variable {β : Type u}

/-- Increment the counter of `level`. The array grows with zeros if needed;
a stack only ever bumps the level just past its top, which is at most one
past the end. -/
def bumpEpoch (epochs : Array Nat) (level : Nat) : Array Nat :=
  if h : level < epochs.size then epochs.set level (epochs[level] + 1)
  else (epochs ++ Array.replicate (level - epochs.size) 0).push 1

theorem getD_bumpEpoch_self (epochs : Array Nat) (level : Nat) :
    (bumpEpoch epochs level)[level]?.getD 0 = epochs[level]?.getD 0 + 1 := by
  unfold bumpEpoch
  split
  · rename_i h
    simp [Array.getElem?_eq_getElem h]
  · rename_i h
    have hsize : (epochs ++ Array.replicate (level - epochs.size) 0).size = level := by
      simp only [Array.size_append, Array.size_replicate]
      omega
    have hnone : epochs[level]? = none := Array.getElem?_eq_none (by omega)
    rw [Array.getElem?_push, hsize, hnone]
    simp

theorem getD_bumpEpoch_ne (epochs : Array Nat) {level other : Nat} (hne : other ≠ level) :
    (bumpEpoch epochs level)[other]?.getD 0 = epochs[other]?.getD 0 := by
  unfold bumpEpoch
  split
  · simp [Ne.symm hne]
  · rename_i h
    have hsize : (epochs ++ Array.replicate (level - epochs.size) 0).size = level := by
      simp only [Array.size_append, Array.size_replicate]
      omega
    rw [Array.getElem?_push, hsize]
    simp only [hne, ↓reduceIte]
    rw [Array.getElem?_append]
    split
    · rfl
    · rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega)]
      split <;> rfl

/-- Free-variable types, outermost first, with a push counter per level. -/
structure Stack (β : Type u) where
  entries : Array (RExpr β) := #[]
  /-- `epochs[k]` counts the pushes at level `k` so far; pops keep it. -/
  epochs : Array Nat := #[]

namespace Stack

def empty : Stack β := {}

/-- The depth: the number of variables. -/
def size (s : Stack β) : Nat := s.entries.size

/-- Open a variable at level `s.size` of type `A`. -/
def push (s : Stack β) (A : RExpr β) : Stack β :=
  { entries := s.entries.push A, epochs := bumpEpoch s.epochs s.entries.size }

/-- Close the innermost variable. The push counters are kept. -/
def pop (s : Stack β) : Stack β := { s with entries := s.entries.pop }

/-- The type of `fvar level`, a term at depth `level`. -/
def fvarType? (s : Stack β) (level : Nat) : Option (RExpr β) := s.entries[level]?

/-- The number of pushes at `level` so far. -/
def epochAt (s : Stack β) (level : Nat) : Nat := s.epochs[level]?.getD 0

@[simp] theorem size_push (s : Stack β) (A : RExpr β) : (s.push A).size = s.size + 1 := by
  simp [push, size]

@[simp] theorem size_pop (s : Stack β) : s.pop.size = s.size - 1 := by
  simp [pop, size]

@[simp] theorem toList_push (s : Stack β) (A : RExpr β) :
    (s.push A).entries.toList = s.entries.toList ++ [A] := by
  simp [push]

@[simp] theorem toList_pop (s : Stack β) : s.pop.entries.toList = s.entries.toList.dropLast := by
  simp [pop]

theorem epochAt_push_self (s : Stack β) (A : RExpr β) :
    (s.push A).epochAt s.size = s.epochAt s.size + 1 :=
  getD_bumpEpoch_self s.epochs s.entries.size

theorem epochAt_push_ne (s : Stack β) (A : RExpr β) {level : Nat} (hne : level ≠ s.size) :
    (s.push A).epochAt level = s.epochAt level :=
  getD_bumpEpoch_ne s.epochs hne

@[simp] theorem epochAt_pop (s : Stack β) (level : Nat) : s.pop.epochAt level = s.epochAt level := rfl

/-! ## Well-formedness and the view -/

/-- Entries innermost first: each is bvar-closed and mentions only the levels
of the entries after it in this list. -/
def WFRev : List (RExpr β) → Prop
  | [] => True
  | A :: rest => A.fvarBound ≤ rest.length ∧ A.looseBound = 0 ∧ WFRev rest

/-- Entry `k` is bvar-closed and mentions only the levels below `k`. -/
def WF (s : Stack β) : Prop := WFRev s.entries.toList.reverse

/-- The model context of entries listed innermost first: each is read at its
own depth and pushed. -/
def viewRev : List (RExpr β) → Context β
  | [] => []
  | A :: rest => Context.push (RExpr.close rest.length A) (viewRev rest)

/-- The model context a stack denotes. A specification function: claims at
a stack are stated at its view. -/
def view (s : Stack β) : Context β := viewRev s.entries.toList.reverse

/-! ## Stamps -/

/-- The depth a result was made at and the push count of the level below it. -/
structure Stamp where
  depth : Nat
  epoch : Nat
deriving DecidableEq, Repr

/-- The stamp of a result made at the current depth. -/
def stamp (s : Stack β) : Stamp := ⟨s.size, s.epochAt (s.size - 1)⟩

/-- A stamp is valid at a stack at least as deep whose level `depth - 1` has
not been pushed since the stamp was taken. -/
def Stamp.valid (st : Stamp) (s : Stack β) : Bool :=
  decide (st.depth ≤ s.size) && (st.depth == 0 || s.epochAt (st.depth - 1) == st.epoch)

theorem Stamp.valid_iff {st : Stamp} {s : Stack β} :
    st.valid s = true ↔ st.depth ≤ s.size ∧ (st.depth = 0 ∨ s.epochAt (st.depth - 1) = st.epoch) := by
  simp [Stamp.valid]

theorem stamp_valid_self (s : Stack β) : s.stamp.valid s = true := by
  simp [Stamp.valid_iff, stamp]

/-- The states a run of pushes and pops reaches. -/
inductive Reach : Stack β → Stack β → Prop
  | refl (s : Stack β) : Reach s s
  | push {s s' : Stack β} (A : RExpr β) : Reach s s' → Reach s (s'.push A)
  | pop {s s' : Stack β} : Reach s s' → Reach s s'.pop

/-- The states a run reaches without popping below `depth`. -/
inductive ReachAbove (depth : Nat) : Stack β → Stack β → Prop
  | refl (s : Stack β) : ReachAbove depth s s
  | push {s s' : Stack β} (A : RExpr β) : ReachAbove depth s s' → ReachAbove depth s (s'.push A)
  | pop {s s' : Stack β} : ReachAbove depth s s' → depth < s'.size → ReachAbove depth s s'.pop

private theorem prefix_dropLast {l₁ l₂ : List α} (h : l₁ <+: l₂) (hl : l₁.length < l₂.length) :
    l₁ <+: l₂.dropLast := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := by
    rintro rfl
    simp at hl
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

/-- Along any run, the push count of a level never decreases, and while it is
unchanged the stack is at least as deep as the level only if the stack below
the level's successor is the original one. -/
private theorem reach_epoch {s s' : Stack β} (h : Reach s s') (level : Nat)
    (hlevel : level + 1 = s.size) :
    s.epochAt level ≤ s'.epochAt level ∧
      (s'.epochAt level = s.epochAt level → s.size ≤ s'.size →
        s.entries.toList <+: s'.entries.toList) := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun _ _ => List.prefix_refl _⟩
  | @push s' A _ ih =>
    by_cases hk : level = s'.size
    · subst hk
      have hbump := epochAt_push_self s' A
      refine ⟨by omega, fun heq _ => by omega⟩
    · rw [epochAt_push_ne s' A hk]
      refine ⟨ih.1, fun heq hle => ?_⟩
      have hle' : s.size ≤ s'.size := by
        simp only [size_push] at hle
        omega
      rw [toList_push]
      exact (ih.2 heq hle').trans (List.prefix_append _ _)
  | @pop s' _ ih =>
    rw [epochAt_pop]
    refine ⟨ih.1, fun heq hle => ?_⟩
    simp only [size_pop] at hle
    have hlt : s.size < s'.size := by omega
    rw [toList_pop]
    refine prefix_dropLast (ih.2 heq (by omega)) ?_
    simpa [size] using hlt

/-- A valid stamp means the stack below its depth is the one it was taken at. -/
theorem Stamp.valid_sound {s s' : Stack β} (h : Reach s s') (hv : s.stamp.valid s' = true) :
    s.entries.toList <+: s'.entries.toList := by
  rw [Stamp.valid_iff] at hv
  obtain ⟨hle, hep⟩ := hv
  by_cases hd : s.size = 0
  · have hnil : s.entries.toList = [] :=
      List.eq_nil_of_length_eq_zero (by simpa [size] using hd)
    rw [hnil]
    exact List.nil_prefix
  · have hep : s'.epochAt (s.size - 1) = s.epochAt (s.size - 1) := by
      simpa [stamp, hd] using hep
    exact (reach_epoch h (s.size - 1) (by omega)).2 hep (by simpa [stamp] using hle)

/-- A stamp stays valid while the run does not pop below its depth. -/
theorem Stamp.valid_of_reachAbove {s s' : Stack β} (h : ReachAbove s.size s s') :
    s.stamp.valid s' = true := by
  have key : s.size ≤ s'.size ∧
      (s.size = 0 ∨ s'.epochAt (s.size - 1) = s.epochAt (s.size - 1)) := by
    induction h with
    | refl => exact ⟨Nat.le_refl _, .inr rfl⟩
    | @push s' A _ ih =>
      refine ⟨by simp only [size_push]; omega, ?_⟩
      by_cases hd : s.size = 0
      · exact .inl hd
      · rw [epochAt_push_ne s' A (by omega)]; exact ih.2
    | @pop s' _ hlt ih =>
      exact ⟨by simp only [size_pop]; omega, by rw [epochAt_pop]; exact ih.2⟩
  rw [Stamp.valid_iff]
  refine ⟨key.1, ?_⟩
  simp only [stamp]
  rcases key.2 with hd | he
  · exact .inl hd
  · exact .inr he

end Stack

end Ix.Kernel.Runtime
