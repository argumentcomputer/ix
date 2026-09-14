/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupMessages
import Ix.Aiur.Proofs.LocalConstraints

/-!
Selector-weighted messages in the native shared lookup slots and continuation
merges. Adding variable-length messages retains the longer tail; zero padding
recovers the uniquely selected message without a common raw-length premise.

The field-characteristic bound, selector equations, layout's single-writer
property and continuation parent activity remain explicit. These lemmas do
not by themselves reflect the Rust emitter or extract its satisfying rows.
-/

namespace Aiur.AIR

/-- The native argument combiner adds overlapping fields and retains the
longer tail, so messages of different lengths share zero-padded slots. -/
def addMessages : List G → List G → List G
  | [], right => right
  | left, [] => left
  | x :: left, y :: right => (x + y) :: addMessages left right

def scaleMessage (selector : G) (message : List G) : List G :=
  message.map (selector * ·)

def weightedMessage (parts : List (G × List G)) : List G :=
  parts.foldl (fun combined part => addMessages combined (scaleMessage part.1 part.2)) []

theorem addMessages_read (left right : List G) (i : Nat) :
    (addMessages left right)[i]?.getD 0 = left[i]?.getD 0 + right[i]?.getD 0 := by
  induction left generalizing right i with
  | nil => simp only [addMessages, List.getElem?_nil, Option.getD_none, G.zero_add]
  | cons value left ih =>
    cases right with
    | nil => simp only [addMessages, List.getElem?_nil, Option.getD_none, G.add_zero]
    | cons other right =>
      cases i with
      | zero => rfl
      | succ i => exact ih right i

theorem addMessages_length (left right : List G) :
    (addMessages left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => simp only [addMessages, List.length_nil, Nat.zero_max]
  | cons value left ih =>
    cases right with
    | nil => simp only [addMessages, List.length_nil, Nat.max_zero]
    | cons other right => simp only [addMessages, List.length_cons, ih, Nat.add_max_add_right]

theorem scaleMessage_read (selector : G) (message : List G) (i : Nat) :
    (scaleMessage selector message)[i]?.getD 0 = selector * message[i]?.getD 0 := by
  induction message generalizing i with
  | nil => simp only [scaleMessage, List.map_nil, List.getElem?_nil, Option.getD_none, G.mul_zero]
  | cons value message ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem weightedMessage_fold_read (parts : List (G × List G)) (start : List G) (i : Nat) :
    (parts.foldl (fun combined part => addMessages combined (scaleMessage part.1 part.2)) start)[i]?.getD 0 =
      (parts.map fun part => part.1 * part.2[i]?.getD 0).foldl (· + ·) (start[i]?.getD 0) := by
  induction parts generalizing start with
  | nil => rfl
  | cons part parts ih =>
    simp only [List.foldl_cons, List.map_cons, ih, addMessages_read, scaleMessage_read]

theorem weightedMessage_read (parts : List (G × List G)) (i : Nat) :
    (weightedMessage parts)[i]?.getD 0 = selectorSum (parts.map fun part => part.1 * part.2[i]?.getD 0) :=
  weightedMessage_fold_read parts [] i

theorem selectorSum_append (left right : List G) :
    selectorSum (left ++ right) = selectorSum left + selectorSum right := by
  change (left ++ right).foldl (· + ·) 0 = left.foldl (· + ·) 0 + selectorSum right
  rw [List.foldl_append, foldl_add_eq]

theorem weighted_value_zero {parts : List (G × List G)}
    (zero : ∀ part ∈ parts, part.1 = 0) (i : Nat) :
    selectorSum (parts.map fun part => part.1 * part.2[i]?.getD 0) = 0 := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    have tail := ih (fun p member => zero p (List.mem_cons_of_mem part member))
    simp only [List.map_cons, selectorSum_cons, zero part List.mem_cons_self,
      G.mul_comm 0, G.mul_zero, G.zero_add, tail]

theorem weightedMessage_split (width : Nat) (before after : List (G × List G)) (chosen : G × List G)
    (active : chosen.1 = 1) (zero : ∀ part ∈ before ++ after, part.1 = 0) :
    padMessage width (weightedMessage (before ++ chosen :: after)) = padMessage width chosen.2 := by
  apply congrArg List.ofFn
  funext i
  have beforeZero := weighted_value_zero (fun p member => zero p (List.mem_append_left _ member)) i.val
  have afterZero := weighted_value_zero (fun p member => zero p (List.mem_append_right _ member)) i.val
  change (weightedMessage (before ++ chosen :: after))[i.val]?.getD 0 = chosen.2[i.val]?.getD 0
  rw [weightedMessage_read, List.map_append, selectorSum_append, beforeZero, G.zero_add,
    List.map_cons, selectorSum_cons, afterZero, G.add_zero, active, G.mul_comm, G.mul_one]

theorem selector_parts_active_split {parts : List (G × List G)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1) :
    ∃ before chosen after, parts = before ++ chosen :: after ∧ chosen.1 = 1 ∧
      ∀ part ∈ before ++ after, part.1 = 0 := by
  obtain ⟨before, after, split, zero⟩ := selectorSum_active_split
    (fun value member => by
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst value
      exact individual part partMember)
    (by simpa only [List.length_map] using bounded) active
  obtain ⟨first, rest, partsEq, firstEq, restEq⟩ := List.map_eq_append_iff.mp split
  obtain ⟨chosen, last, tailEq, activeChosen, lastEq⟩ := List.map_eq_cons_iff.mp restEq
  refine ⟨first, chosen, last, by rw [partsEq, tailEq], activeChosen, ?_⟩
  intro part member
  apply zero part.1
  rcases List.mem_append.mp member with firstMember | lastMember
  · apply List.mem_append_left
    rw [← firstEq]
    exact List.mem_map.mpr ⟨part, firstMember, rfl⟩
  · apply List.mem_append_right
    rw [← lastEq]
    exact List.mem_map.mpr ⟨part, lastMember, rfl⟩

/-- A shared slot contains exactly the selected branch's padded message.
Inactive branches may have different lengths and arbitrary field values. -/
theorem weightedMessage_active (width : Nat) {parts : List (G × List G)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1) :
    ∃ chosen ∈ parts, chosen.1 = 1 ∧
      padMessage width (weightedMessage parts) = padMessage width chosen.2 := by
  obtain ⟨before, chosen, after, partsEq, activeChosen, zero⟩ :=
    selector_parts_active_split individual bounded active
  refine ⟨chosen, ?_, activeChosen, ?_⟩
  · rw [partsEq]
    exact List.mem_append_right _ List.mem_cons_self
  · rw [partsEq]
    exact weightedMessage_split width before after chosen activeChosen zero

theorem weightedMessage_inactive (width : Nat) {parts : List (G × List G)}
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (inactive : selectorSum (parts.map Prod.fst) = 0) :
    padMessage width (weightedMessage parts) = padMessage width [] := by
  have zero := selectorSum_inactive
    (fun value member => by
      obtain ⟨part, partMember, equal⟩ := List.mem_map.mp member
      subst value
      exact individual part partMember)
    (by simpa only [List.length_map] using bounded) inactive
  apply congrArg List.ofFn
  funext i
  change (weightedMessage parts)[i.val]?.getD 0 = 0
  rw [weightedMessage_read]
  exact weighted_value_zero (fun part member => zero _ (List.mem_map.mpr ⟨part, member, rfl⟩)) i.val

/-- Native lookup gating omits the selector product for a slot known to
have just one writer. Multiplicity still determines whether it is used. -/
def gateMessage (branchless : Bool) (selector : G) (message : List G) : List G :=
  if branchless then message else scaleMessage selector message

def slotMessage (branchless : Bool) (parts : List (G × List G)) : List G :=
  parts.foldl (fun combined part => addMessages combined (gateMessage branchless part.1 part.2)) []

theorem gateMessage_active (branchless : Bool) {selector : G} (message : List G)
    (active : selector = 1) : gateMessage branchless selector message = message := by
  cases branchless <;> simp [gateMessage, scaleMessage, active, G.mul_comm, G.mul_one]

/-- The branchless optimization is sound on an active slot when its layout
actually gives it one writer. That layout property is an explicit premise. -/
theorem slotMessage_active (width : Nat) (branchless : Bool) {parts : List (G × List G)}
    (single : branchless = true → parts.length = 1)
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1) :
    ∃ chosen ∈ parts, chosen.1 = 1 ∧
      padMessage width (slotMessage branchless parts) = padMessage width chosen.2 := by
  cases branchless with
  | false => exact weightedMessage_active width individual bounded active
  | true =>
    obtain ⟨part, equal⟩ := List.length_eq_one_iff.mp (single rfl)
    subst parts
    have selected : part.1 = 1 := by
      simpa only [List.map_cons, List.map_nil, selectorSum_cons,
        selectorSum, List.foldl_nil, List.foldl_cons, G.zero_add, G.add_zero] using active
    exact ⟨part, List.mem_cons_self, selected, rfl⟩

/-- A continuation's active merge columns equal the values of its unique
active yield. The caller must establish that the parent is active and that
the native continuation-link equation makes the yield sum one. -/
theorem continuation_merge {parent : G} {parts : List (G × List G)} {merged : List G}
    (parentActive : parent = 1)
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1)
    (sizes : ∀ part ∈ parts, part.2.length = merged.length)
    (equations : ∀ i, i < merged.length →
      parent * (merged[i]?.getD 0 -
        selectorSum (parts.map fun part => part.1 * part.2[i]?.getD 0)) = 0) :
    ∃ chosen ∈ parts, chosen.1 = 1 ∧ merged = chosen.2 := by
  obtain ⟨chosen, member, selected, message⟩ :=
    weightedMessage_active merged.length individual bounded active
  refine ⟨chosen, member, selected, ?_⟩
  apply padMessage_injective_of_length (Nat.le_refl _) (sizes chosen member).symm
  apply Eq.trans _ message
  apply congrArg List.ofFn
  funext i
  change merged[i.val]?.getD 0 = (weightedMessage parts)[i.val]?.getD 0
  rw [weightedMessage_read]
  have equation := equations i.val i.isLt
  rw [parentActive, G.mul_comm, G.mul_one] at equation
  exact (G.sub_eq_zero_iff _ _).mp equation

end Aiur.AIR
