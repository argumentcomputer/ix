/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GlobalLookups

/-!
The native verifier's conservative lookup-consumer budget.

Canonical slot counts and active-order trace heights determine the bound:
one public claim plus every lookup slot in every active trace row. The total
natural-number model below checks sequence alignment, shift bounds and the
strict field-characteristic bound. Its accepted arithmetic fits the native
checked u64 operations. The component gate compares both implementations.

Interpreting actual consumer multiplicities as zero or one and counting them
within these slots still belongs to native AIR extraction. These definitions
and comparisons are not a proof of Rust execution refinement.
-/

namespace Aiur

/-- Canonical circuit slot counts and the activation bitmap consume trace
degrees in active order. Missing, extra and misaligned entries fail. -/
def lookupSlotSum : List Nat → List Bool → List Nat → Option Nat
  | [], [], [] => some 0
  | _ :: slots, false :: active, degrees => lookupSlotSum slots active degrees
  | slots :: rest, true :: active, degree :: degrees => do
    let tail ← lookupSlotSum rest active degrees
    pure (2 ^ degree * slots + tail)
  | _, _, _ => none

def lookupQueryBoundAux : List Nat → List Bool → List Nat → Nat → Option Nat
  | [], [], [], used => some used
  | _ :: slots, false :: active, degrees, used => lookupQueryBoundAux slots active degrees used
  | slots :: rest, true :: active, degree :: degrees, used =>
    if degree < 64 then
      let next := used + 2 ^ degree * slots
      if next < gSize.toNat then lookupQueryBoundAux rest active degrees next else none
    else none
  | _, _, _, _ => none

/-- Total natural-number mirror of the native checked-u64 budget guard.
Counting every slot includes providers and bounds unit consumers from above.
The initial one is the single public claim. -/
def lookupQueryBound (slots : List Nat) (active : List Bool) (degrees : List Nat) : Option Nat :=
  if active.any id then lookupQueryBoundAux slots active degrees 1 else none

theorem lookupQueryBoundAux_sound {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {used result : Nat} (below : used < gSize.toNat)
    (accepted : lookupQueryBoundAux slots active degrees used = some result) :
    ∃ total, lookupSlotSum slots active degrees = some total ∧ result = used + total ∧
      result < gSize.toNat := by
  induction slots generalizing active degrees used with
  | nil =>
    cases active <;> cases degrees <;> simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
    cases accepted
    exact ⟨0, rfl, by omega, below⟩
  | cons count slots ih =>
    cases active with
    | nil => simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
    | cons enabled active =>
      cases enabled with
      | false => exact ih below accepted
      | true =>
        cases degrees with
        | nil => simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
        | cons degree degrees =>
          simp only [lookupQueryBoundAux] at accepted
          split at accepted
          next degreeBound =>
            split at accepted
            next nextBound =>
              obtain ⟨total, shape, sum, bounded⟩ := ih nextBound accepted
              refine ⟨2 ^ degree * count + total, ?_, by omega, bounded⟩
              simp only [lookupSlotSum, shape, bind, Option.bind, pure]
            next => contradiction
          next => contradiction

theorem lookupQueryBound_sound {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {result : Nat} (accepted : lookupQueryBound slots active degrees = some result) :
    active.any id = true ∧ ∃ total, lookupSlotSum slots active degrees = some total ∧
      result = 1 + total ∧ result < gSize.toNat := by
  simp only [lookupQueryBound] at accepted
  split at accepted
  next enabled => exact ⟨enabled, lookupQueryBoundAux_sound (by decide) accepted⟩
  next => contradiction

theorem lookupQueryBound_consumer_count {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {result total : Nat} (accepted : lookupQueryBound slots active degrees = some result)
    (shape : lookupSlotSum slots active degrees = some total)
    {α : Type u} (queries : List α) (perSlot : queries.length ≤ total) :
    (queries.length + 1) < gSize.toNat := by
  obtain ⟨_, sum, sameShape, sameResult, below⟩ := lookupQueryBound_sound accepted
  have equal := Option.some.inj (sameShape.symm.trans shape)
  omega

theorem lookupQueryBoundAux_shape {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {used result : Nat} (accepted : lookupQueryBoundAux slots active degrees used = some result) :
    slots.length = active.length ∧ degrees.length = active.count true ∧
      ∀ degree ∈ degrees, degree < 64 := by
  induction slots generalizing active degrees used with
  | nil =>
    cases active <;> cases degrees <;> simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
    exact ⟨rfl, rfl, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
  | cons count slots ih =>
    cases active with
    | nil => simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
    | cons enabled active =>
      cases enabled with
      | false =>
        obtain ⟨aligned, degreesCount, bounded⟩ := ih accepted
        refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ aligned, ?_, bounded⟩
        simpa only [List.count_cons, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          using degreesCount
      | true =>
        cases degrees with
        | nil => simp only [lookupQueryBoundAux, reduceCtorEq] at accepted
        | cons degree degrees =>
          simp only [lookupQueryBoundAux] at accepted
          split at accepted
          next degreeBound =>
            split at accepted
            next =>
              obtain ⟨aligned, degreesCount, bounded⟩ := ih accepted
              refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ aligned, ?_, ?_⟩
              · simpa only [List.length_cons, List.count_cons, beq_iff_eq, ↓reduceIte, Nat.succ_eq_add_one]
                  using congrArg Nat.succ degreesCount
              · intro d member
                rcases List.mem_cons.mp member with same | later
                · exact same ▸ degreeBound
                · exact bounded d later
            next => contradiction
          next => contradiction

theorem lookupQueryBound_shape {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {result : Nat} (accepted : lookupQueryBound slots active degrees = some result) :
    active.any id = true ∧ slots.length = active.length ∧
      degrees.length = active.count true ∧ ∀ degree ∈ degrees, degree < 64 := by
  simp only [lookupQueryBound] at accepted
  split at accepted
  next enabled => exact ⟨enabled, lookupQueryBoundAux_shape accepted⟩
  next => contradiction

/-- A step admitted by the natural-number guard fits both native checked
u64 operations. Arithmetic overflow can never turn a rejected sum into an
accepted smaller count. -/
theorem lookupQueryBound_step_no_overflow {used height slots : Nat}
    (accepted : used + height * slots < gSize.toNat) :
    height * slots < 2 ^ 64 ∧ used + height * slots < 2 ^ 64 := by
  have modulus : gSize.toNat < 2 ^ 64 := by decide +kernel
  omega

theorem lookupQueryBoundAux_complete {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {used total : Nat} (shape : lookupSlotSum slots active degrees = some total)
    (degreesBound : ∀ degree ∈ degrees, degree < 64)
    (bounded : used + total < gSize.toNat) :
    lookupQueryBoundAux slots active degrees used = some (used + total) := by
  induction slots generalizing active degrees used total with
  | nil =>
    cases active <;> cases degrees <;> simp only [lookupSlotSum, reduceCtorEq] at shape
    cases shape
    rfl
  | cons count slots ih =>
    cases active with
    | nil => simp only [lookupSlotSum, reduceCtorEq] at shape
    | cons enabled active =>
      cases enabled with
      | false => exact ih shape degreesBound bounded
      | true =>
        cases degrees with
        | nil => simp only [lookupSlotSum, reduceCtorEq] at shape
        | cons degree degrees =>
          cases tail : lookupSlotSum slots active degrees with
          | none => simp only [lookupSlotSum, tail, bind, Option.bind, reduceCtorEq] at shape
          | some rest =>
            have totalEq : 2 ^ degree * count + rest = total := by
              simpa only [lookupSlotSum, tail, bind, Option.bind, pure, Option.some.injEq] using shape
            have nextBound : used + 2 ^ degree * count < gSize.toNat := by omega
            have continued := ih tail
              (fun d member => degreesBound d (List.mem_cons_of_mem degree member))
              (used := used + 2 ^ degree * count) (by omega)
            simp only [lookupQueryBoundAux, if_pos (degreesBound degree List.mem_cons_self),
              if_pos nextBound, continued]
            congr 1
            omega

theorem lookupQueryBound_complete {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {total : Nat} (enabled : active.any id = true)
    (shape : lookupSlotSum slots active degrees = some total)
    (degreesBound : ∀ degree ∈ degrees, degree < 64)
    (bounded : 1 + total < gSize.toNat) :
    lookupQueryBound slots active degrees = some (1 + total) := by
  simp only [lookupQueryBound, enabled, ↓reduceIte]
  exact lookupQueryBoundAux_complete shape degreesBound bounded

theorem lookupSlotSum_bounded {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {total maxSlots maxDegree : Nat} (shape : lookupSlotSum slots active degrees = some total)
    (slotsBound : ∀ count ∈ slots, count ≤ maxSlots)
    (degreesBound : ∀ degree ∈ degrees, degree ≤ maxDegree) :
    total ≤ slots.length * (2 ^ maxDegree * maxSlots) := by
  induction slots generalizing active degrees total with
  | nil =>
    cases active <;> cases degrees <;> simp only [lookupSlotSum, reduceCtorEq] at shape
    cases shape
    exact Nat.zero_le _
  | cons count slots ih =>
    have tailSlots : ∀ n ∈ slots, n ≤ maxSlots :=
      fun n member => slotsBound n (List.mem_cons_of_mem count member)
    cases active with
    | nil => simp only [lookupSlotSum, reduceCtorEq] at shape
    | cons enabled active =>
      cases enabled with
      | false =>
        have bound := ih shape tailSlots degreesBound
        simp only [List.length_cons, Nat.add_mul]
        omega
      | true =>
        cases degrees with
        | nil => simp only [lookupSlotSum, reduceCtorEq] at shape
        | cons degree degrees =>
          cases tail : lookupSlotSum slots active degrees with
          | none => simp only [lookupSlotSum, tail, bind, Option.bind, reduceCtorEq] at shape
          | some rest =>
            have totalEq : 2 ^ degree * count + rest = total := by
              simpa only [lookupSlotSum, tail, bind, Option.bind, pure, Option.some.injEq] using shape
            have tailBound := ih tail tailSlots
              (fun d member => degreesBound d (List.mem_cons_of_mem degree member))
            have powerBound : 2 ^ degree ≤ 2 ^ maxDegree :=
              Nat.pow_le_pow_right (by decide) (degreesBound degree List.mem_cons_self)
            have headBound := Nat.mul_le_mul powerBound (slotsBound count List.mem_cons_self)
            simp only [List.length_cons, Nat.add_mul]
            omega

/-- Version-five keys encode circuit and slot counts as u16. Together with
Goldilocks' maximum 2^32 trace height, those format limits already leave a
strict margin below the characteristic. The explicit budget guard preserves
every such well-shaped proof, independently of its chosen activation subset. -/
theorem lookupQueryBound_encodedKey {slots : List Nat} {active : List Bool} {degrees : List Nat}
    {total : Nat} (enabled : active.any id = true)
    (shape : lookupSlotSum slots active degrees = some total)
    (circuitCount : slots.length < 65536)
    (slotsBound : ∀ count ∈ slots, count < 65536)
    (degreesBound : ∀ degree ∈ degrees, degree ≤ 32) :
    lookupQueryBound slots active degrees = some (1 + total) := by
  apply lookupQueryBound_complete enabled shape
    (fun degree member => Nat.lt_of_le_of_lt (degreesBound degree member) (by decide))
  have totalBound := lookupSlotSum_bounded shape (maxSlots := 65535)
    (fun count member => Nat.le_sub_one_of_lt (slotsBound count member)) degreesBound
  have countBound : slots.length ≤ 65535 := by omega
  have outerBound := Nat.mul_le_mul_right (2 ^ 32 * 65535) countBound
  have margin : 1 + 65535 * (2 ^ 32 * 65535) < gSize.toNat := by decide +kernel
  omega

/-- The checked native budget supplies the global count premise once local
AIR extraction bounds internal unit consumers by the trace's slot total. -/
theorem AIR.GlobalLookups.of_budget {tables : AIR.LookupTables} {width : Nat}
    {slots : List Nat} {active : List Bool} {degrees : List Nat} {result total : Nat}
    (accepted : lookupQueryBound slots active degrees = some result)
    (shape : lookupSlotSum slots active degrees = some total)
    (root : List G) (queries : List (List G)) (perSlot : queries.length ≤ total)
    (balance : AIR.PaddedLookupBalance width (root :: queries) tables.providers)
    (widths : ∀ query ∈ root :: queries, query.length ≤ width) :
    AIR.GlobalLookups tables width (root :: queries) :=
  ⟨balance, lookupQueryBound_consumer_count accepted shape queries perSlot, widths⟩

end Aiur
