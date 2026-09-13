/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.FriQuery
import Ix.Aiur.Proofs.Folding

/-! Accepted query steps preserve sibling order and the carried value,
evaluate the row interpolant and implement global polynomial folding.
Complete chains consume descending input heights and reach the exact final
index and polynomial value. The captured rows still require authentication.
-/

namespace Aiur.NativeAIR.FriQuery

open ProofCodec (Extension)
open _root_.Aiur.NativeAIR.Quotient (horner)

theorem reconstruct_eq (arity : Domain.Subgroup) (index : Nat) (value : R) (siblings : List R)
    (shape : siblings.length + 1 = Domain.size arity) :
    reconstruct arity index value siblings = some (siblings.insertIdx (index % Domain.size arity) value) := by
  simp only [reconstruct, shape, beq_self_eq_true, if_true]

theorem reconstruct_success {arity : Domain.Subgroup} {index : Nat} {value : R} {siblings row : List R}
    (accepted : reconstruct arity index value siblings = some row) :
    siblings.length + 1 = Domain.size arity ∧ row = siblings.insertIdx (index % Domain.size arity) value := by
  unfold reconstruct at accepted
  split at accepted
  next shape => exact ⟨beq_iff_eq.mp shape, (Option.some.inj accepted).symm⟩
  next _ => cases accepted

theorem reconstruct_length {arity : Domain.Subgroup} {index : Nat} {value : R} {siblings row : List R}
    (accepted : reconstruct arity index value siblings = some row) : row.length = Domain.size arity := by
  obtain ⟨shape, rfl⟩ := reconstruct_success accepted
  rw [List.length_insertIdx_of_le_length _ value, shape]
  have bounded := Nat.mod_lt index (Domain.size_positive arity)
  omega

theorem reconstruct_self {arity : Domain.Subgroup} {index : Nat} {value : R} {siblings row : List R}
    (accepted : reconstruct arity index value siblings = some row) :
    row[index % Domain.size arity]? = some value := by
  obtain ⟨shape, rfl⟩ := reconstruct_success accepted
  rw [List.getElem?_insertIdx_self, if_pos]
  have bounded := Nat.mod_lt index (Domain.size_positive arity)
  omega

theorem reconstruct_siblings {arity : Domain.Subgroup} {index : Nat} {value : R} {siblings row : List R}
    (accepted : reconstruct arity index value siblings = some row) :
    row.eraseIdx (index % Domain.size arity) = siblings := by
  obtain ⟨_, rfl⟩ := reconstruct_success accepted
  exact List.eraseIdx_insertIdx_self value

theorem step_success {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) :
    0 < round.arity.val ∧ round.arity.val ≤ state.domain.val ∧
      ∃ child values folded,
        Domain.ofLogSize (state.domain.val - round.arity.val) = some child ∧
        reconstruct round.arity state.index state.value round.siblings = some values ∧
        Interpolation.foldRow state.domain round.arity (state.index / Domain.size round.arity) values round.challenge = some folded ∧
        result = ⟨⟨child, state.index / Domain.size round.arity,
          (roll child.val (round.challenge.power (Domain.size round.arity)) folded openings).1⟩,
          (roll child.val (round.challenge.power (Domain.size round.arity)) folded openings).2,
          ⟨child, state.index / Domain.size round.arity, values⟩⟩ := by
  unfold step at accepted
  split at accepted
  next _ => cases accepted
  next admitted =>
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at admitted
    cases childRead : Domain.ofLogSize (state.domain.val - round.arity.val) with
    | none => simp only [childRead, bind, Option.bind_none] at accepted; cases accepted
    | some child =>
      simp only [childRead, bind, Option.bind_some] at accepted
      cases rowRead : reconstruct round.arity state.index state.value round.siblings with
      | none => simp only [rowRead, Option.bind_none] at accepted; cases accepted
      | some values =>
        simp only [rowRead, Option.bind_some] at accepted
        cases foldRead : Interpolation.foldRow state.domain round.arity
            (state.index / Domain.size round.arity) values round.challenge with
        | none => simp only [foldRead, Option.bind_none] at accepted; cases accepted
        | some folded =>
          simp only [foldRead, Option.bind_some, pure] at accepted
          exact ⟨by omega, by omega, child, values, folded, rfl, rfl, foldRead,
            (Option.some.inj accepted).symm⟩

theorem step_dimensions {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) :
    0 < round.arity.val ∧ state.domain.val = result.state.domain.val + round.arity.val ∧
      result.state.index = state.index / Domain.size round.arity ∧
      result.state.index < Domain.size result.state.domain ∧
      result.row.domain = result.state.domain ∧ result.row.index = result.state.index := by
  obtain ⟨positive, nested, child, values, folded, childRead, _, foldRead, rfl⟩ := step_success accepted
  have childValue := Domain.ofLogSize_some childRead
  have bounded := (Interpolation.foldRow_success foldRead).2.1
  refine ⟨positive, by simp only; omega, rfl, ?_, rfl, rfl⟩
  simpa only [Domain.size, childValue] using bounded

theorem step_row {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) :
    result.row.values.length = Domain.size round.arity ∧
      result.row.values[state.index % Domain.size round.arity]? = some state.value ∧
      result.row.values.eraseIdx (state.index % Domain.size round.arity) = round.siblings := by
  obtain ⟨_, _, _, _, _, _, rowRead, _, rfl⟩ := step_success accepted
  exact ⟨reconstruct_length rowRead, reconstruct_self rowRead, reconstruct_siblings rowRead⟩

theorem step_index_bound {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) : state.index < Domain.size state.domain := by
  obtain ⟨_, dimensions, index, bounded, _, _⟩ := step_dimensions accepted
  rw [index, Nat.div_lt_iff_lt_mul (Domain.size_positive round.arity)] at bounded
  simpa only [Domain.size, dimensions, Nat.pow_add] using bounded

theorem step_self_sample {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) :
    (Extension.ofBase (FriDomain.queryPoint state.domain state.index), state.value) ∈
      Interpolation.foldSamples state.domain round.arity result.state.index result.row.values := by
  obtain ⟨_, dimensions, index, bounded, _, _⟩ := step_dimensions accepted
  have nested : round.arity.val ≤ state.domain.val := by omega
  have groupBound : result.state.index < 2^(state.domain.val - round.arity.val) := by
    simpa only [Domain.size, dimensions, Nat.add_sub_cancel] using bounded
  have slotBound := Nat.mod_lt state.index (Domain.size_positive round.arity)
  have node := FriDomain.foldNode_eq state.domain round.arity nested groupBound slotBound
  have joined : result.state.index * Domain.size round.arity + state.index % Domain.size round.arity = state.index := by
    rw [index, Nat.mul_comm, Nat.div_add_mod]
  rw [joined] at node
  apply List.mem_of_getElem? (i := state.index % Domain.size round.arity)
  apply List.getElem?_zip_eq_some.mpr
  constructor
  · simp only [Polynomial.foldingNodes, List.getElem?_map, List.getElem?_range slotBound, Option.map_some, node]
  · exact (step_row accepted).2.1

theorem step_polynomial {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) :
    ∃ candidate : List Extension, candidate.length ≤ Domain.size round.arity ∧
      horner (Extension.ofBase (FriDomain.queryPoint state.domain state.index)) candidate = state.value ∧
      (∀ sample ∈ Interpolation.foldSamples state.domain round.arity result.state.index result.row.values,
        horner sample.1 candidate = sample.2) ∧
      (result.state.value, result.remaining) = roll result.state.domain.val
        (round.challenge.power (Domain.size round.arity)) (horner round.challenge candidate) openings := by
  have self := step_self_sample accepted
  obtain ⟨_, _, child, values, folded, _, _, foldRead, output⟩ := step_success accepted
  obtain ⟨_, _, _, candidate, degree, agrees, value⟩ := Interpolation.foldRow_success foldRead
  refine ⟨candidate, degree, ?_, ?_, ?_⟩
  · exact agrees (Extension.ofBase (FriDomain.queryPoint state.domain state.index), state.value)
      (by simpa only [output] using self)
  · simpa only [output] using agrees
  · simp only [output]
    rw [← value]

theorem step_global {state : State} {round : Round} {openings : List (Nat × Extension)} {result : StepResult}
    (accepted : step state round openings = some result) (coefficients : List Extension)
    (agrees : ∀ sample ∈ Interpolation.foldSamples state.domain round.arity result.state.index result.row.values,
      horner sample.1 coefficients = sample.2) :
    (result.state.value, result.remaining) = roll result.state.domain.val
      (round.challenge.power (Domain.size round.arity))
      (horner (Extension.ofBase (FriDomain.queryPoint result.state.domain result.state.index))
        (Folding.foldCoefficients round.arity round.challenge coefficients)) openings := by
  obtain ⟨_, nested, child, values, folded, childRead, rowRead, foldRead, rfl⟩ := step_success accepted
  have dimensions : state.domain.val = child.val + round.arity.val := by
    have := Domain.ofLogSize_some childRead
    omega
  have bounded := (Interpolation.foldRow_success foldRead).2.1
  rw [Folding.foldRow_global state.domain child round.arity dimensions bounded values coefficients
    (reconstruct_length rowRead) agrees] at foldRead
  rw [Option.some.inj foldRead]

theorem roll_length (height : Nat) (factor value : Extension) (openings : List (Nat × Extension)) :
    (roll height factor value openings).2.length ≤ openings.length := by
  cases openings with
  | nil => exact Nat.le_refl _
  | cons entry rest =>
    rcases entry with ⟨nextHeight, next⟩
    change (if nextHeight == height then (value + factor * next, rest)
      else (value, (nextHeight, next) :: rest)).2.length ≤ rest.length + 1
    split <;> simp only [List.length_cons] <;> omega

theorem roll_empty (height : Nat) (factor value : Extension) : roll height factor value [] = (value, []) := rfl

theorem roll_matching (height : Nat) (factor value next : Extension) (rest : List (Nat × Extension)) :
    roll height factor value ((height, next) :: rest) = (value + factor * next, rest) := by
  simp only [roll, beq_self_eq_true, if_true]

theorem roll_other (height nextHeight : Nat) (factor value next : Extension) (rest : List (Nat × Extension))
    (different : nextHeight ≠ height) :
    roll height factor value ((nextHeight, next) :: rest) = (value, (nextHeight, next) :: rest) := by
  simp only [roll, beq_iff_eq, if_neg different]

theorem roll_count (height : Nat) (factor value : Extension) (openings : List (Nat × Extension)) :
    openings.length ≤ (roll height factor value openings).2.length + 1 := by
  cases openings with
  | nil => exact Nat.zero_le _
  | cons entry rest =>
    rcases entry with ⟨nextHeight, next⟩
    by_cases same : nextHeight = height
    · subst nextHeight
      rw [roll_matching]
      exact Nat.le_refl _
    · rw [roll_other height nextHeight factor value next rest same]
      exact Nat.le_succ _

theorem roll_order (height : Nat) (factor value : Extension) (openings : List (Nat × Extension))
    (unique : (roll height factor value openings).2.Pairwise (fun left right => right.1 < left.1))
    (bounded : ∀ entry ∈ (roll height factor value openings).2, entry.1 < height) :
    openings.Pairwise (fun left right => right.1 < left.1) ∧
      ∀ entry ∈ openings, entry.1 ≤ height := by
  cases openings with
  | nil => exact ⟨List.Pairwise.nil, fun _ member => by cases member⟩
  | cons entry rest =>
    rcases entry with ⟨nextHeight, next⟩
    by_cases same : nextHeight = height
    · subst nextHeight
      rw [roll_matching] at unique bounded
      refine ⟨List.pairwise_cons.mpr ⟨bounded, unique⟩, ?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (bounded entry later)
    · rw [roll_other height nextHeight factor value next rest same] at unique bounded
      exact ⟨unique, fun entry member => Nat.le_of_lt (bounded entry member)⟩

theorem walk_nil_success {final : Domain.Subgroup} {state : State}
    {openings : List (Nat × Extension)} {result : Result}
    (accepted : walk final state openings [] = some result) :
    state.domain = final ∧ openings = [] ∧ result = ⟨state, []⟩ := by
  unfold walk at accepted
  split at accepted
  next shape =>
    obtain ⟨height, empty⟩ := (by simpa only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] using shape :
      state.domain = final ∧ openings = [])
    exact ⟨height, empty, (Option.some.inj accepted).symm⟩
  next _ => cases accepted

theorem walk_cons_success {final : Domain.Subgroup} {state : State}
    {openings : List (Nat × Extension)} {round : Round} {rest : List Round} {result : Result}
    (accepted : walk final state openings (round :: rest) = some result) :
    ∃ head tail, step state round openings = some head ∧
      walk final head.state head.remaining rest = some tail ∧ result = ⟨tail.state, head.row :: tail.rows⟩ := by
  rw [walk] at accepted
  cases headRead : step state round openings with
  | none => simp only [headRead, bind, Option.bind_none] at accepted; cases accepted
  | some head =>
    simp only [headRead, bind, Option.bind_some] at accepted
    cases tailRead : walk final head.state head.remaining rest with
    | none => simp only [tailRead, Option.bind_none] at accepted; cases accepted
    | some tail =>
      simp only [tailRead, Option.bind_some, pure] at accepted
      exact ⟨head, tail, rfl, tailRead, (Option.some.inj accepted).symm⟩

theorem walk_summary {final : Domain.Subgroup} {state : State}
    {openings : List (Nat × Extension)} {rounds : List Round} {result : Result}
    (accepted : walk final state openings rounds = some result) :
    result.state.domain = final ∧ result.rows.length = rounds.length ∧
      state.domain.val = final.val + (rounds.map (fun round => round.arity.val)).sum ∧
      result.state.index = state.index / 2^((rounds.map (fun round => round.arity.val)).sum) := by
  induction rounds generalizing state openings result with
  | nil =>
    obtain ⟨height, _, rfl⟩ := walk_nil_success accepted
    refine ⟨height, rfl, ?_, ?_⟩
    · simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using congrArg Fin.val height
    · simp only [List.map_nil, List.sum_nil, Nat.pow_zero, Nat.div_one]
  | cons round rest ih =>
    obtain ⟨head, tail, stepRead, tailRead, rfl⟩ := walk_cons_success accepted
    obtain ⟨height, length, dimensions, index⟩ := ih tailRead
    obtain ⟨_, headDimensions, headIndex, _, _, _⟩ := step_dimensions stepRead
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    refine ⟨height, by simp only [length], by omega, ?_⟩
    rw [index, headIndex, Nat.div_div_eq_div_mul, Domain.size, ← Nat.pow_add]

theorem walk_openings {final : Domain.Subgroup} {state : State}
    {openings : List (Nat × Extension)} {rounds : List Round} {result : Result}
    (accepted : walk final state openings rounds = some result) :
    openings.Pairwise (fun left right => right.1 < left.1) ∧
      (∀ entry ∈ openings, entry.1 < state.domain.val) ∧ openings.length ≤ rounds.length := by
  induction rounds generalizing state openings result with
  | nil =>
    obtain ⟨_, rfl, _⟩ := walk_nil_success accepted
    exact ⟨List.Pairwise.nil, (fun _ member => by cases member), Nat.le_refl _⟩
  | cons round rest ih =>
    obtain ⟨head, tail, stepRead, tailRead, _⟩ := walk_cons_success accepted
    obtain ⟨positive, nested, child, values, folded, childRead, _, _, rfl⟩ := step_success stepRead
    obtain ⟨unique, bounded, count⟩ := ih tailRead
    change (roll child.val (round.challenge.power (Domain.size round.arity)) folded openings).2.length ≤ rest.length at count
    obtain ⟨oldUnique, oldBounded⟩ := roll_order child.val
      (round.challenge.power (Domain.size round.arity)) folded openings unique bounded
    have childValue := Domain.ofLogSize_some childRead
    have childLess : child.val < state.domain.val := by omega
    have removed := roll_count child.val (round.challenge.power (Domain.size round.arity)) folded openings
    exact ⟨oldUnique, fun entry member => Nat.lt_of_le_of_lt (oldBounded entry member) childLess,
      by simp only [List.length_cons]; omega⟩

theorem run_success {initial final : Domain.Subgroup} {index : Nat}
    {openings : List (Nat × Extension)} {rounds : List Round} {result : Result}
    (accepted : run initial final index openings rounds = some result) :
    index < Domain.size initial ∧ ∃ value rest, openings = (initial.val, value) :: rest ∧
      walk final ⟨initial, index, value⟩ rest rounds = some result := by
  unfold run at accepted
  split at accepted
  next _ => cases accepted
  next admitted =>
    refine ⟨by omega, ?_⟩
    cases openings with
    | nil => cases accepted
    | cons entry rest =>
      rcases entry with ⟨height, value⟩
      change (if height == initial.val then walk final ⟨initial, index, value⟩ rest rounds else none) = some result at accepted
      split at accepted
      next matching =>
        have same : height = initial.val := beq_iff_eq.mp matching
        subst height
        exact ⟨value, rest, rfl, accepted⟩
      next _ => cases accepted

theorem run_summary {initial final : Domain.Subgroup} {index : Nat}
    {openings : List (Nat × Extension)} {rounds : List Round} {result : Result}
    (accepted : run initial final index openings rounds = some result) :
    index < Domain.size initial ∧ result.state.domain = final ∧
      result.rows.length = rounds.length ∧
      initial.val = final.val + (rounds.map (fun round => round.arity.val)).sum ∧
      result.state.index = index / 2^((rounds.map (fun round => round.arity.val)).sum) ∧
      result.state.index < Domain.size final ∧
      openings.Pairwise (fun left right => right.1 < left.1) ∧ openings.length ≤ rounds.length + 1 := by
  obtain ⟨indexBound, value, rest, rfl, walked⟩ := run_success accepted
  obtain ⟨height, length, dimensions, finalIndex⟩ := walk_summary walked
  change initial.val = final.val + (rounds.map (fun round => round.arity.val)).sum at dimensions
  obtain ⟨unique, bounded, count⟩ := walk_openings walked
  refine ⟨indexBound, height, length, dimensions, finalIndex, ?_,
    List.pairwise_cons.mpr ⟨bounded, unique⟩, by simp only [List.length_cons]; omega⟩
  rw [finalIndex, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  simpa only [Domain.size, dimensions, Nat.pow_add] using indexBound

theorem check_success {initial final : Domain.Subgroup} {index : Nat}
    {openings : List (Nat × Extension)} {rounds : List Round} {finalPolynomial : List Extension} {result : Result}
    (accepted : check initial final index openings rounds finalPolynomial = some result) :
    run initial final index openings rounds = some result ∧
      horner (Extension.ofBase (FriDomain.queryPoint initial result.state.index)) finalPolynomial = result.state.value := by
  unfold check at accepted
  cases runRead : run initial final index openings rounds with
  | none => simp only [runRead, bind, Option.bind_none] at accepted; cases accepted
  | some output =>
    simp only [runRead, bind, Option.bind_some] at accepted
    split at accepted
    next matching =>
      cases accepted
      exact ⟨rfl, beq_iff_eq.mp matching⟩
    next _ => cases accepted

theorem check_final_polynomial {initial final : Domain.Subgroup} {index : Nat}
    {openings : List (Nat × Extension)} {rounds : List Round} {finalPolynomial : List Extension} {result : Result}
    (accepted : check initial final index openings rounds finalPolynomial = some result) :
    horner (Extension.ofBase (FriDomain.queryPoint final result.state.index)) finalPolynomial = result.state.value := by
  obtain ⟨runRead, equal⟩ := check_success accepted
  obtain ⟨_, _, _, dimensions, _, bounded, _, _⟩ := run_summary runRead
  rw [FriDomain.queryPoint_padding initial final (by omega) bounded] at equal
  exact equal

end Aiur.NativeAIR.FriQuery
