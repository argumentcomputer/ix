/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LogUpAlgebra
import Ix.Aiur.KeyCodec

/-! Checked reads, complete grouping, and the polynomial equations extracted
from the executable logUp evaluator. These results preserve both coordinates
and their order, including the last-row boundary injection. -/

namespace Aiur.NativeAIR.LogUp

theorem groupCount_positive (groupSize lookupCount : Nat) : 0 < groupCount groupSize lookupCount := by
  simp only [groupCount]; omega

theorem groupCount_covers (groupSize lookupCount : Nat) :
    lookupCount ≤ groupCount groupSize lookupCount * max groupSize 1 := by
  apply (Nat.le_mul_iff_le_left (by omega : 0 < max groupSize 1)).mpr
  exact Nat.le_max_right _ _

theorem groupCount_zero (lookupCount : Nat) : groupCount 0 lookupCount = groupCount 1 lookupCount := rfl

theorem groupCount_empty (groupSize : Nat) : groupCount groupSize 0 = 1 := by
  have positive : 0 < max groupSize 1 := by omega
  simp only [groupCount, Nat.zero_add, Nat.div_eq_of_lt (by omega : max groupSize 1 - 1 < max groupSize 1)]
  rfl

theorem groupCount_key (circuit : KeyCodec.Circuit) (positive : 0 < circuit.lookupGroupSize) :
    groupCount circuit.lookupGroupSize circuit.graph.lookups.length = circuit.groups := by
  simp only [groupCount, KeyCodec.Circuit.groups, Nat.max_eq_left positive]

theorem chunk_length (groupSize index : Nat) (values : List α) :
    (chunk groupSize index values).length = min (max groupSize 1) (values.length - index * max groupSize 1) := by
  simp only [chunk, List.length_take, List.length_drop]

theorem chunks_take (groupSize count : Nat) (values : List α) :
    (List.range count).flatMap (fun index => chunk groupSize index values) = values.take (count * max groupSize 1) := by
  induction count with
  | zero => simp only [List.range_zero, List.flatMap_nil, Nat.zero_mul, List.take_zero]
  | succ count ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, chunk, Nat.add_mul,
      Nat.one_mul, List.take_add]

theorem chunks_cover (groupSize : Nat) (values : List α) :
    (List.range (groupCount groupSize values.length)).flatMap (fun index => chunk groupSize index values) = values := by
  rw [chunks_take, List.take_of_length_le (groupCount_covers groupSize values.length)]

theorem chunk_mem {groupSize index : Nat} {values : List α} {value : α}
    (member : value ∈ chunk groupSize index values) : value ∈ values :=
  List.mem_of_mem_drop (List.mem_of_mem_take member)

theorem chunk_map (groupSize index : Nat) (values : List α) (f : α → β) :
    chunk groupSize index (values.map f) = (chunk groupSize index values).map f := by
  simp only [chunk, List.map_take, List.map_drop]

theorem mapM_some_reads {read : α → Option β} {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM read = some outputs) : outputs.length = inputs.length ∧
      ∀ (index : Nat) input, inputs[index]? = some input → ∃ output, outputs[index]? = some output ∧ read input = some output := by
  induction inputs generalizing outputs with
  | nil =>
    cases accepted
    exact ⟨rfl, fun _ _ impossible => by simp at impossible⟩
  | cons input inputs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at accepted
    obtain ⟨output, head, rest, tail, rfl⟩ := accepted
    obtain ⟨length, reads⟩ := ih tail
    refine ⟨congrArg (· + 1) length, ?_⟩
    intro index value valueRead
    cases index with
    | zero =>
      have same := Option.some.inj valueRead
      subst value
      exact ⟨output, rfl, head⟩
    | succ index => exact reads index value valueRead

theorem mapM_defined (inputs : List α) (read : α → Option β)
    (defined : ∀ input ∈ inputs, ∃ output, read input = some output) :
    ∃ outputs, inputs.mapM read = some outputs := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons input inputs ih =>
    obtain ⟨output, head⟩ := defined input List.mem_cons_self
    obtain ⟨outputs, tail⟩ := ih (fun value member => defined value (List.mem_cons_of_mem _ member))
    exact ⟨output :: outputs, by simp only [List.mapM_cons, head, tail, bind, Option.bind_some, pure]⟩

theorem read_coordinates_defined (values : Array W) (slot : Nat) (bounded : 2 * slot + 1 < values.size) :
    ∃ value, Coordinates.read values slot = some value := by
  have first : 2 * slot < values.size := by omega
  exact ⟨⟨values[2 * slot], values[2 * slot + 1]⟩, by
    simp only [Coordinates.read, Array.getElem?_eq_getElem first, Array.getElem?_eq_getElem bounded,
      bind, Option.bind_some, pure]⟩

theorem read_coordinates_success {values : Array W} {slot : Nat} {value : Coordinates W}
    (accepted : Coordinates.read values slot = some value) :
    values[2 * slot]? = some value.c0 ∧ values[2 * slot + 1]? = some value.c1 := by
  simp only [Coordinates.read, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at accepted
  obtain ⟨first, hf, second, hs, rfl⟩ := accepted
  exact ⟨hf, hs⟩

section Evaluation

variable {W : Type u} [Lean.Grind.CommRing W]

theorem step_polynomial {beta gamma injection next : Coordinates W} {stageCurrent : Array W}
    {lookups : List (W × List W)} {groupSize index : Nat} {result : Coordinates W}
    (accepted : step beta gamma injection next stageCurrent lookups groupSize index = some result) :
    ∃ source target, Coordinates.read stageCurrent index = some source ∧
      (if index + 1 < groupCount groupSize lookups.length then Coordinates.read stageCurrent (index + 1)
        else some (next + injection)) = some target ∧
      result = product ((compress beta gamma (chunk groupSize index lookups)).map Prod.snd) *
        (target - source) - numerator (compress beta gamma (chunk groupSize index lookups)) := by
  simp only [step, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨source, hs, accepted⟩ := accepted
  split at accepted
  next interior =>
    simp only [Option.bind_eq_some_iff] at accepted
    obtain ⟨target, ht, accepted⟩ := accepted
    cases accepted
    exact ⟨source, target, hs, by rw [if_pos interior]; exact ht, groupEquation_polynomial _ _⟩
  next final =>
    cases accepted
    exact ⟨source, next + injection, hs, by rw [if_neg final], groupEquation_polynomial _ _⟩

theorem step_defined (beta gamma injection next : Coordinates W) (stageCurrent : Array W)
    (lookups : List (W × List W)) (groupSize index : Nat)
    (width : groupCount groupSize lookups.length * 2 ≤ stageCurrent.size)
    (bounded : index < groupCount groupSize lookups.length) :
    ∃ result, step beta gamma injection next stageCurrent lookups groupSize index = some result := by
  obtain ⟨source, hs⟩ := read_coordinates_defined stageCurrent index (by omega)
  have target : ∃ target, (if index + 1 < groupCount groupSize lookups.length then
      Coordinates.read stageCurrent (index + 1) else some (next + injection)) = some target := by
    split
    next bound => exact read_coordinates_defined stageCurrent (index + 1) (by omega)
    next => exact ⟨_, rfl⟩
  obtain ⟨target, ht⟩ := target
  refine ⟨groupEquation (compress beta gamma (chunk groupSize index lookups)) (target - source), ?_⟩
  by_cases interior : index + 1 < groupCount groupSize lookups.length
  · rw [if_pos interior] at ht
    simp only [step, hs, if_pos interior, ht, bind, Option.bind_some, pure]
  · rw [if_neg interior] at ht
    have same := Option.some.inj ht
    simp only [step, hs, if_neg interior, same, bind, Option.bind_some, pure]

theorem equations_success {lookups : List (W × List W)} {stageCurrent stageNext publics deltaScaled : Array W}
    {isLast : W} {groupSize : Nat} {result : List (Coordinates W)}
    (accepted : equations lookups stageCurrent stageNext publics deltaScaled isLast groupSize = some result) :
    groupSize ≤ 8 ∧ ∃ beta gamma delta next,
      Coordinates.read publics 0 = some beta ∧ Coordinates.read publics 1 = some gamma ∧
      Coordinates.read deltaScaled 0 = some delta ∧ Coordinates.read stageNext 0 = some next ∧
      result.length = groupCount groupSize lookups.length ∧
      ∀ index, index < groupCount groupSize lookups.length → ∃ value,
        result[index]? = some value ∧
        step beta gamma (delta.scale isLast) next stageCurrent lookups groupSize index = some value := by
  unfold equations at accepted
  split at accepted
  next => cases accepted
  next bounded =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨beta, hb, gamma, hg, delta, hd, next, hn, steps⟩ := accepted
    obtain ⟨length, reads⟩ := mapM_some_reads steps
    refine ⟨by omega, beta, gamma, delta, next, hb, hg, hd, hn, ?_, ?_⟩
    · simpa only [List.length_range] using length
    · intro index bound
      exact reads index index (List.getElem?_range bound)

theorem equations_defined (lookups : List (W × List W)) (stageCurrent stageNext publics deltaScaled : Array W)
    (isLast : W) (groupSize : Nat) (bounded : groupSize ≤ 8)
    (currentWidth : groupCount groupSize lookups.length * 2 ≤ stageCurrent.size)
    (nextWidth : 2 ≤ stageNext.size) (publicWidth : 4 ≤ publics.size) (deltaWidth : 2 ≤ deltaScaled.size) :
    ∃ result, equations lookups stageCurrent stageNext publics deltaScaled isLast groupSize = some result := by
  obtain ⟨beta, hb⟩ := read_coordinates_defined publics 0 (by omega)
  obtain ⟨gamma, hg⟩ := read_coordinates_defined publics 1 (by omega)
  obtain ⟨delta, hd⟩ := read_coordinates_defined deltaScaled 0 (by omega)
  obtain ⟨next, hn⟩ := read_coordinates_defined stageNext 0 (by omega)
  obtain ⟨result, steps⟩ := mapM_defined (List.range (groupCount groupSize lookups.length))
    (step beta gamma (delta.scale isLast) next stageCurrent lookups groupSize)
    (fun index member => step_defined _ _ _ _ _ _ _ _ currentWidth (List.mem_range.mp member))
  exact ⟨result, by simp only [equations, if_neg (by omega : ¬8 < groupSize), hb, hg, hd, hn,
    bind, Option.bind_some, steps]⟩

theorem equations_zero {lookups : List (W × List W)} {stageCurrent stageNext publics deltaScaled : Array W}
    {isLast : W} {groupSize : Nat} {result : List (Coordinates W)}
    (accepted : equations lookups stageCurrent stageNext publics deltaScaled isLast groupSize = some result)
    (zero : ∀ value ∈ result, value = 0) :
    ∃ beta gamma delta next,
      Coordinates.read publics 0 = some beta ∧ Coordinates.read publics 1 = some gamma ∧
      Coordinates.read deltaScaled 0 = some delta ∧ Coordinates.read stageNext 0 = some next ∧
      ∀ index, index < groupCount groupSize lookups.length → ∃ source target,
        Coordinates.read stageCurrent index = some source ∧
        (if index + 1 < groupCount groupSize lookups.length then Coordinates.read stageCurrent (index + 1)
          else some (next + delta.scale isLast)) = some target ∧
        product ((compress beta gamma (chunk groupSize index lookups)).map Prod.snd) *
          (target - source) = numerator (compress beta gamma (chunk groupSize index lookups)) := by
  obtain ⟨_, beta, gamma, delta, next, hb, hg, hd, hn, _, steps⟩ := equations_success accepted
  refine ⟨beta, gamma, delta, next, hb, hg, hd, hn, ?_⟩
  intro index bound
  obtain ⟨value, valueRead, stepRead⟩ := steps index bound
  obtain ⟨source, target, hs, ht, equation⟩ := step_polynomial stepRead
  have vanishes := zero value (List.mem_of_getElem? valueRead)
  exact ⟨source, target, hs, ht, by rw [vanishes] at equation; grind⟩

theorem constraintValues_success {lookups : List Lookup} {nodeValues stageCurrent stageNext publics deltaScaled : Array W}
    {isLast : W} {groupSize : Nat} {result : List W}
    (accepted : constraintValues lookups nodeValues stageCurrent stageNext publics deltaScaled isLast groupSize = some result) :
    ∃ values coordinates, lookups.mapM (readLookup nodeValues) = some values ∧
      equations values stageCurrent stageNext publics deltaScaled isLast groupSize = some coordinates ∧
      result = Coordinates.flatten coordinates := by
  simp only [constraintValues, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at accepted
  obtain ⟨values, hv, coordinates, hc, rfl⟩ := accepted
  exact ⟨values, coordinates, hv, hc, rfl⟩

theorem constraintValues_length {lookups : List Lookup} {nodeValues stageCurrent stageNext publics deltaScaled : Array W}
    {isLast : W} {groupSize : Nat} {result : List W}
    (accepted : constraintValues lookups nodeValues stageCurrent stageNext publics deltaScaled isLast groupSize = some result) :
    result.length = 2 * groupCount groupSize lookups.length := by
  obtain ⟨values, coordinates, hv, hc, rfl⟩ := constraintValues_success accepted
  obtain ⟨_, _, _, _, _, _, _, _, _, length, _⟩ := equations_success hc
  rw [Coordinates.flatten_length, length, (mapM_some_reads hv).1]

theorem constraintValues_defined (lookups : List Lookup) (nodeValues stageCurrent stageNext publics deltaScaled : Array W)
    (isLast : W) (groupSize : Nat) (bounded : groupSize ≤ 8)
    (roots : ∀ lookup ∈ lookups, ∀ index ∈ lookup.roots, index < nodeValues.size)
    (currentWidth : groupCount groupSize lookups.length * 2 ≤ stageCurrent.size)
    (nextWidth : 2 ≤ stageNext.size) (publicWidth : 4 ≤ publics.size) (deltaWidth : 2 ≤ deltaScaled.size) :
    ∃ result, constraintValues lookups nodeValues stageCurrent stageNext publics deltaScaled isLast groupSize = some result := by
  obtain ⟨values, hv⟩ := mapM_defined lookups (readLookup nodeValues) (by
    intro lookup member
    obtain ⟨value, read, _⟩ := readLookup_defined nodeValues lookup (roots lookup member)
    exact ⟨value, read⟩)
  have lengths := (mapM_some_reads hv).1
  obtain ⟨coordinates, hc⟩ := equations_defined values stageCurrent stageNext publics deltaScaled isLast groupSize
    bounded (by simpa only [lengths] using currentWidth) nextWidth publicWidth deltaWidth
  exact ⟨Coordinates.flatten coordinates, by simp only [constraintValues, hv, hc, bind, Option.bind_some, pure]⟩

theorem constraintValues_reflect {ops : EvalOps W} {values : Values W} {trees : Array Expr} {buffer : Array W}
    (reflects : Reflects ops values trees buffer) (lookups : List Lookup)
    (stageCurrent stageNext publics deltaScaled : Array W) (isLast : W) (groupSize : Nat) :
    constraintValues lookups buffer stageCurrent stageNext publics deltaScaled isLast groupSize =
      (do let lookupValues ← lookups.mapM (evalLookup ops values trees)
          return Coordinates.flatten (← equations lookupValues stageCurrent stageNext publics deltaScaled isLast groupSize)) := by
  have same : readLookup buffer = evalLookup ops values trees := funext reflects.readLookup
  simp only [constraintValues, same]

end Evaluation
end Aiur.NativeAIR.LogUp
