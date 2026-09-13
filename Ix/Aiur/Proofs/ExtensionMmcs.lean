/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ExtensionMmcs
import Ix.Aiur.Proofs.PrunedMerkle

/-! Extension-coordinate packing and its authenticated row correspondence. -/

namespace Aiur.NativeAIR.ExtensionMmcs

open Merkle (Digest Hash Dimensions)
open ProofCodec (Extension)

theorem baseRow_length (values : List Extension) : (baseRow values).length = values.length * 2 := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [baseRow, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons] at ih ⊢
    omega

theorem baseRow_injective {left right : List Extension} (same : baseRow left = baseRow right) : left = right := by
  induction left generalizing right with
  | nil =>
    have count := congrArg List.length same
    rw [baseRow_length, baseRow_length] at count
    have empty : right.length = 0 := by simp only [List.length_nil] at count; omega
    exact (List.eq_nil_of_length_eq_zero empty).symm
  | cons value values ih =>
    cases right with
    | nil =>
      have count := congrArg List.length same
      rw [baseRow_length, baseRow_length] at count
      simp only [List.length_cons, List.length_nil] at count
      omega
    | cons other others =>
      simp only [baseRow, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at same
      have rowEq : value = other := by
        cases value
        cases other
        simp only [Extension.mk.injEq]
        exact ⟨same.1, same.2.1⟩
      rw [rowEq, ih same.2.2]

theorem baseRows_length (rows : List (List Extension)) : (baseRows rows).length = rows.length :=
  List.length_map _

theorem baseRows_injective {left right : List (List Extension)} (same : baseRows left = baseRows right) : left = right := by
  induction left generalizing right with
  | nil =>
    have count := congrArg List.length same
    rw [baseRows_length, baseRows_length] at count
    exact (List.eq_nil_of_length_eq_zero count.symm).symm
  | cons row rows ih =>
    cases right with
    | nil => simp only [baseRows, List.map_cons, List.map_nil, List.cons_ne_nil] at same
    | cons other others =>
      simp only [baseRows, List.map_cons, List.cons.injEq] at same
      rw [baseRow_injective same.1, ih same.2]

theorem baseRows_fields (rows : List (List Extension)) :
    (baseRows rows).flatten.length = rows.flatten.length * 2 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [baseRows, List.map_cons, List.flatten_cons, List.length_append, baseRow_length] at ih ⊢
    omega

theorem baseDimensions_length (wordBits : Nat) (dimensions : List Dimensions) :
    (baseDimensions wordBits dimensions).length = dimensions.length := List.length_map _

theorem baseDimensions_heights (wordBits : Nat) (dimensions : List Dimensions) :
    (baseDimensions wordBits dimensions).map Dimensions.logHeight = dimensions.map Dimensions.logHeight := by
  simp only [baseDimensions, List.map_map, Function.comp_def]

theorem baseDimensions_maxHeight (wordBits : Nat) (dimensions : List Dimensions) :
    Merkle.maxHeight (baseDimensions wordBits dimensions) = Merkle.maxHeight dimensions := by
  simp only [Merkle.maxHeight, baseDimensions_heights]

theorem baseDimensions_covered (wordBits : Nat) (dimensions : List Dimensions) (capHeight : Nat) :
    Merkle.covered (baseDimensions wordBits dimensions) capHeight = Merkle.covered dimensions capHeight := by
  simp only [Merkle.covered, baseDimensions_heights]

theorem baseDimensions_exact {wordBits : Nat} {dimensions : List Dimensions} (bounded : WidthsFit wordBits dimensions) :
    baseDimensions wordBits dimensions = dimensions.map (fun dimension => { dimension with width := dimension.width * 2 }) := by
  apply List.map_congr_left
  intro dimension member
  simp only [Nat.mod_eq_of_lt (bounded dimension member)]

theorem shape_base {wordBits : Nat} {dimensions : List Dimensions} {rows : List (List Extension)}
    (bounded : WidthsFit wordBits dimensions) :
    Merkle.shape (baseDimensions wordBits dimensions) (baseRows rows) = shape dimensions rows := by
  rw [baseDimensions_exact bounded]
  induction dimensions generalizing rows with
  | nil => cases rows <;> rfl
  | cons dimension dimensions ih =>
    have tailBound : WidthsFit wordBits dimensions :=
      fun child member => bounded child (List.mem_cons.mpr (Or.inr member))
    cases rows with
    | nil => rfl
    | cons row rows =>
      have count : ((baseRow row).length == dimension.width * 2) = (row.length == dimension.width) := by
        rw [baseRow_length]
        have equality : (row.length * 2 = dimension.width * 2) ↔ row.length = dimension.width := by omega
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using equality
      change (((baseRow row).length == dimension.width * 2) &&
        Merkle.shape (dimensions.map (fun dimension => { dimension with width := dimension.width * 2 }))
          (baseRows rows)) = ((row.length == dimension.width) && shape dimensions rows)
      rw [count, ih tailBound]

theorem fri_width_fits {logArity height : Nat} (bounded : logArity ≤ 32) :
    WidthsFit 64 [⟨2^logArity, height⟩] := by
  intro dimension member
  obtain rfl := List.mem_singleton.mp member
  change 2^logArity * 2 < 2^64
  rw [← Nat.pow_succ]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem baseRows_query {indices : List Nat} {rows : List (List (List Extension))}
    {index : Nat} {query : List (List Extension)} (member : (index, query) ∈ indices.zip rows) :
    (index, baseRows query) ∈ indices.zip (rows.map baseRows) := by
  rw [List.zip_map_right]
  exact List.mem_map.mpr ⟨(index, query), member, rfl⟩

theorem replay_shape {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {rows : List (List Extension)} {proof : List Digest} {result : Merkle.Replay}
    (bounded : WidthsFit wordBits dimensions)
    (success : replay hash wordBits dimensions capHeight index rows proof = some result) :
    shape dimensions rows = true := by
  have fits := (Merkle.replay_success success).2.1
  rwa [shape_base bounded] at fits

theorem verifyMulti_individual {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {indices : List Nat} {cap : List Digest} {rows : List (List (List Extension))} {query : List (List Extension)}
    {proof : List Digest}
    (accepted : verifyMulti hash wordBits dimensions capHeight indices cap rows proof = true)
    (member : (index, query) ∈ indices.zip rows) :
    ∃ path result, replay hash wordBits dimensions capHeight index query path = some result ∧
      verify hash wordBits dimensions capHeight index cap query path = true ∧
      result.hashing.inputs ⊆ (replayMulti hash wordBits dimensions capHeight indices rows proof).inputs :=
  PrunedMerkle.verify_individual accepted (baseRows_query member)

theorem verifyMulti_shape {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {indices : List Nat} {cap : List Digest} {rows : List (List (List Extension))} {query : List (List Extension)}
    {proof : List Digest}
    (bounded : WidthsFit wordBits dimensions)
    (accepted : verifyMulti hash wordBits dimensions capHeight indices cap rows proof = true)
    (member : (index, query) ∈ indices.zip rows) : shape dimensions query = true := by
  obtain ⟨_, _, result, _, _⟩ := verifyMulti_individual accepted member
  exact replay_shape bounded result

theorem verifyMultiCovered_individual {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {indices : List Nat} {cap : List Digest} {rows : List (List (List Extension))} {query : List (List Extension)}
    {proof : List Digest}
    (accepted : verifyMultiCovered hash wordBits dimensions capHeight indices cap rows proof = true)
    (member : (index, query) ∈ indices.zip rows) :
    ∃ path result, replay hash wordBits dimensions capHeight index query path = some result ∧
      verifyCovered hash wordBits dimensions capHeight index cap query path = true ∧
      result.hashing.inputs ⊆ (replayMulti hash wordBits dimensions capHeight indices rows proof).inputs := by
  simp only [verifyMultiCovered, Bool.and_eq_true] at accepted
  obtain ⟨path, result, evaluated, verified, subset⟩ := verifyMulti_individual accepted.2 member
  exact ⟨path, result, evaluated, by simp only [verifyCovered, accepted.1, verified, Bool.and_self], subset⟩

theorem replay_native_input {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {rows : List (List Extension)} {proof : List Digest} {result : Merkle.Replay}
    (success : replay hash wordBits dimensions capHeight index rows proof = some result)
    (bounded : rows.flatten.length < 2^60) {input : List UInt8} (member : input ∈ result.hashing.inputs) :
    Blake3.NativeInput input := by
  have baseBound : (baseRows rows).flatten.length < 2^61 := by rw [baseRows_fields]; omega
  exact Merkle.replay_native_input success baseBound member

theorem verifyCovered_collision {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {cap : List Digest} {leftRows rightRows : List (List Extension)} {leftProof rightProof : List Digest}
    (left : verifyCovered hash wordBits dimensions capHeight index cap leftRows leftProof = true)
    (right : verifyCovered hash wordBits dimensions capHeight index cap rightRows rightProof = true)
    (different : leftRows ≠ rightRows) :
    ∃ left right, replay hash wordBits dimensions capHeight index leftRows leftProof = some left ∧
      replay hash wordBits dimensions capHeight index rightRows rightProof = some right ∧
      Merkle.CollisionOn hash (left.hashing.inputs ++ right.hashing.inputs) ∧
      (left.hashing.inputs ++ right.hashing.inputs).length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) := by
  simp only [verifyCovered, Bool.and_eq_true] at left right
  have coverage : Merkle.covered (baseDimensions wordBits dimensions) capHeight = true := by
    simpa only [baseDimensions_covered] using left.1
  have distinct : baseRows leftRows ≠ baseRows rightRows := fun same => different (baseRows_injective same)
  simpa only [replay, baseDimensions_maxHeight] using Merkle.verify_collision coverage left.2 right.2 distinct

theorem verifyMultiCovered_collision {hash : Hash} {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List Extension))} {leftQuery rightQuery : List (List Extension)}
    {leftProof rightProof : List Digest}
    (left : verifyMultiCovered hash wordBits dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verifyMultiCovered hash wordBits dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery) :
    ∃ inputs,
      inputs ⊆ (replayMulti hash wordBits dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replayMulti hash wordBits dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn hash inputs ∧ inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, input.length ≤ max 64 (16 * max leftQuery.flatten.length rightQuery.flatten.length) := by
  simp only [verifyMultiCovered, Bool.and_eq_true] at left right
  have coverage : Merkle.covered (baseDimensions wordBits dimensions) capHeight = true := by
    simpa only [baseDimensions_covered] using left.1
  have distinct : baseRows leftQuery ≠ baseRows rightQuery := fun same => different (baseRows_injective same)
  obtain ⟨inputs, subset, collision, count, bytes⟩ := PrunedMerkle.verify_collision coverage left.2 right.2
    (baseRows_query leftMember) (baseRows_query rightMember) distinct
  refine ⟨inputs, subset, collision, ?_, ?_⟩
  · simpa only [baseDimensions_maxHeight] using count
  · intro input member
    have bounded := bytes input member
    rw [baseRows_fields, baseRows_fields] at bounded
    omega

theorem blake3_native_collision {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {cap : List Digest} {leftRows rightRows : List (List Extension)} {leftProof rightProof : List Digest}
    (left : verifyCovered Blake3.digest wordBits dimensions capHeight index cap leftRows leftProof = true)
    (right : verifyCovered Blake3.digest wordBits dimensions capHeight index cap rightRows rightProof = true)
    (different : leftRows ≠ rightRows)
    (leftBound : leftRows.flatten.length < 2^60) (rightBound : rightRows.flatten.length < 2^60) :
    ∃ left right, replay Blake3.digest wordBits dimensions capHeight index leftRows leftProof = some left ∧
      replay Blake3.digest wordBits dimensions capHeight index rightRows rightProof = some right ∧
      Merkle.CollisionOn Blake3.digest (left.hashing.inputs ++ right.hashing.inputs) ∧
      (left.hashing.inputs ++ right.hashing.inputs).length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ left.hashing.inputs ++ right.hashing.inputs, Blake3.NativeInput input := by
  obtain ⟨left, right, leftReplay, rightReplay, collision, count⟩ := verifyCovered_collision left right different
  refine ⟨left, right, leftReplay, rightReplay, collision, count, ?_⟩
  intro input member
  exact (List.mem_append.mp member).elim (replay_native_input leftReplay leftBound)
    (replay_native_input rightReplay rightBound)

theorem blake3_multi_native_collision {wordBits capHeight index : Nat} {dimensions : List Dimensions}
    {leftIndices rightIndices : List Nat} {cap : List Digest}
    {leftRows rightRows : List (List (List Extension))} {leftQuery rightQuery : List (List Extension)}
    {leftProof rightProof : List Digest}
    (left : verifyMultiCovered Blake3.digest wordBits dimensions capHeight leftIndices cap leftRows leftProof = true)
    (right : verifyMultiCovered Blake3.digest wordBits dimensions capHeight rightIndices cap rightRows rightProof = true)
    (leftMember : (index, leftQuery) ∈ leftIndices.zip leftRows)
    (rightMember : (index, rightQuery) ∈ rightIndices.zip rightRows)
    (different : leftQuery ≠ rightQuery)
    (leftBound : leftQuery.flatten.length < 2^60) (rightBound : rightQuery.flatten.length < 2^60) :
    ∃ inputs,
      inputs ⊆ (replayMulti Blake3.digest wordBits dimensions capHeight leftIndices leftRows leftProof).inputs ++
        (replayMulti Blake3.digest wordBits dimensions capHeight rightIndices rightRows rightProof).inputs ∧
      Merkle.CollisionOn Blake3.digest inputs ∧ inputs.length ≤ 2 + 6 * (Merkle.maxHeight dimensions - capHeight) ∧
      ∀ input ∈ inputs, Blake3.NativeInput input := by
  obtain ⟨inputs, subset, collision, count, bytes⟩ := verifyMultiCovered_collision left right leftMember rightMember different
  refine ⟨inputs, subset, collision, count, ?_⟩
  intro input member
  have := bytes input member
  unfold Blake3.NativeInput
  omega

end Aiur.NativeAIR.ExtensionMmcs
