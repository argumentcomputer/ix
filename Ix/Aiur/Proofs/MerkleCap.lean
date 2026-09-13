/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.MerkleCap
import Ix.Aiur.Proofs.ShapedVerifier

/-! Cap coverage puts every selected power-of-two matrix injection on the
authenticated path. Hash binding and native path replay remain separate.
-/

namespace Aiur.NativeAIR.MerkleCap

theorem maxDegree_nil : maxDegree [] = 0 := rfl

theorem maxDegree_cons (degree : Nat) (degrees : List Nat) :
    maxDegree (degree :: degrees) = max degree (maxDegree degrees) := rfl

theorem degree_le_max {degree : Nat} {degrees : List Nat} (member : degree ∈ degrees) :
    degree ≤ maxDegree degrees := by
  induction degrees with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rw [maxDegree_cons]
    rcases member with rfl | member
    · omega
    · have := ih member; omega

theorem maxDegree_le {degrees : List Nat} {bound : Nat}
    (bounded : ∀ degree ∈ degrees, degree ≤ bound) : maxDegree degrees ≤ bound := by
  induction degrees with
  | nil => exact Nat.zero_le _
  | cons degree rest ih =>
    have first := bounded degree (by simp)
    have tail := ih (fun d member => bounded d (by simp [member]))
    rw [maxDegree_cons]
    omega

theorem maxDegree_mono {selected degrees : List Nat}
    (subset : ∀ degree ∈ selected, degree ∈ degrees) : maxDegree selected ≤ maxDegree degrees :=
  maxDegree_le fun degree member => degree_le_max (subset degree member)

theorem coverage_iff {logBlowup capHeight : Nat} {degrees : List Nat} :
    coverage logBlowup capHeight degrees = true ↔
      ∀ degree ∈ degrees, min (capHeight - logBlowup) (maxDegree degrees) ≤ degree := by
  simp only [coverage, List.all_eq_true, decide_eq_true_eq]

theorem coverage_height_iff {logBlowup capHeight : Nat} {degrees : List Nat} :
    coverage logBlowup capHeight degrees = true ↔
      ∀ degree ∈ degrees,
        min capHeight (logBlowup + maxDegree degrees) ≤ logBlowup + degree := by
  rw [coverage_iff]
  constructor <;> intro covered degree member
  · have := covered degree member; omega
  · have := covered degree member; omega

theorem coverage_empty (logBlowup capHeight : Nat) : coverage logBlowup capHeight [] = true := rfl

theorem coverage_low_cap {logBlowup capHeight : Nat} (low : capHeight ≤ logBlowup)
    (degrees : List Nat) : coverage logBlowup capHeight degrees = true := by
  apply coverage_iff.mpr
  intro degree member
  omega

theorem coverage_uniform {logBlowup capHeight degree : Nat} {degrees : List Nat}
    (uniform : ∀ d ∈ degrees, d = degree) : coverage logBlowup capHeight degrees = true := by
  have bound : maxDegree degrees ≤ degree := maxDegree_le fun d member => by
    rw [uniform d member]
    exact Nat.le_refl _
  apply coverage_iff.mpr
  intro d member
  rw [uniform d member]
  omega

theorem coverage_subset {logBlowup capHeight : Nat} {degrees selected : List Nat}
    (covered : coverage logBlowup capHeight degrees = true)
    (subset : ∀ degree ∈ selected, degree ∈ degrees) :
    coverage logBlowup capHeight selected = true := by
  have bound := maxDegree_mono subset
  apply coverage_iff.mpr
  intro degree member
  have := coverage_iff.mp covered degree (subset degree member)
  omega

/-- The matrix is injected no later than the final authenticated path step.
Clamping the cap to the tree's depth is included in the right-hand side. -/
theorem coverage_injection {logBlowup capHeight : Nat} {degrees : List Nat}
    (covered : coverage logBlowup capHeight degrees = true) {degree : Nat}
    (member : degree ∈ degrees) :
    (logBlowup + maxDegree degrees) - (logBlowup + degree) ≤
      (logBlowup + maxDegree degrees) - min capHeight (logBlowup + maxDegree degrees) := by
  have := coverage_height_iff.mp covered degree member
  omega

theorem coverage_cap_size {logBlowup capHeight : Nat} {degrees : List Nat}
    (covered : coverage logBlowup capHeight degrees = true) {degree : Nat}
    (member : degree ∈ degrees) :
    2 ^ min capHeight (logBlowup + maxDegree degrees) ≤ 2 ^ (logBlowup + degree) :=
  Nat.pow_le_pow_right (by decide) (coverage_height_iff.mp covered degree member)

/-- A matrix omitted by the truncated walk must fail the coverage guard. -/
theorem omitted_rejected {logBlowup capHeight degree : Nat} {degrees : List Nat}
    (member : degree ∈ degrees)
    (omitted : (logBlowup + maxDegree degrees) - min capHeight (logBlowup + maxDegree degrees) <
      (logBlowup + maxDegree degrees) - (logBlowup + degree)) :
    coverage logBlowup capHeight degrees = false := by
  cases accepted : coverage logBlowup capHeight degrees with
  | false => rfl
  | true => have := coverage_injection accepted member; omega

theorem shorter_matrix_rejected : coverage 0 2 [3, 1] = false := by decide

theorem exact_injection_accepted : coverage 0 1 [3, 1] = true := by decide

theorem check_iff {key : KeyCodec.Key} {proof : ProofCodec.Data} :
    check key proof = true ↔
      ∀ degree ∈ proof.logDegrees,
        min key.parameters.capHeight
          (key.parameters.logBlowup + maxDegree (proof.logDegrees.map UInt8.toNat)) ≤
          key.parameters.logBlowup + degree.toNat := by
  simp only [check, coverage_height_iff, List.forall_mem_map]

theorem check_degree {key : KeyCodec.Key} {proof : ProofCodec.Data}
    (accepted : check key proof = true) {position : Nat} {degree : UInt8}
    (present : proof.logDegrees[position]? = some degree) :
    min key.parameters.capHeight
      (key.parameters.logBlowup + maxDegree (proof.logDegrees.map UInt8.toNat)) ≤
      key.parameters.logBlowup + degree.toNat :=
  check_iff.mp accepted degree (List.mem_of_getElem? present)

end Aiur.NativeAIR.MerkleCap

namespace Aiur.BoundVerifier

theorem CheckedProof.cap_coverage {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) :
    NativeAIR.MerkleCap.coverage key.parameters.logBlowup key.parameters.capHeight
      (checked.data.logDegrees.map UInt8.toNat) = true := checked.cap

theorem CheckedProof.row_cap {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) {position : Nat} {row : NativeAIR.ProofShape.Row}
    (present : checked.rows[position]? = some row) :
    min key.parameters.capHeight
      (key.parameters.logBlowup + NativeAIR.MerkleCap.maxDegree (checked.data.logDegrees.map UInt8.toNat)) ≤
      key.parameters.logBlowup + row.logDegree.toNat :=
  NativeAIR.MerkleCap.check_degree checked.cap (checked.row present).2.1.degree

theorem CheckedProof.row_injection {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) {position : Nat} {row : NativeAIR.ProofShape.Row}
    (present : checked.rows[position]? = some row) :
    (key.parameters.logBlowup + NativeAIR.MerkleCap.maxDegree (checked.data.logDegrees.map UInt8.toNat)) -
      (key.parameters.logBlowup + row.logDegree.toNat) ≤
      (key.parameters.logBlowup + NativeAIR.MerkleCap.maxDegree (checked.data.logDegrees.map UInt8.toNat)) -
        key.parameters.capHeight := by
  have := checked.row_cap present
  omega

theorem verifyShaped_cap {selection : Selection} {backend : CompiledBackend selection}
    {input : Array G} {bytes : ByteArray} (accepted : verifyShaped backend input bytes = .ok ()) :
    ∃ checked : CheckedProof backend.keyData bytes,
      readProof backend.keyData bytes = .ok checked ∧
      NativeAIR.MerkleCap.check backend.keyData checked.data = true := by
  obtain ⟨checked, parsed, _⟩ := verifyShaped_success accepted
  exact ⟨checked, parsed, checked.cap⟩

end Aiur.BoundVerifier
