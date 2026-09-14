/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofShape
import Ix.Aiur.Proofs.CompiledKey

/-! Shape acceptance supplies the actual selected opening records and their
checked dimensions. Polynomial authentication and trace satisfaction are
not assumed or concluded by these results. -/

namespace Aiur.NativeAIR.ProofShape

open ProofCodec (Data)

theorem pair_success {values : List (List ProofCodec.Extension)} {result : Pair}
    (accepted : pair values = some result) : values = [result.current, result.next] := by
  cases values with
  | nil => cases accepted
  | cons current rest =>
    cases rest with
    | nil => cases accepted
    | cons next rest =>
      cases rest with
      | nil => cases accepted; rfl
      | cons _ _ => cases accepted

theorem single_success {values : List α} {result : α} (accepted : single values = some result) :
    values = [result] := by
  cases values with
  | nil => cases accepted
  | cons value rest =>
    cases rest with
    | nil => cases accepted; rfl
    | cons _ _ => cases accepted

theorem readPreprocessed_none (proof : Data) : readPreprocessed proof none = some none := rfl

theorem readPreprocessed_some {proof : Data} {slot : Nat} {result : Option Pair}
    (accepted : readPreprocessed proof (some slot) = some result) :
    ∃ values opened, proof.preprocessed = some opened ∧
      opened[slot]? = some [values.current, values.next] ∧ result = some values := by
  simp only [readPreprocessed, Option.map_eq_some_iff, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨values, ⟨opened, hp, matrix, hm, hv⟩, rfl⟩ := accepted
  exact ⟨values, opened, hp, (pair_success hv) ▸ hm, rfl⟩

structure Row.Sourced (key : KeyCodec.Key) (proof : Data) (index position : Nat) (row : Row) : Prop where
  index_eq : row.circuitIndex = index
  circuit : key.circuits[index]? = some row.circuit
  degree : proof.logDegrees[position]? = some row.logDegree
  stage1 : proof.stage1[position]? = some [row.stage1.current, row.stage1.next]
  stage2 : proof.stage2[position]? = some [row.stage2.current, row.stage2.next]
  quotient : proof.quotient[position]? = some [row.quotient]
  accumulator : proof.accumulators[position]? = some row.accumulator
  preprocessed : ∃ slot, key.preprocessedIndices[index]? = some slot ∧
    readPreprocessed proof slot = some row.preprocessed

theorem readRow_success {key : KeyCodec.Key} {proof : Data} {index position : Nat} {row : Row}
    (accepted : readRow key proof index position = some row) : row.Sourced key proof index position := by
  simp only [readRow, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at accepted
  obtain ⟨circuit, hc, slot, hi, degree, hd, first, hf, firstPair, hfp,
    second, hs, secondPair, hsp, quotient, hq, singleQ, hqs, accumulator, ha,
    preprocessed, hp, rfl⟩ := accepted
  exact ⟨rfl, hc, hd, (pair_success hfp) ▸ hf, (pair_success hsp) ▸ hs,
    (single_success hqs) ▸ hq, ha, slot, hi, hp⟩

theorem Pair.hasWidth_success {values : Pair} {width : Nat} (accepted : values.hasWidth width = true) :
    values.current.length = width ∧ values.next.length = width := by
  simpa only [Pair.hasWidth, Bool.and_eq_true, beq_iff_eq] using accepted

structure Row.Fits (parameters : KeyCodec.Parameters) (row : Row) : Prop where
  stage1 : row.stage1.current.length = row.circuit.mainWidth ∧ row.stage1.next.length = row.circuit.mainWidth
  stage2 : row.stage2.current.length = row.circuit.widths.stage2 ∧ row.stage2.next.length = row.circuit.widths.stage2
  preprocessed : ∀ values, row.preprocessed = some values →
    values.current.length = row.circuit.preprocessedWidth ∧ values.next.length = row.circuit.preprocessedWidth
  quotient : row.quotient.length = quotientDegree row.circuit * 2
  degree : row.logDegree.toNat + (quotientDegree row.circuit).log2 ≤ 32 - parameters.logBlowup

theorem Row.fits_success {parameters : KeyCodec.Parameters} {row : Row} (accepted : row.fits parameters = true) :
    row.Fits parameters := by
  simp only [Row.fits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨⟨⟨⟨first, second⟩, preprocessed⟩, quotient⟩, degree⟩ := accepted
  refine ⟨Pair.hasWidth_success first, Pair.hasWidth_success second, ?_, quotient, degree⟩
  intro values present
  rw [present] at preprocessed
  exact Pair.hasWidth_success preprocessed

theorem check_success {key : KeyCodec.Key} {proof : Data} {result : List Row}
    (accepted : check key proof = some result) : header key proof = true ∧
    inactivePreprocessed key proof = true ∧ rows key proof = some result ∧
    ∀ row ∈ result, row.Fits key.parameters := by
  unfold check at accepted
  split at accepted
  next initial =>
    have initial' : header key proof = true ∧ inactivePreprocessed key proof = true := by
      simpa only [Bool.and_eq_true] using initial
    obtain ⟨header, inactive⟩ := initial'
    cases parsed : rows key proof with
    | none => simp [parsed, bind, Option.bind] at accepted
    | some entries =>
      simp only [parsed, bind, Option.bind_some] at accepted
      split at accepted
      next fits =>
        cases accepted
        exact ⟨header, inactive, rfl, fun row member => Row.fits_success (List.all_eq_true.mp fits row member)⟩
      next => cases accepted
  next => cases accepted

theorem check_length {key : KeyCodec.Key} {proof : Data} {result : List Row}
    (accepted : check key proof = some result) : result.length = (activeIndices proof).length := by
  have parsed := (check_success accepted).2.2.1
  have same := Bytecode.AIR.list_mapM_some_length _ _ _ parsed
  simpa only [List.length_zipIdx] using same

theorem activeIndices_mem {proof : Data} {index : Nat} :
    index ∈ activeIndices proof ↔ proof.active[index]? = some true := by
  unfold activeIndices
  constructor
  · intro member
    obtain ⟨⟨enabled, ci⟩, present, value⟩ := List.mem_filterMap.mp member
    cases enabled with
    | false => cases value
    | true =>
      cases value
      exact List.mk_mem_zipIdx_iff_getElem?.mp present
  · intro present
    exact List.mem_filterMap.mpr ⟨(true, index), List.mk_mem_zipIdx_iff_getElem?.mpr present, rfl⟩

theorem check_row {key : KeyCodec.Key} {proof : Data} {result : List Row}
    (accepted : check key proof = some result) {position : Nat} {row : Row}
    (present : result[position]? = some row) :
    ∃ index, (activeIndices proof)[position]? = some index ∧ row.Sourced key proof index position ∧ row.Fits key.parameters := by
  have parsed := (check_success accepted).2.2.1
  have read := OpEmitter.list_mapM_read parsed position
  rw [present] at read
  simp only [List.getElem?_zipIdx] at read
  cases located : (activeIndices proof)[position]? with
  | none => simp [located] at read
  | some index =>
    simp only [located, Option.map_some, bind, Option.bind_some, Nat.zero_add] at read
    exact ⟨index, rfl, readRow_success read,
      (check_success accepted).2.2.2 row (List.mem_of_getElem? present)⟩

theorem check_row_active {key : KeyCodec.Key} {proof : Data} {result : List Row}
    (accepted : check key proof = some result) {position : Nat} {row : Row}
    (present : result[position]? = some row) : proof.active[row.circuitIndex]? = some true := by
  obtain ⟨index, located, sourced, _⟩ := check_row accepted present
  rw [sourced.index_eq]
  exact activeIndices_mem.mp (List.mem_of_getElem? located)

theorem check_nonempty {key : KeyCodec.Key} {proof : Data} {result : List Row}
    (accepted : check key proof = some result) : result ≠ [] := by
  have lengths := check_length accepted
  have valid := (check_success accepted).1
  simp only [header, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at valid
  intro empty
  rw [empty] at lengths
  have positive : 0 < (activeIndices proof).length := valid.1.1.1.1.1.1.1.1.2
  simp only [List.length_nil] at lengths
  omega

theorem fixedHeights_sound {key : KeyCodec.Key} {proof : Data} (accepted : fixedHeights key proof = true) :
    FixedTraceHeights (key.circuits.map (·.preprocessedHeight)) proof.active (proof.logDegrees.map UInt8.toNat) :=
  fixedTraceHeights_sound accepted

theorem queryBound_sound {key : KeyCodec.Key} {proof : Data} {bound : Nat}
    (accepted : queryBound key proof = some bound) :
    ∃ total, lookupSlotSum (key.circuits.map (·.graph.lookups.length)) proof.active
      (proof.logDegrees.map UInt8.toNat) = some total ∧ bound = 1 + total ∧ bound < gSize.toNat :=
  (lookupQueryBound_sound accepted).2

end Aiur.NativeAIR.ProofShape
