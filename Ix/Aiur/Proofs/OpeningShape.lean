/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.VerifierArithmetic
import Ix.Aiur.Proofs.ShapedVerifier
import Ix.Aiur.Proofs.Selectors
import Ix.Aiur.Proofs.LogUp

/-! The selected compiled key supplies the missing preprocessed-slot
invariant. Together with checked proof shape it gives the complete graph
view, lookup widths and valid logarithmic trace domain.
-/

namespace Aiur.NativeAIR.CompiledKey

theorem preprocessedIndices_none (program : Bytecode.Toplevel) (index : Nat) :
    (preprocessedIndices program)[index]? = some none ↔
      index < program.circuits.size + program.memorySizes.size := by
  unfold preprocessedIndices
  by_cases inside : index < program.circuits.size + program.memorySizes.size
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using inside)]
    simp only [List.getElem?_replicate, inside, if_true]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt inside)]
    simp only [List.length_replicate]
    constructor
    · intro present
      have member := List.mem_of_getElem? present
      simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or] at member
    · intro bound; exact False.elim (inside bound)

theorem circuits_preprocessed_absent {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) {index : Nat} {artifact : KeyCodec.Circuit}
    (selected : result[index]? = some artifact)
    (absent : (preprocessedIndices program)[index]? = some none) : artifact.preprocessedWidth = 0 := by
  have bound := (preprocessedIndices_none program index).mp absent
  by_cases first : index < program.circuits.size
  · have source := Array.getElem?_eq_getElem first
    obtain ⟨_, _, _, _, width, _, _⟩ := functionCircuit_success (circuits_function built source selected)
    exact width
  · have memory : index - program.circuits.size < program.memorySizes.size := by omega
    have source := Array.getElem?_eq_getElem memory
    have equal : program.circuits.size + (index - program.circuits.size) = index := by omega
    have compiled := circuits_memory built source (equal ▸ selected)
    obtain ⟨_, _, _, _, width, _, _⟩ := memoryCircuit_success compiled
    exact width

end Aiur.NativeAIR.CompiledKey

namespace Aiur.BoundVerifier
open NativeAIR

theorem CompiledBackend.row_preprocessed_absent {selection : Selection}
    (backend : CompiledBackend selection) {proof : ProofCodec.Data} {index position : Nat}
    {row : ProofShape.Row} (sourced : row.Sourced backend.keyData proof index position)
    (absent : row.preprocessed = none) : row.circuit.preprocessedWidth = 0 := by
  obtain ⟨slot, present, read⟩ := sourced.preprocessed
  cases slot with
  | none =>
    rw [backend.preprocessed_indices] at present
    exact CompiledKey.circuits_preprocessed_absent backend.circuits_bound sourced.circuit present
  | some slot =>
    obtain ⟨_, _, _, _, someRow⟩ := ProofShape.readPreprocessed_some read
    rw [absent] at someRow
    cases someRow

end Aiur.BoundVerifier

namespace Aiur.NativeAIR.VerifierArithmetic
open ProofCodec (Extension)
open LogUp (Coordinates)

theorem publics_size (challenges : Challenges) (entering leaving : Extension) :
    (publics challenges entering leaving).size = 8 := rfl

theorem publics_beta (challenges : Challenges) (entering leaving : Extension) :
    Coordinates.read (publics challenges entering leaving) 0 =
      some ((Coordinates.fromExtension challenges.beta).map Extension.ofBase) := rfl

theorem publics_gamma (challenges : Challenges) (entering leaving : Extension) :
    Coordinates.read (publics challenges entering leaving) 1 =
      some ((Coordinates.fromExtension challenges.gamma).map Extension.ofBase) := rfl

theorem publics_entering (challenges : Challenges) (entering leaving : Extension) :
    Coordinates.read (publics challenges entering leaving) 2 =
      some ((Coordinates.fromExtension entering).map Extension.ofBase) := rfl

theorem publics_leaving (challenges : Challenges) (entering leaving : Extension) :
    Coordinates.read (publics challenges entering leaving) 3 =
      some ((Coordinates.fromExtension leaving).map Extension.ofBase) := rfl

theorem deltaScaled_size (domain : Domain.Subgroup) (entering leaving : Extension) :
    (deltaScaled domain entering leaving).size = 2 := rfl

theorem deltaScaled_coordinates (domain : Domain.Subgroup) (entering leaving : Extension) :
    Coordinates.read (deltaScaled domain entering leaving) 0 =
      some (((Coordinates.fromExtension (leaving - entering)).scale (Domain.normalizer domain).inverse).map
        Extension.ofBase) := by
  change some (⟨(Extension.ofBase leaving.c0 - Extension.ofBase entering.c0) *
      Extension.ofBase (Domain.normalizer domain).inverse,
    (Extension.ofBase leaving.c1 - Extension.ofBase entering.c1) *
      Extension.ofBase (Domain.normalizer domain).inverse⟩ : Coordinates Extension) =
    some ⟨Extension.ofBase ((leaving.c0 - entering.c0) * (Domain.normalizer domain).inverse),
      Extension.ofBase ((leaving.c1 - entering.c1) * (Domain.normalizer domain).inverse)⟩
  rw [Extension.ofBase_mul, Extension.ofBase_mul, Extension.ofBase_sub, Extension.ofBase_sub]

theorem view_fits {parameters : KeyCodec.Parameters} {row : ProofShape.Row}
    (fits : row.Fits parameters) (absent : row.preprocessed = none → row.circuit.preprocessedWidth = 0)
    (challenges : Challenges) (entering : Extension) (selectors : Domain.Selectors Extension) :
    (view challenges row entering selectors).Fits row.circuit.widths := by
  refine ⟨?_, rfl⟩
  intro source offset
  cases source with
  | main => cases offset <;> simp only [view, rowColumns, pairColumns, List.size_toArray,
      KeyCodec.Circuit.widths, GraphWidths.width, fits.stage1]
  | stage2 =>
    cases offset with
    | current => exact fits.stage2.1
    | next => exact fits.stage2.2
  | preprocessed =>
    cases selected : row.preprocessed with
    | none => simp only [view, rowColumns, selected, Array.size_empty, KeyCodec.Circuit.widths,
        GraphWidths.width, absent selected]
    | some pair =>
      have dimensions := fits.preprocessed pair selected
      cases offset <;> simp only [view, rowColumns, selected, pairColumns, List.size_toArray,
        KeyCodec.Circuit.widths, GraphWidths.width, dimensions]

theorem domain_defined {parameters : KeyCodec.Parameters} {row : ProofShape.Row} (fits : row.Fits parameters) :
    ∃ domain, Domain.ofLogSize row.logDegree.toNat = some domain := by
  have bounded : row.logDegree.toNat < 33 := by have := fits.degree; omega
  exact ⟨⟨row.logDegree.toNat, bounded⟩, by simp only [Domain.ofLogSize, dif_pos bounded]⟩

theorem stage2_width {parameters : KeyCodec.Parameters} {row : ProofShape.Row} (fits : row.Fits parameters)
    (positive : 0 < row.circuit.lookupGroupSize) :
    LogUp.groupCount row.circuit.lookupGroupSize row.circuit.graph.lookups.length * 2 ≤
      (rowColumns row .stage2 .current).size ∧ 2 ≤ (rowColumns row .stage2 .next).size := by
  simp only [rowColumns, pairColumns, List.size_toArray, fits.stage2, KeyCodec.Circuit.widths,
    ← LogUp.groupCount_key row.circuit positive]
  have := LogUp.groupCount_positive row.circuit.lookupGroupSize row.circuit.graph.lookups.length
  omega

end Aiur.NativeAIR.VerifierArithmetic
