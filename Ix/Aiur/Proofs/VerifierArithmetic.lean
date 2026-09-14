/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OpeningShape
import Ix.Aiur.Proofs.Quotient

/-! The complete opened-row arithmetic check has defined reads on a shaped
row from the selected compiled key. Acceptance reflects the graph's unfolded
expressions and the quotient identity at the supplied challenge. It does
not by itself imply individual constraints vanish on the trace domain.
-/

namespace Aiur.NativeAIR.VerifierArithmetic
open ProofCodec (Extension)

structure Evaluation.Reads (challenges : Challenges) (row : ProofShape.Row) (entering : Extension)
    (result : Evaluation) : Prop where
  domain : Domain.ofLogSize row.logDegree.toNat = some result.domain
  selectors : Domain.selectors result.domain challenges.zeta = some result.selectors
  nodes : row.circuit.graph.sweep Extension.evalOps (view challenges row entering result.selectors) = some result.nodeValues
  user : readNodes result.nodeValues row.circuit.graph.zeros = some result.userValues
  lookup : LogUp.constraintValues row.circuit.graph.lookups result.nodeValues
    (rowColumns row .stage2 .current) (rowColumns row .stage2 .next)
    (publics challenges entering row.accumulator) (deltaScaled result.domain entering row.accumulator)
    result.selectors.isLast row.circuit.lookupGroupSize = some result.lookupValues
  quotient : Quotient.evaluate result.domain challenges.zeta row.quotient = some result.quotientValue

theorem evaluate_success {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (accepted : evaluate challenges row entering = some result) :
    result.Reads challenges row entering := by
  simp only [evaluate, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
  obtain ⟨domain, hd, selectors, hs, nodes, hn, user, hu, lookup, hl, quotient, hq, rfl⟩ := accepted
  exact ⟨hd, hs, hn, hu, hl, hq⟩

theorem Evaluation.Reads.evaluate {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (reads : result.Reads challenges row entering) :
    evaluate challenges row entering = some result := by
  simp only [VerifierArithmetic.evaluate, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  exact ⟨result.domain, reads.domain, result.selectors, reads.selectors, result.nodeValues, reads.nodes,
    result.userValues, reads.user, result.lookupValues, reads.lookup, result.quotientValue, reads.quotient, rfl⟩

theorem evaluate_defined {parameters : KeyCodec.Parameters} {row : ProofShape.Row}
    (fits : row.Fits parameters) (valid : row.circuit.valid = true)
    (absent : row.preprocessed = none → row.circuit.preprocessedWidth = 0)
    (challenges : Challenges) (entering : Extension) {domain : Domain.Subgroup}
    (domainRead : Domain.ofLogSize row.logDegree.toNat = some domain)
    (nonzero : Domain.vanishing domain challenges.zeta ≠ 0) :
    ∃ result, evaluate challenges row entering = some result := by
  obtain ⟨positive, bounded, graphValid, _⟩ := KeyCodec.Circuit.valid_graph valid
  obtain ⟨selectors, selectorsRead⟩ := Domain.selectors_defined domain challenges.zeta nonzero
  let values := view challenges row entering selectors
  obtain ⟨nodes, swept, length⟩ := graphValid.sweep_defined Extension.evalOps values
    (view_fits fits absent challenges entering selectors)
  obtain ⟨user, userRead, _⟩ := readNodes_defined nodes row.circuit.graph.zeros (by
    intro index member; rw [length]; exact graphValid.zeros index member)
  have widths := stage2_width fits positive
  obtain ⟨lookup, lookupRead⟩ := LogUp.constraintValues_defined row.circuit.graph.lookups nodes
    (rowColumns row .stage2 .current) (rowColumns row .stage2 .next)
    (publics challenges entering row.accumulator) (deltaScaled domain entering row.accumulator)
    selectors.isLast row.circuit.lookupGroupSize bounded
    (by intro lookup member index root
        rw [length]
        exact graphValid.lookups index (List.mem_flatMap.mpr ⟨lookup, member, root⟩))
    widths.1 widths.2 (by rw [publics_size]; decide) (by rw [deltaScaled_size]; decide)
  obtain ⟨coefficients, coefficientRead⟩ := Quotient.coefficients_defined row.quotient (by rw [fits.quotient]; omega)
  refine ⟨⟨domain, selectors, nodes, user, lookup, Quotient.horner (challenges.zeta.power (Domain.size domain)) coefficients⟩,
    Evaluation.Reads.evaluate ⟨domainRead, selectorsRead, swept, userRead, lookupRead, ?_⟩⟩
  simp only [Quotient.evaluate, coefficientRead, bind, pure, Option.bind_some]

theorem evaluate_defined_iff {parameters : KeyCodec.Parameters} {row : ProofShape.Row}
    (fits : row.Fits parameters) (valid : row.circuit.valid = true)
    (absent : row.preprocessed = none → row.circuit.preprocessedWidth = 0)
    (challenges : Challenges) (entering : Extension) :
    (∃ result, evaluate challenges row entering = some result) ↔
      ∃ domain, Domain.ofLogSize row.logDegree.toNat = some domain ∧ Domain.vanishing domain challenges.zeta ≠ 0 := by
  constructor
  · rintro ⟨result, evaluated⟩
    have reads := evaluate_success evaluated
    exact ⟨result.domain, reads.domain, (Domain.selectors_defined_iff _ _).mp ⟨result.selectors, reads.selectors⟩⟩
  · rintro ⟨domain, read, nonzero⟩
    exact evaluate_defined fits valid absent challenges entering read nonzero

theorem evaluate_constraint_count {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (accepted : evaluate challenges row entering = some result)
    (positive : 0 < row.circuit.lookupGroupSize) :
    result.constraints.length = row.circuit.constraintCount := by
  have reads := evaluate_success accepted
  have user := Bytecode.AIR.list_mapM_some_length _ _ _ reads.user
  have lookup := LogUp.constraintValues_length reads.lookup
  simp only [Evaluation.constraints, List.length_append, KeyCodec.Circuit.constraintCount,
    user, lookup, LogUp.groupCount_key row.circuit positive]
  omega

theorem evaluate_reflects {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (accepted : evaluate challenges row entering = some result)
    (valid : row.circuit.graph.Valid row.circuit.widths) :
    ∃ trees lookups coordinates,
      row.circuit.graph.unfold = some trees ∧
      Reflects Extension.evalOps (view challenges row entering result.selectors) trees result.nodeValues ∧
      evalRoots Extension.evalOps (view challenges row entering result.selectors) trees row.circuit.graph.zeros =
        some result.userValues ∧
      row.circuit.graph.lookups.mapM (evalLookup Extension.evalOps (view challenges row entering result.selectors) trees) =
        some lookups ∧
      LogUp.equations lookups (rowColumns row .stage2 .current) (rowColumns row .stage2 .next)
        (publics challenges entering row.accumulator) (deltaScaled result.domain entering row.accumulator)
        result.selectors.isLast row.circuit.lookupGroupSize = some coordinates ∧
      result.lookupValues = LogUp.Coordinates.flatten coordinates := by
  have reads := evaluate_success accepted
  obtain ⟨trees, unfolded, _⟩ := valid.unfold_defined
  have reflected := row.circuit.graph.sweep_reflects Extension.evalOps _ unfolded reads.nodes
  obtain ⟨lookups, coordinates, lookupRead, equationsRead, equal⟩ := LogUp.constraintValues_success reads.lookup
  have same : readLookup result.nodeValues =
      evalLookup Extension.evalOps (view challenges row entering result.selectors) trees :=
    funext reflected.readLookup
  exact ⟨trees, lookups, coordinates, unfolded, reflected,
    (reflected.readNodes _).symm.trans reads.user, same ▸ lookupRead, equationsRead, equal⟩

theorem Evaluation.Reads.identity {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (reads : result.Reads challenges row entering) :
    result.accepts challenges.alpha = true ↔
      Quotient.composition challenges.alpha result.constraints =
        Domain.vanishing result.domain challenges.zeta * result.quotientValue := by
  have invert := (Domain.selectors_success _ _ _ reads.selectors).2.2.2
  simp only [Evaluation.accepts, beq_iff_eq]
  exact Quotient.inverse_check _ _ _ _ invert

theorem check_true_iff (challenges : Challenges) (row : ProofShape.Row) (entering : Extension) :
    check challenges row entering = some true ↔
      ∃ result, evaluate challenges row entering = some result ∧
        Quotient.composition challenges.alpha result.constraints =
          Domain.vanishing result.domain challenges.zeta * result.quotientValue := by
  simp only [check, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨result, read, accepted⟩
    exact ⟨result, read, (evaluate_success read).identity.mp accepted⟩
  · rintro ⟨result, read, identity⟩
    exact ⟨result, read, (evaluate_success read).identity.mpr identity⟩

theorem check_quotient {challenges : Challenges} {row : ProofShape.Row} {entering : Extension}
    {result : Evaluation} (evaluated : evaluate challenges row entering = some result) :
    check challenges row entering =
      Quotient.check result.domain challenges.zeta challenges.alpha result.constraints row.quotient := by
  have reads := evaluate_success evaluated
  simp only [check, evaluated, Quotient.check, reads.selectors, reads.quotient, Evaluation.accepts,
    bind, pure, Option.bind_some]

end Aiur.NativeAIR.VerifierArithmetic

namespace Aiur.BoundVerifier
open NativeAIR

theorem CompiledBackend.checked_row_arithmetic {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes) {position : Nat} {row : ProofShape.Row}
    (present : checked.rows[position]? = some row)
    (challenges : VerifierArithmetic.Challenges) (entering : ProofCodec.Extension) :
    ∃ domain, Domain.ofLogSize row.logDegree.toNat = some domain ∧
      ((∃ result, VerifierArithmetic.evaluate challenges row entering = some result) ↔
        Domain.vanishing domain challenges.zeta ≠ 0) := by
  obtain ⟨_, sourced, fits⟩ := checked.row present
  obtain ⟨domain, domainRead⟩ := VerifierArithmetic.domain_defined fits
  have valid := (KeyCodec.decode_valid backend.toBackend.key_decodes).1 row.circuit
    (List.mem_of_getElem? sourced.circuit)
  refine ⟨domain, domainRead, ?_⟩
  rw [VerifierArithmetic.evaluate_defined_iff fits valid (backend.row_preprocessed_absent sourced)]
  constructor
  · rintro ⟨other, otherRead, nonzero⟩
    cases Option.some.inj (domainRead.symm.trans otherRead)
    exact nonzero
  · intro nonzero; exact ⟨domain, domainRead, nonzero⟩

end Aiur.BoundVerifier
