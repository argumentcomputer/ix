/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.VerifierArithmetic
import Ix.Aiur.Proofs.DomainAccumulator

/-! Public claims initialize the positive sum of inverse compressed messages.
Ordered active rows use consecutive accumulator values and finish at zero.
These are arithmetic facts with explicit challenges, without a transcript
or polynomial-authentication assumption disguised as a conclusion.
-/

namespace Aiur.NativeAIR.VerifierArithmetic
open ProofCodec (Extension)
open LogUp (Coordinates)

theorem claimMessage_native (challenges : Challenges) (claim : List G) :
    claimMessage challenges claim = challenges.beta +
      claim.foldr (fun arg accumulated => accumulated * challenges.gamma + Extension.ofBase arg) 0 := by
  rw [claimMessage, LogUp.fingerprint_toExtension]
  rfl

def publicEntries (challenges : Challenges) (claims : List (List G)) : List (Extension × Extension) :=
  claims.map fun claim => (1, claimMessage challenges claim)

theorem publicEntries_compress (challenges : Challenges) (claims : List (List G)) :
    LogUp.fieldEntries (LogUp.compress (Coordinates.fromExtension challenges.beta)
      (Coordinates.fromExtension challenges.gamma) (claims.map fun claim => (1, claim))) =
      publicEntries challenges claims := by
  simp only [LogUp.fieldEntries, LogUp.compress, publicEntries, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro claim _
  change ((1 : Extension), (LogUp.fingerprint (Coordinates.fromExtension challenges.gamma) claim +
    Coordinates.fromExtension challenges.beta).toExtension) = (1, claimMessage challenges claim)
  rw [Coordinates.toExtension_add, claimMessage]
  change ((1 : Extension), _ + challenges.beta) = (1, challenges.beta + _)
  rw [Extension.add_comm]

theorem initialAccumulator_nil (challenges : Challenges) : initialAccumulator challenges [] = some 0 := rfl

theorem initialAccumulator_cons (challenges : Challenges) (claim : List G) (claims : List (List G)) :
    initialAccumulator challenges (claim :: claims) = do
      let inverse ← (claimMessage challenges claim).tryInverse
      let rest ← initialAccumulator challenges claims
      return inverse + rest := by
  unfold initialAccumulator
  rw [List.mapM_cons]
  cases first : (claimMessage challenges claim).tryInverse <;>
    cases rest : claims.mapM (fun claim => (claimMessage challenges claim).tryInverse) <;> rfl

theorem initialAccumulator_success {challenges : Challenges} {claims : List (List G)} {accumulator : Extension}
    (accepted : initialAccumulator challenges claims = some accumulator) :
    LogUp.PoleFree (publicEntries challenges claims) ∧
      accumulator = LogUp.fractionSum (publicEntries challenges claims) := by
  induction claims generalizing accumulator with
  | nil =>
    constructor
    · intro _ member; cases member
    · cases accepted; rfl
  | cons claim claims ih =>
    rw [initialAccumulator_cons] at accepted
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at accepted
    obtain ⟨inverse, inverseRead, rest, restRead, rfl⟩ := accepted
    obtain ⟨free, equal⟩ := ih restRead
    have nonzero : claimMessage challenges claim ≠ 0 := by
      intro zero
      have none := (Extension.tryInverse_none_iff _).mpr zero
      rw [none] at inverseRead
      cases inverseRead
    refine ⟨?_, ?_⟩
    · intro entry member
      simp only [publicEntries, List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact nonzero
      · exact free entry member
    · rw [publicEntries, List.map_cons, LogUp.fractionSum_cons]
      simp only [LogUp.inverseValue, inverseRead, Option.getD_some, Lean.Grind.Semiring.one_mul]
      rw [equal]
      rfl

theorem initialAccumulator_defined (challenges : Challenges) (claims : List (List G))
    (free : LogUp.PoleFree (publicEntries challenges claims)) :
    ∃ accumulator, initialAccumulator challenges claims = some accumulator := by
  induction claims with
  | nil => exact ⟨0, rfl⟩
  | cons claim claims ih =>
    have head : claimMessage challenges claim ≠ 0 := free (1, claimMessage challenges claim) List.mem_cons_self
    obtain ⟨inverseRead, _⟩ := Extension.inverse_correct _ head
    obtain ⟨rest, restRead⟩ := ih (fun entry member => free entry (List.mem_cons_of_mem _ member))
    exact ⟨(claimMessage challenges claim).conjugate.scale (claimMessage challenges claim).norm.inverse + rest,
      by simp only [initialAccumulator_cons, inverseRead, restRead, bind, pure, Option.bind_some]⟩

theorem initialAccumulator_defined_iff (challenges : Challenges) (claims : List (List G)) :
    (∃ accumulator, initialAccumulator challenges claims = some accumulator) ↔
      LogUp.PoleFree (publicEntries challenges claims) :=
  ⟨fun ⟨_, read⟩ => (initialAccumulator_success read).1, initialAccumulator_defined challenges claims⟩

theorem initialAccumulator_lookupFractions {challenges : Challenges} {claims : List (List G)} {accumulator : Extension}
    (accepted : initialAccumulator challenges claims = some accumulator) :
    accumulator = LogUp.lookupFractions (Coordinates.fromExtension challenges.beta)
      (Coordinates.fromExtension challenges.gamma) (claims.map fun claim => (1, claim)) := by
  rw [LogUp.lookupFractions, publicEntries_compress]
  exact (initialAccumulator_success accepted).2

theorem checkRows_cons (challenges : Challenges) (row : ProofShape.Row) (rows : List ProofShape.Row)
    (entering final : Extension) :
    checkRows challenges (row :: rows) entering = some final ↔
      check challenges row entering = some true ∧ checkRows challenges rows row.accumulator = some final := by
  simp only [checkRows, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨accepted, checked, tail⟩
    cases accepted with
    | false => cases tail
    | true => exact ⟨checked, tail⟩
  · rintro ⟨checked, tail⟩; exact ⟨true, checked, tail⟩

theorem checkRows_final {challenges : Challenges} {rows : List ProofShape.Row} {entering final : Extension}
    (accepted : checkRows challenges rows entering = some final) :
    rows.foldl (fun _ row => row.accumulator) entering = final := by
  induction rows generalizing entering with
  | nil => exact Option.some.inj accepted
  | cons row rows ih => exact ih ((checkRows_cons _ _ _ _ _).mp accepted).2

theorem checkRows_row {challenges : Challenges} {rows : List ProofShape.Row} {entering final : Extension}
    (accepted : checkRows challenges rows entering = some final) {position : Nat} {row : ProofShape.Row}
    (present : rows[position]? = some row) :
    ∃ before, (entering :: rows.map (·.accumulator))[position]? = some before ∧
      check challenges row before = some true := by
  induction rows generalizing entering position with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at present
  | cons first rows ih =>
    obtain ⟨checked, tail⟩ := (checkRows_cons _ _ _ _ _).mp accepted
    cases position with
    | zero => cases present; exact ⟨entering, rfl, checked⟩
    | succ position =>
      obtain ⟨before, beforeRead, rowRead⟩ := ih tail present
      exact ⟨before, beforeRead, rowRead⟩

theorem checkRows_sum {challenges : Challenges} {rows : List ProofShape.Row} {entering final : Extension}
    (accepted : checkRows challenges rows entering = some final) (fraction : ProofShape.Row → Extension)
    (rowIdentity : ∀ row ∈ rows, ∀ before, check challenges row before = some true →
      fraction row = row.accumulator - before) :
    LogUp.sum (rows.map fraction) = final - entering := by
  induction rows generalizing entering with
  | nil =>
    have same := Option.some.inj accepted
    change (0 : Extension) = final - entering
    rw [same]
    grind
  | cons row rows ih =>
    obtain ⟨checked, tail⟩ := (checkRows_cons _ _ _ _ _).mp accepted
    have head := rowIdentity row List.mem_cons_self entering checked
    have rest := ih tail (fun item member => rowIdentity item (List.mem_cons_of_mem _ member))
    change fraction row + LogUp.sum (rows.map fraction) = final - entering
    rw [head, rest]
    grind

theorem verify_true_iff (challenges : Challenges) (claims : List (List G)) (rows : List ProofShape.Row) :
    verify challenges claims rows = some true ↔ rows ≠ [] ∧
      ∃ entering, initialAccumulator challenges claims = some entering ∧ checkRows challenges rows entering = some 0 := by
  unfold verify
  cases rows with
  | nil => simp only [List.isEmpty_nil, if_true, reduceCtorEq, ne_eq, not_true_eq_false, false_and]
  | cons row rows =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq, beq_iff_eq, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    constructor
    · rintro ⟨entering, initial, final, checked, rfl⟩; exact ⟨entering, initial, checked⟩
    · rintro ⟨entering, initial, checked⟩; exact ⟨entering, initial, 0, checked, rfl⟩

theorem verify_lookup_balance {challenges : Challenges} {claims : List (List G)} {rows : List ProofShape.Row}
    (accepted : verify challenges claims rows = some true) (fraction : ProofShape.Row → Extension)
    (rowIdentity : ∀ row ∈ rows, ∀ before, check challenges row before = some true →
      fraction row = row.accumulator - before) :
    LogUp.lookupFractions (Coordinates.fromExtension challenges.beta) (Coordinates.fromExtension challenges.gamma)
      (claims.map fun claim => (1, claim)) + LogUp.sum (rows.map fraction) = 0 := by
  obtain ⟨_, entering, initial, checked⟩ := (verify_true_iff _ _ _).mp accepted
  rw [checkRows_sum checked fraction rowIdentity, ← initialAccumulator_lookupFractions initial]
  grind

theorem verify_row {challenges : Challenges} {claims : List (List G)} {rows : List ProofShape.Row}
    (accepted : verify challenges claims rows = some true) {position : Nat} {row : ProofShape.Row}
    (present : rows[position]? = some row) :
    ∃ initial before result,
      initialAccumulator challenges claims = some initial ∧
      (initial :: rows.map (·.accumulator))[position]? = some before ∧
      evaluate challenges row before = some result ∧
      Quotient.composition challenges.alpha result.constraints =
        Domain.vanishing result.domain challenges.zeta * result.quotientValue := by
  obtain ⟨_, initial, initialRead, checked⟩ := (verify_true_iff _ _ _).mp accepted
  obtain ⟨before, beforeRead, rowChecked⟩ := checkRows_row checked present
  obtain ⟨result, evaluated, identity⟩ := (check_true_iff _ _ _).mp rowChecked
  exact ⟨initial, before, result, initialRead, beforeRead, evaluated, identity⟩

end Aiur.NativeAIR.VerifierArithmetic

namespace Aiur.BoundVerifier
open NativeAIR
open NativeAIR.VerifierArithmetic

/-- Every arithmetic-accepted active opening is tied to its actual key,
proof position, entering accumulator and unfolded graph expressions. -/
theorem CompiledBackend.checked_row_values {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes) {challenges : Challenges}
    {claims : List (List G)} (accepted : VerifierArithmetic.verify challenges claims checked.rows = some true)
    {position : Nat} {row : ProofShape.Row} (present : checked.rows[position]? = some row) :
    row.Sourced backend.keyData checked.data row.circuitIndex position ∧ row.Fits backend.keyData.parameters ∧
      ∃ initial before result trees lookups coordinates,
        initialAccumulator challenges claims = some initial ∧
        (initial :: checked.rows.map (·.accumulator))[position]? = some before ∧
        evaluate challenges row before = some result ∧ row.circuit.graph.unfold = some trees ∧
        evalRoots ProofCodec.Extension.evalOps (view challenges row before result.selectors)
          trees row.circuit.graph.zeros = some result.userValues ∧
        row.circuit.graph.lookups.mapM
          (evalLookup ProofCodec.Extension.evalOps (view challenges row before result.selectors) trees) = some lookups ∧
        LogUp.equations lookups (rowColumns row .stage2 .current) (rowColumns row .stage2 .next)
          (publics challenges before row.accumulator) (deltaScaled result.domain before row.accumulator)
          result.selectors.isLast row.circuit.lookupGroupSize = some coordinates ∧
        result.lookupValues = LogUp.Coordinates.flatten coordinates ∧
        Quotient.composition challenges.alpha result.constraints =
          Domain.vanishing result.domain challenges.zeta * result.quotientValue := by
  obtain ⟨_, sourced, fits⟩ := checked.row present
  obtain ⟨initial, before, result, initialRead, beforeRead, evaluated, identity⟩ := verify_row accepted present
  have valid := backend.toBackend.key_graph_valid (List.mem_of_getElem? sourced.circuit)
  obtain ⟨trees, lookups, coordinates, unfolded, _, roots, lookupValues, equations, equal⟩ :=
    evaluate_reflects evaluated valid
  exact ⟨sourced, fits, initial, before, result, trees, lookups, coordinates, initialRead, beforeRead,
    evaluated, unfolded, roots, lookupValues, equations, equal, identity⟩

end Aiur.BoundVerifier
