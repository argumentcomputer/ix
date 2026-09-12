module
public import Ix.MultiStark.Verify.Protocol.Ood
public import Ix.MultiStark.Verify.Proofs.Arithmetic
public import Ix.MultiStark.Verify.Proofs.Graph

public section

namespace MultiStark.Verify.Proofs

open Arithmetic (Coordinates)

theorem selectors_refines (logDegree : Nat) (point : Ext) (result : Ood.Selectors) :
    Ood.selectors logDegree point = .ok result ↔ Protocol.SelectorsAt logDegree point result := by
  simp only [Ood.selectors, bind_ok_iff, mapError_ok_iff, pure_ok_iff,
    twoAdicGenerator_refines, inverseBase_refines, divide_refines, inverse_refines,
    Protocol.SelectorsAt, exists_and_left]

theorem readRefs_refines (computed : Array Ext) (indices : List Nat) (values : List Ext) :
    Ood.readRefs computed indices = .ok values ↔ Protocol.References computed indices values := by
  induction indices generalizing values with
  | nil => cases values <;> simp [Ood.readRefs, Protocol.References]
  | cons index indices ih =>
    simp only [Ood.readRefs, bind_ok_iff, pure_ok_iff, getAt_ok_iff, ih]
    cases values with
    | nil => simp [Protocol.References]
    | cons value values =>
      simp [Protocol.References]

theorem roots_refines (circuit : Circuit) (computed values : Array Ext) :
    Ood.roots circuit computed = .ok values ↔
      Protocol.References computed circuit.zeros.toList values.toList := by
  simp only [Ood.roots, bind_ok_iff, pure_ok_iff, readRefs_refines]
  constructor
  · rintro ⟨list, reads, equal⟩
    cases equal
    simpa using reads
  · intro reads
    exact ⟨values.toList, reads, by simp⟩

theorem references_length (computed : Array Ext) (indices : List Nat) (values : List Ext)
    (references : Protocol.References computed indices values) : indices.length = values.length := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all [Protocol.References]
  | cons index indices ih =>
    cases values with
    | nil => simp [Protocol.References] at references
    | cons value values =>
      simp only [List.length_cons, ih values references.2]

theorem readCoordinates_refines (row : Array Ext) (offset : Nat) (value : Coordinates) :
    Ood.readCoordinates row offset = .ok value ↔ Protocol.CoordinateRead row offset value := by
  cases value with
  | mk c0 c1 =>
    simp [Ood.readCoordinates, bind_ok_iff, map_ok_iff, getAt_ok_iff, Protocol.CoordinateRead]

theorem lookupMessage_refines (computed : Array Ext) (beta gamma : Coordinates) (lookup : Lookup)
    (result : Coordinates) :
    Ood.lookupMessage computed beta gamma lookup = .ok result ↔
      Protocol.LookupMessage computed beta gamma lookup result := by
  simp only [Ood.lookupMessage, bind_ok_iff, pure_ok_iff, readRefs_refines, Protocol.LookupMessage]

theorem lookupEntries_refines (computed : Array Ext) (beta gamma : Coordinates)
    (lookups : List Lookup) (entries : List (Coordinates × Ext)) :
    Ood.lookupEntries computed beta gamma lookups = .ok entries ↔
      Protocol.LookupEntries computed beta gamma lookups entries := by
  induction lookups generalizing entries with
  | nil => cases entries <;> simp [Ood.lookupEntries, Protocol.LookupEntries]
  | cons lookup lookups ih =>
    simp only [Ood.lookupEntries, bind_ok_iff, pure_ok_iff, lookupMessage_refines, getAt_ok_iff, ih]
    cases entries with
    | nil => simp [Protocol.LookupEntries]
    | cons entry entries =>
      cases entry with
      | mk message multiplicity =>
        simp [Protocol.LookupEntries]
        constructor
        · rintro ⟨m, messageRead, k, multiplicityRead, rest, rfl, rfl⟩
          exact ⟨messageRead, multiplicityRead, rest⟩
        · rintro ⟨messageRead, multiplicityRead, rest⟩
          exact ⟨message, messageRead, multiplicity, multiplicityRead, rest, rfl, rfl⟩

theorem groupEquation_refines (computed : Array Ext) (group : Array Lookup) (beta gamma delta : Coordinates)
    (result : Coordinates) :
    Ood.groupEquation computed group beta gamma delta = .ok result ↔
      Protocol.GroupEquation computed group beta gamma delta result := by
  simp only [Ood.groupEquation, bind_ok_iff, pure_ok_iff, lookupEntries_refines,
    Ood.groupPolynomial, Protocol.GroupEquation]

theorem lookupTarget_refines (view : Ood.View) (injection : Coordinates) (group : Nat) (result : Coordinates) :
    Ood.lookupTarget view injection group = .ok result ↔ Protocol.LookupTarget view injection group result := by
  by_cases later : group + 1 < view.values.circuit.lookupGroups
  · simp only [Ood.lookupTarget, Protocol.LookupTarget, later, ↓reduceIte, readCoordinates_refines]
  · simp only [Ood.lookupTarget, Protocol.LookupTarget, later, ↓reduceIte]
    change ((fun value => value.add injection) <$> Ood.readCoordinates view.values.stage2.2 0) = .ok result ↔ _
    simp only [map_ok_iff, readCoordinates_refines]

theorem lookupGroupsFrom_refines (view : Ood.View) (computed : Array Ext) (beta gamma injection : Coordinates)
    (group remaining : Nat) (values : List Ext) :
    Ood.lookupGroupsFrom view computed beta gamma injection group remaining = .ok values ↔
      Protocol.LookupGroups view computed beta gamma injection group remaining values := by
  induction remaining generalizing group values with
  | zero => simp [Ood.lookupGroupsFrom, Protocol.LookupGroups]
  | succ remaining ih =>
    simp only [Ood.lookupGroupsFrom, bind_ok_iff, pure_ok_iff, readCoordinates_refines,
      lookupTarget_refines, groupEquation_refines, ih, Protocol.LookupGroups, exists_and_left]

theorem lookupValues_refines (view : Ood.View) (computed values : Array Ext) :
    Ood.lookupValues view computed = .ok values ↔ Protocol.LookupValues view computed values := by
  simp only [Ood.lookupValues, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff,
    readCoordinates_refines, lookupGroupsFrom_refines, Bool.and_eq_true, beq_iff_eq,
    Protocol.LookupValues, exists_and_left, listArray_exists_iff]

theorem claimFingerprint_refines (gamma : Ext) (claim : Array Field) :
    Ood.claimFingerprint gamma claim = Protocol.ClaimPolynomial gamma claim := rfl

theorem initialAccumulatorFrom_refines (challenges : Transcript.Challenges)
    (claims : List (Array Field)) (initial final : Ext) :
    Ood.initialAccumulatorFrom challenges claims initial = .ok final ↔
      Protocol.InitialAccumulator challenges claims initial final := by
  induction claims generalizing initial with
  | nil => simp [Ood.initialAccumulatorFrom, Protocol.InitialAccumulator]
  | cons claim claims ih =>
    simp only [Ood.initialAccumulatorFrom, bind_ok_iff, mapError_ok_iff, inverse_refines,
      claimFingerprint_refines, ih, Protocol.InitialAccumulator]

theorem initialAccumulator_refines (challenges : Transcript.Challenges)
    (claims : Array (Array Field)) (result : Ext) :
    Ood.initialAccumulator challenges claims = .ok result ↔
      Protocol.InitialAccumulator challenges claims.toList Arithmetic.zero result :=
  initialAccumulatorFrom_refines challenges claims.toList Arithmetic.zero result

theorem quotientFrom_refines (pointPowerN : Ext) (coefficients : List Ext) (power initial result : Ext) :
    Ood.quotientFrom pointPowerN coefficients power initial = .ok result ↔
      Protocol.QuotientSum pointPowerN coefficients power initial result := by
  cases coefficients with
  | nil => simp [Ood.quotientFrom, Protocol.QuotientSum]
  | cons c0 remaining =>
    cases remaining with
    | nil => simp [Ood.quotientFrom, Protocol.QuotientSum]
    | cons c1 rest =>
      exact quotientFrom_refines pointPowerN rest (power.mul pointPowerN)
        (initial.add (power.mul (c0.add (c1.mul Arithmetic.basis)))) result
termination_by structural coefficients

theorem recombineQuotient_refines (values : Shape.CircuitValues) (pointPowerN result : Ext) :
    Ood.recombineQuotient values pointPowerN = .ok result ↔ Protocol.QuotientValue values pointPowerN result := by
  simp only [Ood.recombineQuotient, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    beq_iff_eq, quotientFrom_refines, Protocol.QuotientValue]

theorem ood_evaluate_refines (challenges : Transcript.Challenges) (initial final : Ext)
    (values : Shape.CircuitValues) (result : Ood.Evaluation) :
    Ood.evaluate challenges initial final values = .ok result ↔
      Protocol.OodEvaluation challenges initial final values result := by
  simp only [Ood.evaluate, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff,
    selectors_refines, sweep_refines, roots_refines, lookupValues_refines,
    recombineQuotient_refines, beq_iff_eq, Protocol.OodEvaluation, Ood.publicValues,
    and_assoc, exists_and_left]

theorem balanced_refines (accumulators : Array Ext) :
    Ood.balanced accumulators = true ↔ accumulators.back? = some Arithmetic.zero := by
  unfold Ood.balanced
  cases accumulators.back? <;> simp [extension_beq_iff_eq]

theorem ood_checkFrom_refines (challenges : Transcript.Challenges)
    (values : List Shape.CircuitValues) (accumulators : List Ext) (initial : Ext)
    (evaluations : List Ood.Evaluation) :
    Ood.checkFrom challenges values accumulators initial = .ok evaluations ↔
      Protocol.OodChain challenges values accumulators initial evaluations := by
  induction values generalizing accumulators initial evaluations with
  | nil => cases accumulators <;> cases evaluations <;> simp [Ood.checkFrom, Protocol.OodChain]
  | cons value values ih =>
    cases accumulators with
    | nil => simp [Ood.checkFrom, Protocol.OodChain]
    | cons final accumulators =>
      simp only [Ood.checkFrom, bind_ok_iff, pure_ok_iff, unit_exists_iff, ensure_ok_iff,
        ood_evaluate_refines, extension_beq_iff_eq, ih]
      cases evaluations with
      | nil => simp [Protocol.OodChain]
      | cons evaluation evaluations =>
        simp [Protocol.OodChain]
        constructor
        · rintro ⟨e, evaluated, equation, rest, rfl⟩
          exact ⟨evaluated, equation, rest⟩
        · rintro ⟨evaluated, equation, rest⟩
          exact ⟨evaluation, evaluated, equation, rest, rfl⟩

/-- The complete deterministic OOD phase is equivalent to selector,
expression-reference, grouped-logUp, accumulator, and quotient identities.
This establishes neither PCS authentication nor cryptographic soundness. -/
theorem ood_check_refines (challenges : Transcript.Challenges) (claims : Array (Array Field))
    (values : Array Shape.CircuitValues) (accumulators : Array Ext) (evaluations : Array Ood.Evaluation) :
    Ood.check challenges claims values accumulators = .ok evaluations ↔
      Protocol.OodAccepted challenges claims values accumulators evaluations := by
  simp only [Ood.check, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff, balanced_refines,
    beq_iff_eq, initialAccumulator_refines, ood_checkFrom_refines, listArray_exists_iff, Protocol.OodAccepted]

end MultiStark.Verify.Proofs
