import Compilatrix.Aiur.Balance

/-! Well-founded dependency expansion of a balanced trace. This is a finite
derivation of extracted row facts, not yet a BytecodeEval or AIR theorem. -/

namespace Compilatrix.Aiur.Trace

/-- Each demanded message has a provider and recursively justified demands.
Multiplicity chooses a usable provider, but does not count copies of a tree. -/
inductive Derivation (trace : Trace) : Message → Prop where
  | provider (id : trace.RowId)
      (active : (trace.row id).active = true)
      (nonzero : (trace.row id).multiplicity ≠ 0)
      (children : ∀ message ∈ (trace.row id).demands, Derivation trace message) :
      Derivation trace (trace.row id).provides

theorem Derivation.has_provider {trace : Trace} {message : Message}
    (derivation : trace.Derivation message) :
    ∃ id : trace.RowId, (trace.row id).active = true ∧ (trace.row id).provides = message := by
  cases derivation with
  | provider id active _ _ => exact ⟨id, active, rfl⟩

theorem row_derivation (trace : Trace) (activity : trace.Activity)
    (balanced : trace.Balanced) (bound : trace.WithinCharacteristic)
    (wellFounded : WellFounded trace.Requires) (id : trace.RowId)
    (active : (trace.row id).active = true) (nonzero : (trace.row id).multiplicity ≠ 0) :
    trace.Derivation (trace.row id).provides := by
  revert active nonzero
  induction id using wellFounded.induction with
  | h id ih =>
    intro active nonzero
    apply Derivation.provider id active nonzero
    intro message member
    obtain ⟨child, sameMessage, weight, childActive⟩ := trace.provider_exists activity balanced bound
      (trace.demand_mem_requirements id active member)
    have requires : trace.Requires child id := by
      exact ⟨active, childActive, weight, by simpa [sameMessage] using member⟩
    have result := ih child requires childActive weight
    simpa [sameMessage] using result

/-- A public claim has a finite rooted derivation once extraction supplies
balance, activity, the consumer bound, and a well-founded requires relation. -/
theorem public_derivation (trace : Trace) (activity : trace.Activity)
    (balanced : trace.Balanced) (bound : trace.WithinCharacteristic)
    (wellFounded : WellFounded trace.Requires) {message : Message}
    (claim : message ∈ trace.publicClaims) : trace.Derivation message := by
  obtain ⟨id, sameMessage, nonzero, active⟩ := trace.provider_exists activity balanced bound
    (trace.public_mem_requirements claim)
  have result := trace.row_derivation activity balanced bound wellFounded id active nonzero
  simpa [sameMessage] using result

/-- Interpret a finite row derivation in any row-local semantics whose
constructor is justified by its demanded messages. The AIR/evaluator bridge
must prove this local rule; it is not inferred from lookup balance. -/
theorem Derivation.sound {trace : Trace} {message : Message}
    (derivation : trace.Derivation message) (meaning : Message → Prop)
    (localRule : ∀ id : trace.RowId,
      (trace.row id).active = true → (trace.row id).multiplicity ≠ 0 →
      (∀ child ∈ (trace.row id).demands, meaning child) → meaning (trace.row id).provides) :
    meaning message := by
  induction derivation with
  | provider id active nonzero _ ih => exact localRule id active nonzero ih

end Compilatrix.Aiur.Trace
