module
public import Ix.MultiStark.Verify.Transcript.Basic

/-! Finite rejection-sampling semantics. This relation specifies a sequence
of discarded noncanonical raw words followed by the FIRST canonical word.
It does not assert that every input admits such a finite sequence. -/

public section

namespace MultiStark.Verify.Transcript

inductive FieldSampling : Challenger → Field → Challenger → Prop where
  | accepted (state : Challenger) (canonical : (draw64 state).1 < Ix.Ixby.goldilocksModulus) :
    FieldSampling state ⟨(draw64 state).1, canonical⟩ (draw64 state).2
  | rejected (state : Challenger) (noncanonical : Ix.Ixby.goldilocksModulus ≤ (draw64 state).1)
      (rest : FieldSampling (draw64 state).2 value final) : FieldSampling state value final

theorem sampleField_sound (attempts : Nat) (state : Challenger) (value : Field) (final : Challenger)
    (accepted : sampleFieldWith attempts state = .ok (value, final)) :
    FieldSampling state value final := by
  induction attempts generalizing state with
  | zero => simp [sampleFieldWith] at accepted
  | succ attempts ih =>
    simp only [sampleFieldWith] at accepted
    split at accepted
    next canonical =>
      have pair := Except.ok.inj accepted
      cases pair
      exact .accepted state canonical
    next noncanonical =>
      exact .rejected state (Nat.le_of_not_lt noncanonical) (ih _ accepted)

theorem sampleField_complete {state : Challenger} {value : Field} {final : Challenger}
    (derivation : FieldSampling state value final) :
    ∃ attempts, sampleFieldWith attempts state = .ok (value, final) := by
  induction derivation with
  | accepted state canonical =>
    exact ⟨1, by simp [sampleFieldWith, canonical]⟩
  | rejected state noncanonical _ ih =>
    obtain ⟨attempts, accepted⟩ := ih
    exact ⟨attempts + 1, by simp [sampleFieldWith, Nat.not_lt.mpr noncanonical, accepted]⟩

end MultiStark.Verify.Transcript
