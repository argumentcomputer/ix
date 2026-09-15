module
public import Ix.MultiStark.Verify.Protocol.Transcript
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

open Transcript (Challenger Limits Error draw64 sampleFieldWith)

theorem observeBytes_refines (limits : Limits) (state final : Challenger) (bytes : Bytes) :
    ((Transcript.observeBytes limits bytes).run state = .ok ((), final)) ↔
      Protocol.Observed limits state bytes final := by
  by_cases empty : bytes.isEmpty = true
  · simp [Transcript.observeBytes, empty, Protocol.Observed, StateT.run]
  · by_cases bounded : state.input.size + bytes.size ≤ limits.observationBytes
    · simp [Transcript.observeBytes, empty, bounded, Nat.not_lt.mpr bounded, Protocol.Observed,
        StateT.run]
    · simp [Transcript.observeBytes, empty, bounded, Nat.lt_of_not_ge bounded, Protocol.Observed,
        StateT.run]

theorem sampleBits_refines (bits : Nat) (state final : Challenger) (value : Nat) :
    ((Transcript.sampleBits bits).run state = .ok (value, final)) ↔
      Protocol.BitsDraw bits state value final := by
  by_cases bounded : bits < 64
  · simp [Transcript.sampleBits, Protocol.BitsDraw, bounded, Nat.not_le.mpr bounded,
      StateT.run]
  · simp [Transcript.sampleBits, Protocol.BitsDraw, bounded, Nat.le_of_not_gt bounded,
      StateT.run]

theorem checkWitness_refines (limits : Limits) (bits : Nat) (witness : Field) (state final : Challenger) :
    ((Transcript.checkWitness limits bits witness).run state = .ok ((), final)) ↔
      Protocol.Grinding limits bits witness state final := by
  simp only [Protocol.Grinding, ← observeBytes_refines, ← sampleBits_refines]
  by_cases zero : bits = 0
  · simp [Transcript.checkWitness, StateT.run, zero]
  · have positive : 0 < bits := Nat.pos_of_ne_zero zero
    by_cases bounded : bits < 64
    · cases observed : Transcript.observeBytes limits (Codec.Wire.littleEndian 8 witness.val) state with
      | error error =>
        simp [Transcript.checkWitness, Transcript.observeField, StateT.run, zero, positive,
          Nat.not_le.mpr bounded, observed]
      | ok result =>
        obtain ⟨ignoredValue, next⟩ := result
        cases ignoredValue
        cases sampled : Transcript.sampleBits bits next with
        | error error =>
          simp [Transcript.checkWitness, Transcript.observeField, StateT.run, zero, positive,
            Nat.not_le.mpr bounded, observed, sampled]
        | ok result =>
          obtain ⟨value, last⟩ := result
          by_cases valid : value = 0
          · simp [Transcript.checkWitness, Transcript.observeField, StateT.run, zero, positive, bounded,
              Nat.not_le.mpr bounded, observed, sampled, valid]
          · simp [Transcript.checkWitness, Transcript.observeField, StateT.run, zero, positive,
              Nat.not_le.mpr bounded, observed, sampled, valid]
    · simp [Transcript.checkWitness, StateT.run, zero, bounded, Nat.le_of_not_gt bounded]

theorem sampleField_sound_count (attempts : Nat) (state : Challenger) (value : Field) (final : Challenger)
    (accepted : sampleFieldWith attempts state = .ok (value, final)) :
    Protocol.FieldDrawWithin attempts state value final := by
  induction attempts generalizing state with
  | zero => simp [sampleFieldWith] at accepted
  | succ attempts ih =>
    simp only [sampleFieldWith] at accepted
    split at accepted
    next canonical =>
      have pair := Except.ok.inj accepted
      cases pair
      exact ⟨1, Nat.succ_le_succ (Nat.zero_le _), .accepted state canonical⟩
    next noncanonical =>
      obtain ⟨count, bounded, derivation⟩ := ih _ accepted
      exact ⟨count + 1, Nat.succ_le_succ bounded,
        .rejected state (Nat.le_of_not_lt noncanonical) derivation⟩

theorem sampleField_complete_count {count : Nat} {state : Challenger} {value : Field} {final : Challenger}
    (derivation : Protocol.FieldDraws count state value final) (attempts : Nat) (bounded : count ≤ attempts) :
    sampleFieldWith attempts state = .ok (value, final) := by
  induction derivation generalizing attempts with
  | accepted state canonical =>
    cases attempts with
    | zero => omega
    | succ attempts => simp [sampleFieldWith, canonical]
  | rejected state noncanonical _ ih =>
    cases attempts with
    | zero => omega
    | succ attempts =>
      simp [sampleFieldWith, Nat.not_lt.mpr noncanonical, ih attempts (Nat.le_of_succ_le_succ bounded)]

/-- Exact bounded completeness: the same public attempt budget is used on
both sides. No assumption of universal successful rejection sampling occurs. -/
theorem sampleField_refines (attempts : Nat) (state : Challenger) (value : Field) (final : Challenger) :
    sampleFieldWith attempts state = .ok (value, final) ↔ Protocol.FieldDrawWithin attempts state value final := by
  constructor
  · exact sampleField_sound_count attempts state value final
  · rintro ⟨count, bounded, derivation⟩
    exact sampleField_complete_count derivation attempts bounded

end MultiStark.Verify.Proofs
