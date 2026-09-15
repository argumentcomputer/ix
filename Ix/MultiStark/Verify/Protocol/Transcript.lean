module
public import Ix.MultiStark.Verify.Transcript.Basic

/-! Relational transcript primitives: observations, raw bit draws, and the
first canonical field draw with an explicit number of consumed raw words.
These do not refer to a verifier acceptance bit or a sampling implementation.
The common raw `draw64` operation supplies the pure BLAKE3 byte stream. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

open Transcript (Challenger Limits draw64)

def Observed (limits : Limits) (state : Challenger) (bytes : Bytes) (final : Challenger) : Prop :=
  (bytes.isEmpty = true ∧ state = final) ∨
    (bytes.isEmpty = false ∧ state.input.size + bytes.size ≤ limits.observationBytes ∧
      Challenger.mk (state.input ++ bytes) #[] = final)

def BitsDraw (bits : Nat) (state : Challenger) (value : Nat) (final : Challenger) : Prop :=
  bits < 64 ∧ (draw64 state).1 % 2 ^ bits = value ∧ (draw64 state).2 = final

inductive FieldDraws : Nat → Challenger → Field → Challenger → Prop where
  | accepted (state : Challenger) (canonical : (draw64 state).1 < Ix.Ixby.goldilocksModulus) :
    FieldDraws 1 state ⟨(draw64 state).1, canonical⟩ (draw64 state).2
  | rejected (state : Challenger) (noncanonical : Ix.Ixby.goldilocksModulus ≤ (draw64 state).1)
      (rest : FieldDraws count (draw64 state).2 value final) : FieldDraws (count + 1) state value final

def FieldDrawWithin (attempts : Nat) (state : Challenger) (value : Field) (final : Challenger) : Prop :=
  ∃ count, count ≤ attempts ∧ FieldDraws count state value final

def Grinding (limits : Limits) (bits : Nat) (witness : Field) (state final : Challenger) : Prop :=
  (bits = 0 ∧ state = final) ∨
    (0 < bits ∧ bits < 64 ∧ ∃ observed,
      Observed limits state (Codec.Wire.littleEndian 8 witness.val) observed ∧ BitsDraw bits observed 0 final)

end MultiStark.Verify.Protocol
