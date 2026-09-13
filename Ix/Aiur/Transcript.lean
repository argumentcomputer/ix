/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Challenger
import Ix.Aiur.VerifierArithmetic

/-! The multi-STARK transcript through the out-of-domain challenge, with
the continuing challenger state retained for PCS verification. This replay
does not authenticate the openings or assert hash security.
-/

namespace Aiur.NativeAIR.Transcript

open Challenger
open ProofCodec (Extension)

def parameterWords (parameters : KeyCodec.Parameters) : List Nat :=
  [parameters.logBlowup, parameters.capHeight, parameters.logFinalPolyLen,
    parameters.maxLogArity, parameters.numQueries, parameters.commitProofOfWorkBits,
    parameters.queryProofOfWorkBits]

def seed (parameters : KeyCodec.Parameters) : List UInt8 :=
  "multi-stark/v0".toUTF8.data.toList ++ (parameterWords parameters).flatMap (KeyCodec.encodeNat 8)

def circuitShape (circuit : KeyCodec.Circuit) : List G :=
  [circuit.constraintCount, circuit.maxConstraintDegree, circuit.preprocessedHeight,
    circuit.preprocessedWidth, circuit.mainWidth, circuit.widths.stage2, circuit.lookupGroupSize].map G.ofNat

def shape (key : KeyCodec.Key) : List G :=
  G.ofNat key.circuits.length :: key.circuits.flatMap circuitShape

def claimsFields (claims : List (List G)) : List G :=
  G.ofNat claims.length :: claims.flatMap (fun claim => G.ofNat claim.length :: claim)

def fieldsBytes (values : List G) : List UInt8 := values.flatMap ProofCodec.encodeField

def prefixBytes (key : KeyCodec.Key) (proof : ProofCodec.Data) (claims : List (List G)) : List UInt8 :=
  fieldsBytes (shape key) ++
    fieldsBytes (proof.active.map (fun active => if active then 1 else 0)) ++
    (key.preprocessedCommitment.getD []).flatten ++ proof.commitments.stage1.flatten ++
    fieldsBytes (proof.logDegrees.map (fun degree => G.ofNat degree.toNat)) ++
    fieldsBytes (claimsFields claims)

def lookupState (key : KeyCodec.Key) (proof : ProofCodec.Data) (claims : List (List G)) : State :=
  observeBytes (initial (seed key.parameters)) (prefixBytes key proof claims)

def accumulatorState (proof : ProofCodec.Data) (state : State) : State :=
  proof.accumulators.foldl observeExtension (observeCap state proof.commitments.stage2)

structure Replay where
  challenges : VerifierArithmetic.Challenges
  state : State
  deriving DecidableEq, Repr

def replay (hash : Hash32) (fuel : Nat) (key : KeyCodec.Key)
    (proof : ProofCodec.Data) (claims : List (List G)) : Option Replay := do
  let (beta, afterBeta) ← sampleExtension hash fuel (lookupState key proof claims)
  let (gamma, afterGamma) ← sampleExtension hash fuel (observeExtension afterBeta beta)
  let (alpha, afterAlpha) ← sampleExtension hash fuel
    (accumulatorState proof (observeExtension afterGamma gamma))
  let (zeta, final) ← sampleExtension hash fuel (observeCap afterAlpha proof.commitments.quotient)
  return ⟨⟨beta, gamma, alpha, zeta⟩, final⟩

/-- Arithmetic with transcript-derived challenges. The PCS still has to
authenticate the polynomial openings using the returned challenger state. -/
def verifyArithmetic (hash : Hash32) (fuel : Nat) (key : KeyCodec.Key)
    (proof : ProofCodec.Data) (claims : List (List G)) (rows : List ProofShape.Row) : Option Replay := do
  let result ← replay hash fuel key proof claims
  if ← VerifierArithmetic.verify result.challenges claims rows then some result else none

end Aiur.NativeAIR.Transcript
