module
public import Ix.MultiStark.Verify.Codec.Wire

/-! Pure canonical codec for the current native multiproof transport.
Parsing proves neither proof shape against a key nor cryptographic validity.
No header/version fallback to the older per-query transport is provided. The
native protocol revision must be fixed by the approved source configuration. -/

public section
@[expose] section

namespace MultiStark.Verify.Codec

namespace Wire

def readCap : Reader MerkleCap := readVector readDigest
def readRound : Reader OpenedRound := readVector (readVector (readVector readExt))

def readCommitments : Reader Commitments := return ⟨← readCap, ← readCap, ← readCap⟩

def readBatchOpening : Reader BatchOpening :=
  return ⟨← readVector (readVector (readVector readField)), ← readVector readDigest⟩

def readCommitPhaseStep : Reader CommitPhaseStep :=
  return ⟨← readByte, ← readVector (readVector readExt), ← readVector readDigest⟩

def readFri : Reader FriProof := do
  return {
    commits := ← readVector readCap
    commitPow := ← readVector readField
    inputOpenings := ← readVector readBatchOpening
    commitOpenings := ← readVector readCommitPhaseStep
    finalPoly := ← readVector readExt
    queryPow := ← readField
  }

def readProof : Reader Proof := do
  return {
    active := ← readVector readBool
    commitments := ← readCommitments
    accumulators := ← readVector readExt
    logDegrees := ← readVector readByte
    fri := ← readFri
    quotient := ← readRound
    preprocessed := ← readOption readRound
    stage1 := ← readRound
    stage2 := ← readRound
  }

def writeCap : MerkleCap → Writer Unit := writeVector writeDigest
def writeRound : OpenedRound → Writer Unit := writeVector (writeVector (writeVector writeExt))

def writeCommitments (commitments : Commitments) : Writer Unit := do
  writeCap commitments.stage1
  writeCap commitments.stage2
  writeCap commitments.quotient

def writeBatchOpening (opening : BatchOpening) : Writer Unit := do
  writeVector (writeVector (writeVector writeField)) opening.values
  writeVector writeDigest opening.frontier

def writeCommitPhaseStep (step : CommitPhaseStep) : Writer Unit := do
  writeByte step.logArity
  writeVector (writeVector writeExt) step.siblings
  writeVector writeDigest step.frontier

def writeFri (proof : FriProof) : Writer Unit := do
  writeVector writeCap proof.commits
  writeVector writeField proof.commitPow
  writeVector writeBatchOpening proof.inputOpenings
  writeVector writeCommitPhaseStep proof.commitOpenings
  writeVector writeExt proof.finalPoly
  writeField proof.queryPow

def writeProof (proof : Proof) : Writer Unit := do
  writeVector writeBool proof.active
  writeCommitments proof.commitments
  writeVector writeExt proof.accumulators
  writeVector writeByte proof.logDegrees
  writeFri proof.fri
  writeRound proof.quotient
  writeOption writeRound proof.preprocessed
  writeRound proof.stage1
  writeRound proof.stage2

end Wire

def encodeProof (limits : DecodeLimits) (proof : Proof) : Except DecodeError Bytes :=
  Wire.encode limits (Wire.writeProof proof)

def decodeProof (limits : DecodeLimits) (bytes : Bytes) :
    Except DecodeError (Canonical (encodeProof limits) bytes) := do
  let proof ← Wire.decode limits bytes Wire.readProof
  Wire.canonicalize (encodeProof limits) bytes proof

end MultiStark.Verify.Codec
