/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.KeyCodec

/-! Total codec for the pinned CPU Goldilocks/Blake3 multi-STARK proof.
The native bincode configuration uses little-endian fixed-width integers,
u64 vector lengths, one-byte booleans/options, and fixed arrays without a
length prefix. Extension elements have two canonical Goldilocks coordinates.

Every opening and authentication digest is retained. Parsing establishes
byte framing only; proof shape, transcript checks and cryptographic meaning
are separate obligations. Native `from_bytes` permits a trailing suffix;
`decode` deliberately requires complete consumption.
-/

namespace Aiur.NativeAIR.ProofCodec

open KeyCodec (Reader readByte readNat readMany encodeNat)

structure Extension where
  c0 : G
  c1 : G
  deriving DecidableEq, Repr

abbrev Digest := List UInt8
abbrev Cap := List Digest
abbrev Openings (α : Type) := List (List (List α))

def readVector (read : Reader α) : Reader (List α) := do
  readMany read (← readNat 8)

def encodeVector (encode : α → List UInt8) (values : List α) : List UInt8 :=
  encodeNat 8 values.length ++ values.flatMap encode

def readOption (read : Reader α) : Reader (Option α) := do
  match (← readByte).toNat with
  | 0 => return none
  | 1 => return some (← read)
  | _ => failure

def encodeOption (encode : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some value => 1 :: encode value

def readBool : Reader Bool := do
  match (← readByte).toNat with
  | 0 => return false
  | 1 => return true
  | _ => failure

def encodeBool (value : Bool) : List UInt8 := [if value then 1 else 0]

def readField : Reader G := do
  let value ← readNat 8
  if value < gSize.toNat then return G.ofNat value else failure

def encodeField (value : G) : List UInt8 := encodeNat 8 value.n

def readExtension : Reader Extension := do
  return ⟨← readField, ← readField⟩

def encodeExtension (value : Extension) : List UInt8 :=
  encodeField value.c0 ++ encodeField value.c1

def readCap : Reader Cap := readVector (readMany readByte 32)

def encodeCap (cap : Cap) : List UInt8 := encodeVector id cap

def readOpenings (read : Reader α) : Reader (Openings α) :=
  readVector (readVector (readVector read))

def encodeOpenings (encode : α → List UInt8) (values : Openings α) : List UInt8 :=
  encodeVector (encodeVector (encodeVector encode)) values

structure Commitments where
  stage1 : Cap
  stage2 : Cap
  quotient : Cap
  deriving DecidableEq, Repr

def readCommitments : Reader Commitments := do
  return ⟨← readCap, ← readCap, ← readCap⟩

def encodeCommitments (value : Commitments) : List UInt8 :=
  encodeCap value.stage1 ++ encodeCap value.stage2 ++ encodeCap value.quotient

structure BatchOpening where
  values : Openings G
  siblingHashes : List Digest
  deriving DecidableEq, Repr

def readBatchOpening : Reader BatchOpening := do
  return ⟨← readOpenings readField, ← readCap⟩

def encodeBatchOpening (value : BatchOpening) : List UInt8 :=
  encodeOpenings encodeField value.values ++ encodeCap value.siblingHashes

structure CommitStep where
  logArity : UInt8
  siblingValues : List (List Extension)
  siblingHashes : List Digest
  deriving DecidableEq, Repr

def readCommitStep : Reader CommitStep := do
  return ⟨← readByte, ← readVector (readVector readExtension), ← readCap⟩

def encodeCommitStep (value : CommitStep) : List UInt8 :=
  value.logArity :: (encodeVector (encodeVector encodeExtension) value.siblingValues ++
    encodeCap value.siblingHashes)

structure Fri where
  commits : List Cap
  commitPowWitnesses : List G
  inputOpenings : List BatchOpening
  commitOpenings : List CommitStep
  finalPoly : List Extension
  queryPowWitness : G
  deriving DecidableEq, Repr

def readFri : Reader Fri := do
  return ⟨← readVector readCap, ← readVector readField,
    ← readVector readBatchOpening, ← readVector readCommitStep,
    ← readVector readExtension, ← readField⟩

def encodeFri (value : Fri) : List UInt8 :=
  encodeVector encodeCap value.commits ++ encodeVector encodeField value.commitPowWitnesses ++
  encodeVector encodeBatchOpening value.inputOpenings ++ encodeVector encodeCommitStep value.commitOpenings ++
  encodeVector encodeExtension value.finalPoly ++ encodeField value.queryPowWitness

structure Data where
  active : List Bool
  commitments : Commitments
  accumulators : List Extension
  logDegrees : List UInt8
  fri : Fri
  quotient : Openings Extension
  preprocessed : Option (Openings Extension)
  stage1 : Openings Extension
  stage2 : Openings Extension
  deriving DecidableEq, Repr

def readData : Reader Data := do
  return ⟨← readVector readBool, ← readCommitments, ← readVector readExtension,
    ← readVector readByte, ← readFri, ← readOpenings readExtension,
    ← readOption (readOpenings readExtension), ← readOpenings readExtension,
    ← readOpenings readExtension⟩

def encodeData (value : Data) : List UInt8 :=
  encodeVector encodeBool value.active ++ encodeCommitments value.commitments ++
  encodeVector encodeExtension value.accumulators ++ encodeVector (fun b => [b]) value.logDegrees ++
  encodeFri value.fri ++ encodeOpenings encodeExtension value.quotient ++
  encodeOption (encodeOpenings encodeExtension) value.preprocessed ++
  encodeOpenings encodeExtension value.stage1 ++ encodeOpenings encodeExtension value.stage2

def decode (bytes : ByteArray) : Option Data := do
  let (value, rest) ← readData bytes.data.toList
  if rest.isEmpty then some value else none

def encode (value : Data) : ByteArray := (encodeData value).toByteArray

def decodeCanonical (bytes : ByteArray) : Option Data := do
  let value ← decode bytes
  if encode value = bytes then some value else none

end Aiur.NativeAIR.ProofCodec
