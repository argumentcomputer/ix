import Ix.Cert.MultiStark.Types

/-! # Multi-STARK Binary Wire Decoders (`Ix.Cert.MultiStark.Wire`)

Exact, Mathlib-free binary decoders matching:
1. `StarkSystem.fromBytes` — `crates/stark-key/src/lib.rs` (v5 dense format)
2. `BatchProof.fromBytes` — `multi-stark/src/{prover.rs,batch.rs}` (bincode v2 `LittleEndian + Fixint`,
   strict canonical Goldilocks `< p`, strict `bool`/`Option` tag checks, exact EOF).
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Simple immutable byte-slice cursor. -/
private structure Cursor where
  bytes : ByteArray
  pos : Nat
  deriving Inhabited

private abbrev DecodeM := StateT Cursor (Except String)

private def readU8 : DecodeM UInt8 := do
  let c ← get
  if h : c.pos < c.bytes.size then
    set { c with pos := c.pos + 1 }
    pure c.bytes[c.pos]
  else
    throw s!"eof: need 1 byte at offset {c.pos}"

private def readBool : DecodeM Bool := do
  match ← readU8 with
  | 0 => pure false
  | 1 => pure true
  | b => throw s!"invalid bool byte {b}"

private def readU16LE : DecodeM Nat := do
  let b0 ← readU8
  let b1 ← readU8
  pure (b0.toNat + (b1.toNat <<< 8))

private def readU32LE : DecodeM Nat := do
  let b0 ← readU8
  let b1 ← readU8
  let b2 ← readU8
  let b3 ← readU8
  pure (b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24))

private def readU64LE : DecodeM UInt64 := do
  let lo ← readU32LE
  let hi ← readU32LE
  pure (UInt64.ofNat (lo + (hi <<< 32)))

private def readLen : DecodeM Nat := do
  let n ← readU64LE
  pure n.toNat

private def readBytes (n : Nat) : DecodeM ByteArray := do
  let c ← get
  if c.pos + n ≤ c.bytes.size then
    set { c with pos := c.pos + n }
    pure (c.bytes.extract c.pos (c.pos + n))
  else
    throw s!"eof: need {n} bytes at offset {c.pos}"

private def readDigest : DecodeM D := do
  let bs ← readBytes 32
  match Digest.ofBytes? bs with
  | some d => pure d
  | none => throw "internal error: 32-byte digest decode failed"

private def readCanonicalF : DecodeM F := do
  let w ← readU64LE
  match Goldilocks.ofCanonical? w with
  | some x => pure x
  | none => throw s!"non-canonical Goldilocks element {w}"

private def readEF : DecodeM EF := do
  let c0 ← readCanonicalF
  let c1 ← readCanonicalF
  pure ⟨c0, c1⟩

private def readArray (n : Nat) (f : DecodeM α) : DecodeM (Array α) := do
  let c ← get
  if n > c.bytes.size - c.pos then
    throw s!"length {n} exceeds remaining {c.bytes.size - c.pos} bytes at offset {c.pos}"
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (← f)
  pure out

private def readVec (f : DecodeM α) : DecodeM (Array α) := do
  let n ← readLen
  readArray n f

private def readOption (f : DecodeM α) : DecodeM (Option α) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => some <$> f
  | b => throw s!"invalid option tag {b}"

private def ensureEOF : DecodeM Unit := do
  let c ← get
  unless c.pos == c.bytes.size do
    throw s!"trailing bytes: {c.bytes.size - c.pos} unread at offset {c.pos}"

/-! ## 1. Verifying-Key (`StarkSystem`) Decoder (v5 dense codec) -/

private def readGraphNode : DecodeM GraphNode := do
  let tag ← readU8
  match tag.toNat with
  | 0 =>
    let v ← readU16LE
    pure (.const (Goldilocks.ofUInt64 (UInt64.ofNat v)))
  | 1 =>
    let v ← readU64LE
    pure (.const (Goldilocks.ofUInt64 v))
  | 2 =>
    let idx ← readU8
    pure (.publicInput idx.toNat)
  | 3 => pure .isFirstRow
  | 4 => pure .isLastRow
  | 5 => pure .isTransition
  | 6 => pure (.add (← readU16LE) (← readU16LE))
  | 7 => pure (.sub (← readU16LE) (← readU16LE))
  | 8 => pure (.mul (← readU16LE) (← readU16LE))
  | 9 => pure (.neg (← readU16LE))
  | t =>
    if 10 ≤ t && t ≤ 15 then
      let code := t - 10
      let src := match code / 2 with
        | 0 => ColSource.preprocessed
        | 1 => ColSource.main
        | _ => ColSource.stage2
      let off := if code % 2 == 0 then RowOffset.current else RowOffset.next
      let col ← readU16LE
      pure (.var src off col)
    else
      throw s!"unknown GraphNode tag {t}"

private def readSysCircuit : DecodeM SysCircuit := do
  let mainWidth ← readU16LE
  let preprocessedWidth ← readU16LE
  let preprocessedHeight ← readU32LE
  let maxConstraintDegree ← readU16LE
  let lookupGroupSize := (← readU8).toNat
  let nodeCount ← readU16LE
  let nodes ← readArray nodeCount readGraphNode
  let zeroCount ← readU16LE
  let zeros ← readArray zeroCount readU16LE
  let lookupCount ← readU16LE
  let lookups ← readArray lookupCount do
    let multiplicity ← readU16LE
    let argCount ← readU16LE
    let args ← readArray argCount readU16LE
    pure { multiplicity, args }
  pure {
    mainWidth, preprocessedWidth, preprocessedHeight, maxConstraintDegree
    lookupGroupSize, nodes, zeros, lookups
  }

/-- Decode a v5 Multi-STARK verifying key (`crates/stark-key/src/lib.rs`). -/
def StarkSystem.fromBytes (bytes : ByteArray) : Except String StarkSystem := do
  let (sys, _) ← (do
    let params : StarkParams := {
      logBlowup := ← readU16LE
      capHeight := ← readU16LE
      logFinalPolyLen := ← readU16LE
      maxLogArity := ← readU16LE
      numQueries := ← readU16LE
      commitPowBits := ← readU16LE
      queryPowBits := ← readU16LE
    }
    let circuitCount ← readU16LE
    let circuits ← readArray circuitCount readSysCircuit
    let preprocessedCommit ← match ← readU8 with
      | 0 => pure none
      | 1 =>
        let capLen ← readU16LE
        some <$> readArray capLen readDigest
      | b => throw s!"invalid preprocessed commit flag {b}"
    let preprocessedIndices ← readArray circuitCount do
      let idx ← readU16LE
      pure (if idx == 0xFFFF then none else some idx)
    ensureEOF
    pure ({ params, circuits, preprocessedCommit, preprocessedIndices } : StarkSystem)
  ).run { bytes, pos := 0 }
  pure sys

/-! ## 2. `BatchProof` Decoder (bincode v2 `LittleEndian + Fixint`) -/

private def readMerkleCap : DecodeM (Array D) :=
  readVec readDigest

private def readPrunedPaths : DecodeM (PrunedPaths D) := do
  let siblingHashes ← readVec readDigest
  pure { siblingHashes }

private def readOpenedRound : DecodeM OpenedRound :=
  readVec (readVec (readVec readEF))

private def readBatchOpening : DecodeM (BatchOpening F (PrunedPaths D)) := do
  let openedValues ← readVec (readVec (readVec readCanonicalF))
  let openingProof ← readPrunedPaths
  pure { openedValues, openingProof }

private def readCommitPhaseStep : DecodeM (CommitPhaseStep EF (PrunedPaths D)) := do
  let logArity := (← readU8).toNat
  let siblingValues ← readVec (readVec readEF)
  let openingProof ← readPrunedPaths
  pure { logArity, siblingValues, openingProof }

private def readFriProof : DecodeM (FriProof F EF D (PrunedPaths D) (PrunedPaths D)) := do
  -- Bincode layout of `p3_fri::TwoAdicFriPcsProof` / `FriProof` (mirrors `ProofDeserialize.lean:333-358`):
  -- commit_phase_commits : Vec<MerkleCap> (for cap_height = 0 each cap has length 1)
  let commitCaps ← readVec readMerkleCap
  let mut commitPhaseCommits := Array.mkEmpty commitCaps.size
  for cap in commitCaps do
    unless cap.size == 1 do
      throw s!"expected cap length 1 in FRI commit phase, got {cap.size}"
    let some root := cap[0]? | throw "internal error: empty FRI commit cap"
    commitPhaseCommits := commitPhaseCommits.push root
  let commitPowWitnesses ← readVec readCanonicalF
  let inputOpenings ← readVec readBatchOpening
  let commitPhaseOpenings ← readVec readCommitPhaseStep
  let finalPoly ← readVec readEF
  let queryPowWitness ← readCanonicalF
  pure {
    commitPhaseCommits
    commitPowWitnesses
    inputOpenings
    commitPhaseOpenings
    finalPoly
    queryPowWitness
  }

private def readShardProof : DecodeM ShardProof := do
  let active ← readVec readBool
  let stage1Trace ← readMerkleCap
  let stage2Trace ← readMerkleCap
  let quotientChunks ← readMerkleCap
  let commitments : ShardCommitments := { stage1Trace, stage2Trace, quotientChunks }
  let intermediateAccumulators ← readVec readEF
  let logDegrees := (← readVec readU8).map UInt8.toNat
  let openingProof ← readFriProof
  let quotientOpenedValues ← readOpenedRound
  let preprocessedOpenedValues ← readOption readOpenedRound
  let stage1OpenedValues ← readOpenedRound
  let stage2OpenedValues ← readOpenedRound
  pure {
    active, commitments, intermediateAccumulators, logDegrees, openingProof
    quotientOpenedValues, preprocessedOpenedValues, stage1OpenedValues, stage2OpenedValues
  }

private def readShardHeader : DecodeM ShardHeader := do
  let active ← readVec readBool
  let stage1Trace ← readMerkleCap
  let logDegrees := (← readVec readU8).map UInt8.toNat
  let claims ← readVec (readVec readCanonicalF)
  pure { active, stage1Trace, logDegrees, claims }

private def readBatchMessage : DecodeM BatchMessage := do
  let args ← readVec readCanonicalF
  let multiplicity ← readCanonicalF
  pure { args, multiplicity }

/-- Decode a serialized `BatchProof` (`multi-stark/src/batch.rs:238-241`),
enforcing strict canonical Goldilocks values, strict tags, and exact EOF. -/
def BatchProof.fromBytes (bytes : ByteArray) : Except String BatchProof := do
  let (batch, _) ← (do
    let headers ← readVec readShardHeader
    let messages ← readVec readBatchMessage
    let proofs ← readVec readShardProof
    ensureEOF
    pure ({ preamble := { headers, messages }, proofs } : BatchProof)
  ).run { bytes, pos := 0 }
  pure batch

/-- Decode serialized expected claims (`Vec<Vec<Val>>` bincode). -/
def decodeClaims (bytes : ByteArray) : Except String (Array (Array F)) := do
  let (claims, _) ← (do
    let cs ← readVec (readVec readCanonicalF)
    ensureEOF
    pure cs
  ).run { bytes, pos := 0 }
  pure claims

end Ix.Cert.MultiStark
