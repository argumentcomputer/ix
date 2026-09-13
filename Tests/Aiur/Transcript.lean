/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Transcript
import Ix.Aiur.Proofs.Blake3
import Tests.Aiur.EmissionReader
import Blake3.Rust

/-! Comparison with the instrumented native verifier, including challenger
calls in PCS verification. Replay uses the checked concrete Blake3 hash;
the test also compares it with the independent FFI implementation.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open NativeAIR.Challenger

namespace AiurTests.Transcript

private def nativeHash (bytes : List UInt8) : Fin 32 → UInt8 :=
  let digest := Blake3.Rust.hash bytes.toByteArray
  fun index => digest.val[index.val]'(by simpa only [digest.property] using index.isLt)

private def pureHash : Hash32 := NativeAIR.Blake3.hash

private def readBytes : Reader (List UInt8) := do
  return (← takeBytes (← readCount 10000000)).data.toList

private inductive Event where
  | observe (bytes : List UInt8)
  | field (value : G)
  | bits (count value : Nat)
  | byte (value : UInt8)
  deriving DecidableEq, Repr

private def readEvent : Reader Event := do
  match ← readNat 1 with
  | 0 => return .observe (← readBytes)
  | 1 => return .field (← readField)
  | 2 => return .bits (← readNat) (← readNat)
  | 3 => return .byte (← readNat 1).toUInt8
  | _ => throw "invalid transcript event"

private def runEvent (state : State) (event : Event) : Except String State := do
  match event with
  | .observe bytes => return observeBytes state bytes
  | .field expected =>
    unless sampleField pureHash 16 state == sampleField nativeHash 16 state do throw "pure/FFI field sampling differs"
    let some (actual, next) := sampleField pureHash 16 state | throw "native transcript field exhausted"
    unless actual == expected do throw "native transcript field differs"
    return next
  | .bits bits expected =>
    unless sampleBits pureHash bits state == sampleBits nativeHash bits state do throw "pure/FFI bit sampling differs"
    let some (actual, next) := sampleBits pureHash bits state | throw "native transcript bit count invalid"
    unless actual == expected do throw "native transcript bits differ"
    return next
  | .byte expected =>
    unless sampleByte pureHash state == sampleByte nativeHash state do throw "pure/FFI byte sampling differs"
    let (actual, next) := sampleByte pureHash state
    unless actual == expected do throw "native transcript byte differs"
    return next

private def observed : List Event → List UInt8 × List Event
  | .observe bytes :: rest =>
    let (more, remaining) := observed rest
    (bytes ++ more, remaining)
  | rest => ([], rest)

private def stage (expected : List UInt8) (value : ProofCodec.Extension) (events : List Event) :
    Except String (List Event) := do
  let (bytes, rest) := observed events
  unless bytes == expected do throw "native transcript observation schedule differs"
  match rest with
  | .field c0 :: .field c1 :: rest =>
    unless c0 == value.c0 && c1 == value.c1 do throw "native transcript extension basis order differs"
    return rest
  | _ => throw "native transcript extension sample missing"

private def checkSchedule (key : KeyCodec.Key) (proof : ProofCodec.Data) (claims : List (List G))
    (result : NativeAIR.Transcript.Replay) (events : List Event) : Except String (List Event) := do
  let ch := result.challenges
  let rest ← stage (NativeAIR.Transcript.prefixBytes key proof claims) ch.beta events
  let rest ← stage (ProofCodec.encodeExtension ch.beta) ch.gamma rest
  let rest ← stage (ProofCodec.encodeExtension ch.gamma ++ proof.commitments.stage2.flatten ++
    proof.accumulators.flatMap ProofCodec.encodeExtension) ch.alpha rest
  stage proof.commitments.quotient.flatten ch.zeta rest

private def readStreams : Reader Unit := do
  unless (← readNat) == 16 do throw "incomplete byte-stream cases"
  for seed in [:16] do
    let bytes ← readBytes
    unless bytes.length == seed * 17 do throw "byte-stream seed length differs"
    unless (← readNat) == 80 do throw "incomplete byte-stream operations"
    let events ← readList 80 readEvent
    let final ← ofExcept (events.foldlM runEvent (initial bytes))
    unless final.pending.length ≤ 32 do throw "byte-stream pending buffer oversized"

private def readRejections : Reader Unit := do
  unless (← readNat) == 16 do throw "incomplete rejection cases"
  let mut rejected := 0
  for mask in [:16] do
    unless (← readNat 1) == mask do throw "rejection mask differs"
    let first ← takeBytes 32
    let later ← takeBytes 32
    let hash : Hash32 := fun input index =>
      (if input.length == 1 then first else later)[index.val]!
    let c0 ← readField
    let c1 ← readField
    let firstAttempts ← readCount 5
    let secondAttempts ← readCount 4
    unless firstAttempts > 0 && secondAttempts > 0 do throw "zero rejection attempts"
    rejected := rejected + firstAttempts + secondAttempts - 2
    let start := initial [mask.toUInt8]
    let some (actual0, middle) := sampleField hash firstAttempts start | throw "forced first field exhausted"
    let some (actual1, final) := sampleField hash secondAttempts middle | throw "forced second field exhausted"
    unless actual0 == c0 && actual1 == c1 do throw "forced canonical/rejected limb differs"
    unless (sampleField hash (firstAttempts - 1) start).isNone &&
      (sampleField hash (secondAttempts - 1) middle).isNone do throw "rejection sampler returned too early"
    unless sampleExtension hash 5 start == some (⟨c0, c1⟩, final) do throw "forced extension sample differs"
    unless (sampleExtension hash (max firstAttempts secondAttempts - 1) start).isNone do
      throw "extension sampler bypassed exhausted coordinate"
    let mut state := final
    for bits in [0, 1, 7, 31, 32, 63] do
      let expected ← readNat
      let some (actual, next) := sampleBits hash bits state | throw "forced bit sample invalid"
      unless actual == expected do throw "forced sampling continuation differs"
      state := next
    for invalid in [64, 65, 100] do
      unless (sampleBits hash invalid state).isNone do throw "oversized bit sample accepted"
  unless rejected == 26 do throw s!"incomplete forced rejection coverage: {rejected}"
  let noncanonical : Hash32 := fun _ _ => 255
  unless (sampleField noncanonical 32 (initial [])).isNone do throw "exhausted sampler fabricated a field"

private def readWitnesses : Reader Unit := do
  unless (← readNat) == 48 do throw "incomplete witness cases"
  let mut zeroBits := 0
  for _ in [:48] do
    let seed ← readBytes
    let before ← readField
    let bits ← readNat
    let witness ← readField
    let accepted ← readBool
    let after ← readField
    let some (actualBefore, state) := sampleField pureHash 16 (initial seed) | throw "witness prelude exhausted"
    unless actualBefore == before do throw "witness prelude sample differs"
    let some (actual, next) := checkWitness pureHash bits witness state | throw "witness check undefined"
    unless actual == accepted do throw "witness acceptance differs"
    if bits == 0 then
      zeroBits := zeroBits + 1
      unless next == state do throw "zero-bit witness changed pending output"
    let some (actualAfter, _) := sampleField pureHash 16 next | throw "witness continuation exhausted"
    unless actualAfter == after do throw "witness continuation differs"
  unless zeroBits == 8 do throw "incomplete zero-bit witness coverage"

private def readVerifiers : Reader Unit := do
  unless (← readNat) == 40 do throw "incomplete native verifier cases"
  let mut acceptedCount := 0
  let mut eventCount := 0
  let mut pcsCount := 0
  for index in [:40] do
    let keyBytes := (← readBytes).toByteArray
    let proofBytes := (← readBytes).toByteArray
    let some key := KeyCodec.decodeCanonical keyBytes | throw "transcript key is not canonical"
    let some proof := ProofCodec.decodeCanonical proofBytes | throw "transcript proof is not canonical"
    let claims ← readList (← readCount) readValues
    let accepted ← readBool
    unless accepted == (index % 10 == 0) do throw "native verifier acceptance inventory differs"
    let events ← readList (← readCount 100000) readEvent
    eventCount := eventCount + events.length
    let some result := NativeAIR.Blake3.replay 16 key proof claims | throw "transcript replay exhausted"
    unless NativeAIR.Transcript.replay nativeHash 16 key proof claims == some result do
      throw "pure/FFI transcript replay differs"
    let pcs ← ofExcept (checkSchedule key proof claims result events)
    pcsCount := pcsCount + pcs.length
    unless !pcs.isEmpty do throw "native PCS continuation missing"
    let continued ← ofExcept (pcs.foldlM runEvent result.state)
    let all ← ofExcept (events.foldlM runEvent (initial (NativeAIR.Transcript.seed key.parameters)))
    unless continued == all do throw "PCS received a different challenger state"
    unless NativeAIR.Blake3.replay 32 key proof claims == some result do
      throw "larger replay fuel changed native challenges/state"
    unless (NativeAIR.Blake3.replay 0 key proof claims).isNone do throw "zero replay fuel accepted"
    let some rows := ProofShape.check key proof | throw "native transcript fixture has invalid shape"
    if accepted then
      acceptedCount := acceptedCount + 1
      unless NativeAIR.Blake3.verifyArithmetic 16 key proof claims rows == some result do
        throw "native accepted proof fails transcript-derived arithmetic"
  unless acceptedCount == 4 do throw "incomplete accepted transcript proofs"
  unless eventCount > 1000 && pcsCount > 500 do throw "incomplete native transcript/PCS calls"

private def readCorpus : Reader Unit := do
  let header := "Aiur transcript v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "transcript snapshot version differs"
  readStreams
  readRejections
  readWitnesses
  readVerifiers
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "transcript snapshot has trailing bytes"

end AiurTests.Transcript

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let bytes ← IO.FS.readBinFile path
    match AiurTests.Transcript.readCorpus.run (bytes, 0) with
    | .error error => throw (IO.userError error)
    | .ok _ =>
      IO.println "transcript: 1280 byte operations, 16 forced rejection cases and 48 witness checks match"
      IO.println "transcript: pure Blake3 matches FFI and 40 native verifier schedules/PCS continuations; 4 accepted proofs satisfy derived arithmetic"
  | _ => throw (IO.userError "expected native transcript snapshot")
