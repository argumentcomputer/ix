/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Blake3
import Tests.Aiur.EmissionReader

/-! Compare the total checked hash with the pinned native unkeyed hasher,
Plonky3 wrapper, chunk CVs, and internal parent operations. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.Blake3 AiurTests.EmissionReader

namespace AiurTests.Blake3

private def readBytes : Reader (List UInt8) := do
  return (← takeBytes (← readCount 10000000)).data.toList

private def readDigest : Reader Digest := do
  let bytes ← takeBytes 32
  if length : bytes.data.size = 32 then return ⟨bytes.data, length⟩
  else throw "incomplete Blake3 digest"

private def digestCV (bytes : Digest) : CV :=
  Vector.ofFn fun word => bytesWord (Vector.ofFn fun byte : Fin 4 => bytes[word.val * 4 + byte.val])

private def readHashes : Reader Unit := do
  unless (← readNat) == 258 do throw "incomplete Blake3 hash cases"
  let mut parents := 0
  for _ in [:258] do
    let input ← readBytes
    let expected ← readDigest
    unless digest input == expected do throw s!"Blake3 digest differs at {input.length} bytes"
    unless List.ofFn (hash input) == expected.toList do throw "Blake3 transcript byte order differs"
    if input.length > 1024 then
      parents := parents + 1
      let split ← readNat
      unless leftLen input.length == split do throw "Blake3 canonical split differs"
      let left ← readDigest
      let right ← readDigest
      unless cvBytes (subtree 0 (input.take split)).chainingValue == left do throw "Blake3 left subtree differs"
      unless cvBytes (subtree (split / 1024) (input.drop split)).chainingValue == right do throw "Blake3 right subtree differs"
      unless (parentOutput (digestCV left) (digestCV right)).rootHash == expected do throw "Blake3 root parent differs"
  unless parents == 58 do throw "incomplete Blake3 tree cases"

private def readChunks : Reader Unit := do
  unless (← readNat) == 42 do throw "incomplete Blake3 chunk cases"
  let mut highCounters := 0
  for _ in [:42] do
    let counter ← readNat
    let input ← readBytes
    let expected ← readDigest
    unless input.length > 0 && input.length ≤ 1024 && counter < 2^54 do throw "inadmissible native chunk case"
    if counter ≥ 2^32 then highCounters := highCounters + 1
    let output := chunkOutput counter.toUInt64 input
    unless cvBytes output.chainingValue == expected do throw s!"Blake3 chunk differs at {counter}, {input.length}"
    unless output.counter.toNat == counter do throw "Blake3 chunk counter changed"
    unless output.blockLen.toNat == (input.length - 1) % 64 + 1 do throw "Blake3 final block length differs"
    unless output.flags == (if input.length ≤ 64 then 3 else 2) do throw "Blake3 chunk flags differ"
  unless highCounters == 12 do throw "incomplete 64-bit chunk counters"

private def readParents : Reader Unit := do
  unless (← readNat) == 64 do throw "incomplete Blake3 parent cases"
  for _ in [:64] do
    let left ← readDigest
    let right ← readDigest
    let cv ← readDigest
    let root ← readDigest
    let merkle ← readDigest
    let parent := parentOutput (digestCV left) (digestCV right)
    unless cvBytes parent.chainingValue == cv do throw "Blake3 internal parent CV differs"
    unless parent.rootHash == root do throw "Blake3 internal parent root differs"
    unless digest (left.toList ++ right.toList) == merkle do throw "Blake3 PCS Merkle pair differs"
    unless root != merkle do throw "missing distinction between internal parent and Merkle hash"
    unless cvBytes (digestCV left) == left && cvBytes (digestCV right) == right do throw "Blake3 CV byte packing differs"

private def readCorpus : Reader Unit := do
  let header := "Aiur Blake3 v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "Blake3 snapshot version differs"
  readHashes
  readChunks
  readParents
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "Blake3 snapshot has trailing bytes"

end AiurTests.Blake3

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let bytes ← IO.FS.readBinFile path
    match AiurTests.Blake3.readCorpus.run (bytes, 0) with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "Blake3: 258 full hashes, 58 subtree splits, 42 chunks and 64 parent/Merkle cases match native"
  | _ => throw (IO.userError "expected native Blake3 snapshot")
