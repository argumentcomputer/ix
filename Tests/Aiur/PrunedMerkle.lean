/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.PrunedMerkle
import Ix.Aiur.Proofs.PrunedMerkle
import Tests.Aiur.EmissionReader

/-! Actual native shared openings, complete logs on success and failure,
and reconstructed individual paths with their queried-input inclusion. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.PrunedMerkle AiurTests.EmissionReader

namespace AiurTests.PrunedMerkle

private def readDigest : Reader Merkle.Digest := do
  let bytes ← takeBytes 32
  if length : bytes.data.size = 32 then return ⟨bytes.data, length⟩
  else throw "incomplete shared Merkle digest"

private def readDigests : Reader (List Merkle.Digest) := do
  readList (← readCount) readDigest

private def readCall : Reader (List UInt8 × Merkle.Digest) := do
  let input ← takeBytes (← readCount 100000)
  return (input.data.toList, ← readDigest)

private def readCorpus : Reader Nat := do
  let header := "Aiur pruned Merkle v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "shared Merkle snapshot version differs"
  let expected ← readList 6 readNat
  let cases := expected[0]!
  unless expected == [7946, 1619, 1069, 3854, 2534, 42803] do throw "incomplete shared Merkle corpus"
  let mut accepted := 0
  let mut omitted := 0
  let mut unhashed := 0
  let mut late := 0
  let mut calls := 0
  let mut paths := 0
  for case in [:cases] do
    let dimensions ← readList (← readCount) do
      return Merkle.Dimensions.mk (← readCount) (← readCount 32)
    let capHeight ← readCount
    let indices ← readList (← readCount) readNat
    let rows ← readList (← readCount) do readList (← readCount) readValues
    let proof ← readDigests
    let cap ← readDigests
    let native ← readBool
    let coverage ← readBool
    let hashes ← readList (← readCount) readCall
    let result := replay Blake3.digest dimensions capHeight indices rows proof
    unless result.inputs == hashes.map Prod.fst do
      throw s!"shared Merkle hash input sequence differs at {case}"
    unless verify Blake3.digest dimensions capHeight indices cap rows proof == native do
      throw s!"shared Merkle decision differs at {case}"
    unless Merkle.covered dimensions capHeight == coverage do throw "shared Merkle coverage differs"
    unless verifyCovered Blake3.digest dimensions capHeight indices cap rows proof == (native && coverage) do
      throw "covered shared Merkle decision differs"
    for (input, output) in hashes do
      unless Blake3.digest input == output do throw s!"shared native hash output differs at {case}"
    if let some nodes := result.result then
      let tickets := nodes.flatMap Node.tickets
      unless tickets.length == (uniqueIndices indices).length do throw "shared ticket count differs"
      for (index, values) in indices.zip rows do
        unless tickets.any (fun ticket => ticket.index == index && ticket.rows == values) do
          throw "shared reconstruction lost a query"
      for node in nodes do
        for ticket in node.tickets do
          let some path := Merkle.replay Blake3.digest dimensions capHeight ticket.index ticket.rows ticket.proof
            | throw "shared reconstruction has an invalid individual path"
          unless path.index == node.index && path.hashing.digest == node.digest do
            throw "shared reconstruction reaches a different node"
          unless path.hashing.inputs.all result.inputs.contains do
            throw "shared reconstruction uses an unrecorded hash input"
          paths := paths + 1
    if native then accepted := accepted + 1
    if native && !coverage then omitted := omitted + 1
    if hashes.isEmpty then unhashed := unhashed + 1
    if !native && !hashes.isEmpty then late := late + 1
    calls := calls + hashes.length
  unless expected == [cases, accepted, omitted, unhashed, late, calls] do
    throw "shared Merkle coverage totals differ"
  unless paths == 19709 do throw "incomplete reconstructed individual paths"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "shared Merkle snapshot has trailing bytes"
  return paths

end AiurTests.PrunedMerkle

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.PrunedMerkle.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (paths, _) => IO.println s!"Shared Merkle: 7946 native decisions, 42803 hash calls and {paths} individual paths match"
  | _ => throw (IO.userError "expected native shared Merkle snapshot")
