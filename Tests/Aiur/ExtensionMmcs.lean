/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExtensionMmcs
import Tests.Aiur.EmissionReader

/-! Both native extension MMCS methods, their base-field delegation and
complete hash logs, including release-mode width multiplication overflow. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.ExtensionMmcs

private def readExtension : Reader Extension := do return ⟨← readField, ← readField⟩

private def readDigest : Reader Merkle.Digest := do
  let bytes ← takeBytes 32
  if length : bytes.data.size = 32 then return ⟨bytes.data, length⟩
  else throw "incomplete extension MMCS digest"

private def readDigests : Reader (List Merkle.Digest) := do readList (← readCount) readDigest

private def readCall : Reader (List UInt8 × Merkle.Digest) := do
  let input ← takeBytes (← readCount 100000)
  return (input.data.toList, ← readDigest)

private def readCorpus : Reader Nat := do
  let header := "Aiur extension MMCS v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "extension MMCS snapshot version differs"
  let wordBits ← readCount
  unless wordBits == 32 || wordBits == 64 do throw "unsupported extension MMCS machine width"
  let expected ← readList 7 readNat
  let cases := expected[0]!
  unless expected == [9597, 7362, 2566, 1661, 507, 3513, 42969] do
    throw "incomplete extension MMCS corpus"
  let mut shared := 0
  let mut accepted := 0
  let mut omitted := 0
  let mut overflow := 0
  let mut late := 0
  let mut calls := 0
  let mut paths := 0
  for case in [:cases] do
    let multi ← readBool
    let dimensions ← readList (← readCount) do
      return Merkle.Dimensions.mk (← readNat) (← readCount 32)
    unless dimensions.all (fun dim => dim.width < 2^wordBits) do
      throw "extension MMCS width is not machine-representable"
    let capHeight ← readCount
    let indices ← readList (← readCount) readNat
    let rows ← readList (← readCount) do
      readList (← readCount) do readList (← readCount) readExtension
    let proof ← readDigests
    let cap ← readDigests
    let native ← readBool
    let covered ← readBool
    let widthsFit ← readBool
    let hashes ← readList (← readCount) readCall
    unless (dimensions.all fun dim => dim.width * 2 < 2^wordBits) == widthsFit do
      throw "extension MMCS width overflow differs"
    unless Merkle.covered dimensions capHeight == covered do throw "extension MMCS cap coverage differs"
    let inputs ← if multi then do
      let result := ExtensionMmcs.replayMulti Blake3.digest wordBits dimensions capHeight indices rows proof
      unless ExtensionMmcs.verifyMulti Blake3.digest wordBits dimensions capHeight indices cap rows proof == native do
        throw s!"extension shared decision differs at {case}"
      unless ExtensionMmcs.verifyMultiCovered Blake3.digest wordBits dimensions capHeight indices cap rows proof ==
          (native && covered) do throw "covered extension shared decision differs"
      if let some nodes := result.result then
        let tickets := nodes.flatMap PrunedMerkle.Node.tickets
        unless tickets.length == (PrunedMerkle.uniqueIndices indices).length do
          throw "extension shared ticket count differs"
        for (index, query) in indices.zip rows do
          unless tickets.any (fun ticket => ticket.index == index && ticket.rows == ExtensionMmcs.baseRows query) do
            throw "extension shared reconstruction lost a query"
        for node in nodes do
          for ticket in node.tickets do
            let some (_, query) := (indices.zip rows).find? fun (index, values) =>
                index == ticket.index && ExtensionMmcs.baseRows values == ticket.rows
              | throw "extension shared path lost its original query"
            let some path := ExtensionMmcs.replay Blake3.digest wordBits dimensions capHeight ticket.index query ticket.proof
              | throw "extension shared path is not individually valid"
            unless path.index == node.index && path.hashing.digest == node.digest do
              throw "extension shared path reaches a different node"
            unless path.hashing.inputs.all result.inputs.contains do
              throw "extension shared path uses an unrecorded input"
            paths := paths + 1
      pure result.inputs
    else do
      let [index] := indices | throw "individual extension MMCS has wrong index count"
      let [values] := rows | throw "individual extension MMCS has wrong query count"
      unless ExtensionMmcs.verify Blake3.digest wordBits dimensions capHeight index cap values proof == native do
        throw s!"extension individual decision differs at {case}"
      unless ExtensionMmcs.verifyCovered Blake3.digest wordBits dimensions capHeight index cap values proof ==
          (native && covered) do throw "covered extension individual decision differs"
      match ExtensionMmcs.replay Blake3.digest wordBits dimensions capHeight index values proof with
      | none => pure []
      | some result => paths := paths + 1; pure result.hashing.inputs
    unless inputs == hashes.map Prod.fst do throw s!"extension MMCS hash sequence differs at {case}"
    for (input, output) in hashes do
      unless Blake3.digest input == output do throw "extension MMCS native hash differs"
    if widthsFit then
      for values in rows do
        unless ExtensionMmcs.shape dimensions values ==
            Merkle.shape (ExtensionMmcs.baseDimensions wordBits dimensions) (ExtensionMmcs.baseRows values) do
          throw "extension row shape differs from bounded base row shape"
    if multi then shared := shared + 1
    if native then accepted := accepted + 1
    if native && !covered then omitted := omitted + 1
    if !widthsFit then overflow := overflow + 1
    if !native && !hashes.isEmpty then late := late + 1
    calls := calls + hashes.length
  unless expected == [cases, shared, accepted, omitted, overflow, late, calls] do
    throw "extension MMCS coverage totals differ"
  unless paths == 20448 do throw "incomplete extension MMCS individual paths"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "extension MMCS snapshot has trailing bytes"
  return paths

end AiurTests.ExtensionMmcs

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.ExtensionMmcs.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (paths, _) => IO.println s!"Extension MMCS: 9597 native decisions, 42969 hash calls and {paths} individual paths match"
  | _ => throw (IO.userError "expected native extension MMCS snapshot")
