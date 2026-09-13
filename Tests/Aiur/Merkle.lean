/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Merkle
import Tests.Aiur.EmissionReader

/-! Compare binary path replay with the actual pinned MMCS verifier,
including the complete sequence of byte inputs and native BLAKE3 outputs. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.Merkle AiurTests.EmissionReader

namespace AiurTests.Merkle

private def readDigest : Reader Digest := do
  let bytes ← takeBytes 32
  if length : bytes.data.size = 32 then return ⟨bytes.data, length⟩
  else throw "incomplete Merkle digest"

private def readDigests : Reader (List Digest) := do
  readList (← readCount) readDigest

private def readCall : Reader (List UInt8 × Digest) := do
  let input ← takeBytes (← readCount 100000)
  return (input.data.toList, ← readDigest)

private def readCorpus : Reader Unit := do
  let header := "Aiur Merkle paths v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "Merkle path snapshot version differs"
  for count in [8913, 1802, 1161, 3941, 16456] do
    unless (← readNat) == count do throw "incomplete native Merkle path corpus"
  let mut accepted := 0
  let mut omitted := 0
  let mut unhashed := 0
  let mut calls := 0
  for case in [:8913] do
    let dimensions ← readList (← readCount) do
      return Dimensions.mk (← readCount) (← readCount 32)
    let capHeight ← readCount
    let index ← readCount
    let rows ← readList (← readCount) readValues
    let proof ← readDigests
    let cap ← readDigests
    let native ← readBool
    let coverage ← readBool
    let hashes ← readList (← readCount) readCall
    unless covered dimensions capHeight == coverage do throw s!"Merkle coverage differs at {case}"
    unless verify Blake3.digest dimensions capHeight index cap rows proof == native do
      throw s!"Merkle decision differs at {case}"
    unless verifyCovered Blake3.digest dimensions capHeight index cap rows proof == (native && coverage) do
      throw s!"covered Merkle decision differs at {case}"
    match replay Blake3.digest dimensions capHeight index rows proof with
    | none =>
      unless hashes.isEmpty do throw s!"native hashed a structurally rejected path at {case}"
      unhashed := unhashed + 1
    | some result =>
      unless result.hashing.inputs == hashes.map Prod.fst do
        throw s!"Merkle hash input sequence differs at {case}"
      unless result.logHeight == min capHeight (maxHeight dimensions) &&
          result.index == index / 2^proof.length do throw "Merkle final position differs"
      unless hashes.getLast?.map Prod.snd == some result.hashing.digest do
        throw s!"Merkle final digest differs at {case}"
    for (input, output) in hashes do
      unless Blake3.digest input == output do throw s!"native Merkle hash output differs at {case}"
    if native then accepted := accepted + 1
    if native && !coverage then omitted := omitted + 1
    calls := calls + hashes.length
  unless accepted == 1802 && omitted == 1161 && unhashed == 3941 && calls == 16456 do
    throw "Merkle path coverage totals differ"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "Merkle path snapshot has trailing bytes"

end AiurTests.Merkle

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.Merkle.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok _ => IO.println "Merkle paths: 8913 native/Lean decisions and 16456 hash calls match"
  | _ => throw (IO.userError "expected native Merkle path snapshot")
