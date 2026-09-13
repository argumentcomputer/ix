/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ShapedVerifier
import Tests.Aiur.EmissionReader

/-! Native serde decisions and every field of honest and malformed proofs. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader

namespace AiurTests.ProofBytes

private def vector (item : α → List Nat) (values : List α) : List Nat :=
  values.length :: values.flatMap item

private def extension (value : ProofCodec.Extension) : List Nat := [value.c0.n, value.c1.n]

private def hashes (values : ProofCodec.Cap) : List Nat := vector (List.map UInt8.toNat) values

private def openings (item : α → List Nat) (values : ProofCodec.Openings α) : List Nat :=
  vector (vector (vector item)) values

private def view (value : ProofCodec.Data) : List Nat :=
  vector (fun degree => [degree.toNat]) value.logDegrees ++
  vector (fun active => [if active then 1 else 0]) value.active ++
  openings extension value.stage2 ++ openings extension value.stage1 ++
  (match value.preprocessed with | none => [0] | some values => 1 :: openings extension values) ++
  openings extension value.quotient ++ vector extension value.accumulators ++
  hashes value.commitments.quotient ++ hashes value.commitments.stage2 ++ hashes value.commitments.stage1 ++
  [value.fri.queryPowWitness.n] ++ vector extension value.fri.finalPoly ++
  vector (fun step => hashes step.siblingHashes ++ vector (vector extension) step.siblingValues ++
    [step.logArity.toNat]) value.fri.commitOpenings ++
  vector (fun batch => hashes batch.siblingHashes ++ openings (fun x => [x.n]) batch.values) value.fri.inputOpenings ++
  vector (fun x => [x.n]) value.fri.commitPowWitnesses ++ vector hashes value.fri.commits

private def readBytes : Reader ByteArray := do takeBytes (← readCount 16777216)

private def readCorpus : Reader (Nat × Nat × Nat) := do
  let header := "Aiur proof codec v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "proof codec snapshot version differs"
  let keys ← readList (← readCount) readBytes
  unless keys.length == 4 do throw "missing honest proof systems"
  let keys ← keys.mapM fun bytes => do
    let some key := KeyCodec.decodeCanonical bytes | throw "honest proof key is not canonical"
    return key
  let count ← readCount 100000
  let mut accepted := 0
  let mut suffixed := 0
  for index in [:count] do
    let bytes ← readBytes
    let expected ← readBool
    let parsed := ProofCodec.readData bytes.data.toList
    unless parsed.isSome == expected do throw s!"native proof parsing differs at case {index}"
    if expected then
      let some (value, rest) := parsed | throw "missing parsed proof"
      let canonical ← readBytes
      let words ← readList (← readCount 16777216) readNat
      unless view value == words do throw s!"native proof fields differ at case {index}"
      unless ProofCodec.encode value == canonical do throw s!"native proof encoding differs at case {index}"
      if accepted % 5 == 0 then
        let some key := keys[accepted / 5]? | throw "missing honest proof key"
        unless (BoundVerifier.readProof key canonical).isOk do throw "honest proof fails checked shape guards"
      unless ProofCodec.decodeCanonical canonical == some value do throw "canonical proof round trip failed"
      unless (ProofCodec.decodeCanonical bytes).isSome == (bytes == canonical) do
        throw "canonical proof framing differs"
      unless (ProofCodec.decode bytes).isSome == rest.isEmpty do throw "proof suffix framing differs"
      accepted := accepted + 1
      if !rest.isEmpty then suffixed := suffixed + 1
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "proof codec snapshot has trailing bytes"
  return (count, accepted, suffixed)

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((count, accepted, suffixed), _) =>
    unless count == 3636 && accepted == 20 && suffixed == 8 do
      throw (IO.userError "incomplete proof codec corpus")
    IO.println s!"proof codec: {count} native/Lean byte cases, {accepted} decoded field records, {suffixed} native suffixes rejected by exact framing"

end AiurTests.ProofBytes

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.ProofBytes.run path
  | _ => throw (IO.userError "expected native proof codec snapshot")
