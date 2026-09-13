/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.KeyCodec
import Tests.Aiur.EmissionReader

/-! Native v5 keys, canonicalization, derived metadata and malformed bytes. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader

namespace AiurTests.KeyBytes

private def readBytes : Reader ByteArray := do takeBytes (← readCount 1048576)

private def readCorpus : Reader (Nat × Nat × Nat × Nat) := do
  let header := "Aiur key codec v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "key codec snapshot version differs"
  let count ← readCount 100000
  let mut accepted := 0
  let mut noncanonical := 0
  let mut circuits := 0
  for index in [:count] do
    let bytes ← readBytes
    let expected ← readBool
    let decoded := KeyCodec.decode bytes
    unless decoded.isSome == expected do throw s!"key decoder decision differs at case {index}"
    if expected then
      let some key := decoded | throw "accepted key missing"
      accepted := accepted + 1
      let canonical ← readBytes
      unless KeyCodec.encode key == canonical do throw s!"key canonical bytes differ at case {index}"
      unless KeyCodec.decode canonical == some key do throw s!"key round trip differs at case {index}"
      unless (KeyCodec.decodeCanonical bytes).isSome == (bytes == canonical) do
        throw s!"canonical key decision differs at case {index}"
      if bytes != canonical then noncanonical := noncanonical + 1
      unless (← readCount) == key.circuits.length do throw "key circuit count differs"
      unless key.preprocessedIndices.length == key.circuits.length do throw "key index count differs"
      for circuit in key.circuits do
        circuits := circuits + 1
        let some degrees := KeyCodec.nodeDegreesFrom circuit.graph.nodes #[]
          | throw "accepted key has undefined node degrees"
        let some roots := circuit.graph.zeros.mapM (fun root => degrees[root]?)
          | throw "accepted key has undefined root degrees"
        let metadata := [circuit.mainWidth, circuit.preprocessedWidth, circuit.preprocessedHeight,
          circuit.maxConstraintDegree, circuit.lookupGroupSize, circuit.widths.stage2, circuit.widths.publics,
          circuit.constraintCount, circuit.graph.lookupPrefix, roots.foldr max 0]
        unless (← readList 10 readNat) == metadata do throw s!"derived key metadata differs at case {index}"
        unless (← readList (← readCount 65536) readNat) == degrees.toList do
          throw s!"key node degrees differ at case {index}"
        unless circuit.computedDegree == some circuit.maxConstraintDegree do
          throw "accepted key maximum degree differs"
        unless (checkedGraphPrefix circuit.widths circuit.graph).isSome do
          throw "accepted key has invalid graph reads"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "key codec snapshot has trailing bytes"
  return (count, accepted, noncanonical, circuits)

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((count, accepted, noncanonical, circuits), _) =>
    unless count == 4536 && accepted == 509 && noncanonical == 22 && circuits == 517 do
      throw (IO.userError "incomplete key codec corpus")
    IO.println s!"key codec: {count} native/Lean cases, {accepted} accepted, {noncanonical} noncanonical, {circuits} circuits match"

end AiurTests.KeyBytes

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.KeyBytes.run path
  | _ => throw (IO.userError "expected native key codec snapshot")
