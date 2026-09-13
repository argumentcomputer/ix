/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ShapedVerifier
import Tests.Aiur.EmissionReader

/-! Native shape decisions, every u8 domain exponent, independently changed
matrix dimensions, inactive circuits, fixed heights and global budgets. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader

namespace AiurTests.ProofShapes

private def readBytes : Reader ByteArray := do takeBytes (← readCount 16777216)

private def readCorpus : Reader (Nat × Nat × Nat) := do
  let header := "Aiur proof shapes v2\n".toUTF8
  unless (← takeBytes header.size) == header do throw "proof shape snapshot version differs"
  let systems ← readCount
  let mut total := 0
  let mut accepted := 0
  let mut guarded := 0
  for system in [:systems] do
    let some key := KeyCodec.decodeCanonical (← readBytes) | throw "invalid shape key"
    let count ← readCount 100000
    total := total + count
    for index in [:count] do
      let bytes ← readBytes
      let some proof := ProofCodec.decodeCanonical bytes | throw "invalid shape proof framing"
      let expected ← readOption (do readList (← readCount) readNat)
      let fixed ← readBool
      let bound ← readOption readNat
      let cap ← readBool
      let checked := ProofShape.check key proof
      unless checked.map (List.map (ProofShape.quotientDegree ∘ ProofShape.Row.circuit)) == expected do
        throw s!"native opening shape differs at system {system}, case {index}"
      unless ProofShape.fixedHeights key proof == fixed do throw "fixed proof heights differ"
      unless ProofShape.queryBound key proof == bound do throw "proof lookup budget differs"
      unless MerkleCap.check key proof == cap do throw "proof Merkle cap coverage differs"
      let ready := (BoundVerifier.readProof key bytes).isOk
      unless ready == (expected.isSome && fixed && bound.isSome && cap) do throw "checked proof guard differs"
      if checked.isSome then accepted := accepted + 1
      if ready then guarded := guarded + 1
  unless systems == 4 do throw "missing proof shape systems"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "proof shape snapshot has trailing bytes"
  return (total, accepted, guarded)

def run (path : System.FilePath) : IO Unit := do
  match readCorpus.run ((← IO.FS.readBinFile path), 0) with
  | .error error => throw (IO.userError error)
  | .ok ((total, accepted, guarded), _) =>
    unless total == 4696 && accepted == 510 do throw (IO.userError "incomplete proof shape corpus")
    IO.println s!"proof shapes: {total} native/Lean cases, {accepted} accepted shapes, {guarded} pass fixed-height and budget guards"

end AiurTests.ProofShapes

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.ProofShapes.run path
  | _ => throw (IO.userError "expected native proof shape snapshot")
