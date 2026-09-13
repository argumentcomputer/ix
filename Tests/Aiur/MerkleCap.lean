/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.MerkleCap
import Tests.Aiur.EmissionReader

/-! Every native degree byte, mixed/uniform/empty batches and machine
parameter boundaries for the binary Merkle cap coverage guard. -/

open Aiur.NativeAIR AiurTests.EmissionReader

private def readCorpus : Reader Unit := do
  let header := "Aiur Merkle caps v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "Merkle cap snapshot version differs"
  let parameters : List Nat := [0, 1, 2, 3, 8, 16, 31, 32, 63, 64, 255, 256, 65535, 2^64 - 256, 2^64 - 1]
  let mut total := 0
  for blowup in parameters do
    for cap in parameters do
      unless (← readBool) == MerkleCap.coverage blowup cap [] do throw "empty cap geometry differs"
      total := total + 1
      for degree in [:256] do
        for degrees in [[degree], [degree, 0], [degree, 8, 16], [degree, degree], [255, degree]] do
          unless (← readBool) == MerkleCap.coverage blowup cap degrees do
            throw s!"Merkle cap coverage differs: blowup {blowup}, cap {cap}, degrees {degrees}"
          total := total + 1
  unless total == 288225 do throw "incomplete Merkle cap cases"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "Merkle cap snapshot has trailing bytes"

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok _ => IO.println "Merkle caps: 288225 native/Lean degree and parameter cases match"
  | _ => throw (IO.userError "expected native Merkle cap snapshot")
