import Aiur.Library.Field.BN254.Pairing.Preparation
import Lean.Data.Json

open Aiur.Library.Field.BN254.Pairing

private def natural (value : String) : IO Nat :=
  match value.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid field integer")

private def rejects (value : Except String Unit) : Bool :=
  match value with | .ok _ => false | .error _ => true

def main (args : List String) : IO Unit := do
  let jsonPath := args.headD "crates/aiur/tests/fixtures/bn254-pairing-lines.json"
  let linesPath := args[1]?.getD "crates/aiur/tests/fixtures/bn254-pairing-lines.txt"
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile jsonPath))
  let raw ← IO.ofExcept (json.getObjValAs? (List (List String)) "anchor_coordinates")
  let coordinates ← raw.mapM fun point => point.mapM natural
  let anchors ← IO.ofExcept (match json.getObjValAs? (List Nat) "anchor_bytes" with
    | .ok value => .ok value
    | .error _ => json.getObjValAs? (List Nat) "anchors")
  let text ← IO.FS.readFile linesPath
  let candidate ← (text.splitOn "\n" |>.filter (!·.isEmpty)).mapM fun row =>
    (row.splitOn " ").mapM natural
  IO.ofExcept (Preparation.validate coordinates anchors candidate)
  let altered := candidate.modify 0 (fun row => row.modify 3 (· + 1))
  unless rejects (Preparation.validate coordinates anchors altered) do
    throw (IO.userError "altered pairing coefficient accepted")
  unless rejects (Preparation.validate coordinates (anchors.modify 0 (fun n => (n+1)%256)) candidate) do
    throw (IO.userError "altered pairing anchor accepted")
  unless rejects (Preparation.validate [[0,0,0,0],[0,0,0,0]] anchors candidate) do
    throw (IO.userError "invalid G2 coordinates accepted")
  IO.println s!"validated {candidate.length} pairing lines and anchor/line rejection cases"
