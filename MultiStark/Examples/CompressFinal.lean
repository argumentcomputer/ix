import MultiStark.CompressFinal
import Lean.Data.Json

open Aiur MultiStark

private def naturals (rows : List (List String)) : IO (List (List Nat)) :=
  rows.mapM fun row => row.mapM fun value =>
    match value.toNat? with
    | some n => pure n
    | none => throw (IO.userError "invalid final configuration integer")

def main (args : List String) : IO Unit := do
  unless args.length ≥ 2 do
    throw (IO.userError "usage: compress_final_export CONFIGURATION_JSON ARTIFACT [--check] [--no-trace]")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile args[0]!))
  let format ← IO.ofExcept (json.getObjValAs? String "format")
  unless format == "ix-aiur-final-configuration-v1" do
    throw (IO.userError "unsupported final configuration format")
  let configuration : Final.Configuration := {
    policyDigest := ← IO.ofExcept (json.getObjValAs? (List Nat) "policy_digest")
    anchors := ← IO.ofExcept (json.getObjValAs? (List Nat) "anchors")
    anchorCoordinates := ← naturals (← IO.ofExcept (json.getObjValAs? (List (List String)) "anchor_coordinates"))
    minStage := ← IO.ofExcept (json.getObjValAs? Nat "min_stage")
    maxStage := ← IO.ofExcept (json.getObjValAs? Nat "max_stage") }
  let lines ← naturals (← IO.ofExcept (json.getObjValAs? (List (List String)) "lines"))
  let bytes ← Final.compilePackage configuration lines (!(args.contains "--no-trace"))
  if args.contains "--check" then
    unless bytes.data == (← IO.FS.readBinFile args[1]!).data do
      throw (IO.userError "final fixture differs from its Lean export")
  else Artifact.write args[1]! bytes
  IO.println s!"Aiur final compression package: {bytes.size} bytes"
