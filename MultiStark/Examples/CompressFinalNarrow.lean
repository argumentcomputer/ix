import MultiStark.CompressFinalNarrow
import Lean.Data.Json

open Aiur MultiStark

private def naturals (rows : List (List String)) : IO (List (List Nat)) :=
  rows.mapM fun row => row.mapM fun value =>
    match value.toNat? with
    | some n => pure n
    | none => throw (IO.userError "invalid final configuration integer")

/-! Exports the narrow-stage terminal accumulator relation:
`compress_final_narrow_export CONFIGURATION_JSON KEY ARTIFACT`. `KEY` is the
narrow stage's packed key, embedded in the artifact; the configuration
(`aiur_packed_final_config --narrow`) carries the claim chunk headers. -/
def main (args : List String) : IO Unit := do
  let [configurationPath, keyPath, out] := args
    | throw (IO.userError "usage: compress_final_narrow_export CONFIGURATION_JSON KEY ARTIFACT")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile configurationPath))
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
  let headers ← (← naturals (← IO.ofExcept (json.getObjValAs? (List (List String)) "claim_headers"))).mapM
    fun | [tag, key, values] => pure ({ tag, key, values } : FinalNarrow.Header)
        | _ => throw (IO.userError "claim headers are [tag, key, values]")
  let bytes ← FinalNarrow.compilePackage configuration lines headers (← IO.FS.readBinFile keyPath)
  Artifact.write out bytes
  IO.println s!"Aiur narrow final accumulator package: {bytes.size} bytes"
