import Compilatrix.Ixby.Catalog
import Compilatrix.Ixby.Report
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.Ixby Compilatrix.Tools.Check

private def freeze (keys output : System.FilePath) : IO Unit := do
  need (!(← output.pathExists)) "frozen module output already exists"
  let ixvm ← IO.FS.readBinFile (keys / "ixvm.vk")
  let aggregate ← IO.FS.readBinFile (keys / "aggr.vk")
  need (ixvm.size == 744159 && (Ixon.Address.blake3 ixvm).toHex ==
    "3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063") "fixed IxVM key differs"
  need (aggregate.size == 181630 && (Ixon.Address.blake3 aggregate).toHex ==
    "75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e") "fixed aggregate key differs"
  let word := fun n => ByteArray.mk ((List.range 8).map (fun i => UInt8.ofNat (n / 256 ^ i % 256))).toArray
  let allowed := (Ixon.Address.blake3 ixvm).hash ++ word 755 ++
    (Ixon.Address.blake3 aggregate).hash ++ word 243
  need (allowed.size == 80 && (Ixon.Address.blake3 allowed).toHex ==
    "224668baa32c9e827a1751513d8976836f6e3d9aba3f1b3cca5c9cbd1b7ff19b") "allowed identity differs"
  let file ← IO.FS.Handle.mk output .write
  file.putStr (← IO.FS.readFile (keys / "Freeze.lean"))
  file.putStr "\nset_option maxRecDepth 8192\nset_option maxHeartbeats 0\nnamespace CompilatrixStage2Fixture\n\n"
  -- Constructor data only: byte payloads and bounded list segments. No key
  -- decoder, file loader, concatenation loop, or key generator is a guest callee.
  for i in [:256] do
    file.putStr s!"def b{i} : UInt8 := ⟨⟨⟨{i}, by decide⟩⟩⟩\n"
  for (name, bytes) in [("frozenIxvmKey", ixvm), ("frozenAggregateKey", aggregate)] do
    file.putStr s!"freeze_stage2_data {name} \"{byteHex bytes.data}\"\n\n"
  file.putStr "open MultiStark.Verify\n\nstage2_def initBenchmarkSourceConfig : SourceConfig := {\n  aggregate := {\n    ixvmKey := frozenIxvmKey,\n    verifyClaimEntry := Ix.Ixby.Goldilocks.reduce 755,\n    aggregateKey := frozenAggregateKey,\n    aggregateEntry := Ix.Ixby.Goldilocks.reduce 243 },\n  decode := { bytes := 16777216, vector := 1048576, items := 2097152 },\n  verifier := {\n    queries := 1024,\n    foldArity := 256,\n    transcript := { observationBytes := 16777216, sampleAttempts := 64 } } }\n\nstage2_def initStage2Guest : Bytes → Bytes → Option Bytes :=\n  fun publicClaim proofBytes => claimBytesWrapper initBenchmarkSourceConfig publicClaim proofBytes\n\nend CompilatrixStage2Fixture\n"
  file.flush
  IO.println s!"frozen Stage2 source: 925789 key bytes, entrypoints 755/243, 2 runtime arguments"

def main (args : List String) : IO UInt32 := cli "source-ixby-stage2" do
  if let ["--freeze", keys, output] := args then
    freeze keys output
    return
  let [directory, output] := args |
    throw (IO.userError "usage: source-ixby-stage2 <fixture-directory> <new-output-directory>; or --freeze <fixture-directory> <new-source.lean>")
  let directory : System.FilePath := directory
  let output : System.FilePath := output
  need (!(← output.pathExists)) "Stage2 report requires a new directory"
  let metadata ← readJson (directory / "fixture.json")
  IO.FS.createDirAll output
  freeze directory (output / "Stage2Guest.lean")
  IO.FS.writeBinFile (output / "initStage2Guest.ixe.gz")
    (← IO.FS.readBinFile (directory / "initStage2Guest.ixe.gz"))
  let _ ← run "gzip" #["-dk", (output / "initStage2Guest.ixe.gz").toString]
  let mut rows : Array Lean.Json := #[]
  for (name, manifestName, pieceName) in [
      ("claimBytesWrapper", "manifest", "claimBytesWrapper.ixe"),
      ("initStage2Guest", "guest.manifest", "initStage2Guest.ixe")] do
    let manifest ← IO.FS.readBinFile (directory / manifestName)
    let piece ← IO.FS.readBinFile ((if name == "initStage2Guest" then output else directory) / pieceName)
    let parsed ← checked ((Ixon.Catalog.decodeManifest manifest).mapError reprStr)
    need (parsed.members.size == 1) "Stage2 member count"
    let denial ← match Ixon.Catalog.load manifest #[piece] with
      | .error (.unaddressableConstant _ address (.resource exceeded)) =>
        pure (Lean.Json.mkObj [
          ("stage", Lean.toJson "catalog canonical-address admission"),
          ("address", Lean.toJson address.toHex),
          ("metric", Lean.toJson (reprStr exceeded.metric)),
          ("actual", Lean.toJson exceeded.actual), ("limit", Lean.toJson exceeded.limit)])
      | .error error => throw (IO.userError s!"Stage2 admission frontier changed: {reprStr error}")
      | .ok _ => throw (IO.userError "Stage2 catalog now admitted: review the compilation frontier")
    rows := rows.push (Lean.Json.mkObj [
      ("name", Lean.toJson name), ("piece_bytes", Lean.toJson piece.size),
      ("piece_blake3", Lean.toJson (Ixon.Address.blake3 piece).toHex),
      ("rejection", denial)])
    IO.FS.writeBinFile (output / manifestName) manifest
    IO.FS.writeBinFile (output / pieceName) piece
  let generated ← IO.FS.readBinFile (output / "Stage2Guest.lean")
  let report := Lean.Json.mkObj [
    ("format", Lean.toJson "compilatrix/ixby-stage2-check/1"),
    ("cases", Lean.Json.arr rows),
    ("key_bytes", Lean.toJson (925789 : Nat)), ("runtime_arguments", Lean.toJson (2 : Nat)),
    ("frozen_source_blake3", Lean.toJson (Ixon.Address.blake3 generated).toHex),
    ("guest_image", Lean.Json.null), ("guest_profile", Lean.Json.null),
    ("source_image_reflection", Lean.toJson false), ("flock_compatibility", Lean.toJson false)]
  IO.FS.writeFile (output / "report.json") (report.pretty 100 ++ "\n")
  IO.FS.writeFile (output / "fixture.json") (metadata.pretty 100 ++ "\n")
  IO.println "source-ixby-stage2 ok: 2 source closures, 925789 frozen key bytes, 2 runtime arguments, explicit catalog frontier"
