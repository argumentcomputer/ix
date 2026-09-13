import Compilatrix.Tools.Check

open Lean System Compilatrix.Tools.Check

private def inventory (root : FilePath) : IO (List String) := do
  let root ← IO.FS.realPath root
  return ((← files root).map fun path =>
    (path.toString.drop (root.toString.length + 1)).toString).mergeSort (· ≤ ·)

private def same (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second)) s!"Stage2 artifact differs: {first}"

/-- Inspect the complete input of the kernel declaration command separately
from the producer's encoder. No guest execution or source evaluator is used. -/
private def frozen (source directory : FilePath) : IO Unit := do
  let text ← IO.FS.readFile source
  for i in [:256] do
    need (text.contains s!"def b{i} : UInt8 := ⟨⟨⟨{i}, by decide⟩⟩⟩\n") "frozen byte constructor differs"
  for (name, file) in [("frozenIxvmKey", "ixvm.vk"), ("frozenAggregateKey", "aggr.vk")] do
    let declarations := text.splitOn s!"freeze_stage2_data {name} \""
    need (declarations.length == 2) "frozen key command is missing or duplicated"
    let suffix := declarations[1]!
    let encoded := (suffix.splitOn "\"")[0]!
    need ((← checked (unhex encoded)) == (← IO.FS.readBinFile (directory / file)))
      "complete frozen key data differs"
  requireAll text [
    "verifyClaimEntry := Ix.Ixby.Goldilocks.reduce 755",
    "aggregateEntry := Ix.Ixby.Goldilocks.reduce 243",
    "decode := { bytes := 16777216, vector := 1048576, items := 2097152 }",
    "queries := 1024", "foldArity := 256",
    "transcript := { observationBytes := 16777216, sampleAttempts := 64 }",
    "stage2_def initStage2Guest : Bytes → Bytes → Option Bytes",
    "fun publicClaim proofBytes => claimBytesWrapper initBenchmarkSourceConfig publicClaim proofBytes"]
    "fixed Stage2 configuration"

def main (args : List String) : IO UInt32 := cli "Ixby Stage2 check failed" do
  let args ← checked (parseArgs ["--fixture", "--inputs", "--expected"] args)
  let fixture ← present (optional args "--fixture") "--fixture required"
  let inputs : FilePath := option args "--inputs" "fixtures/ixby-stage2"
  let expected ← readJson (option args "--expected" "fixtures/ixby-stage2/expected.json")
  let metadata ← readJson (inputs / "fixture.json")
  for (name, digest) in ← pairs (← field metadata "files_sha256") do
    let actual := (words (← run "sha256sum" #[(inputs / name).toString])).headD ""
    need (actual == (← string digest)) s!"Stage2 input pin differs: {name}"
  IO.FS.withTempDir fun directory => do
    for name in ["first", "second"] do
      let output := directory / name
      requireAll (← run fixture #[inputs.toString, output.toString])
        ["source-ixby-stage2 ok: 2 source closures, 925789 frozen key bytes, 2 runtime arguments, explicit catalog frontier"]
        "Stage2 fixture"
      need ((← readJson (output / "report.json")) == expected) "Stage2 frontier changed"
      frozen (output / "Stage2Guest.lean") inputs
      let sourceHash := (words (← run "sha256sum" #[(output / "Stage2Guest.lean").toString])).headD ""
      need (sourceHash == (← strField (← field metadata "frozen_data") "source_sha256"))
        "frozen source differs from the exported module"
      let packHash := (words (← run "sha256sum" #[(output / "initStage2Guest.ixe").toString])).headD ""
      need (packHash == (← strField (← field metadata "guest_source_pack") "packed_sha256"))
        "decompressed guest differs from original Ixon bytes"
    let first := directory / "first"
    let second := directory / "second"
    let paths ← inventory first
    need (paths == (← inventory second)) "Stage2 artifact inventory differs"
    for path in paths do same (first / path) (second / path)
    let badKeys := directory / "bad-keys"
    IO.FS.createDirAll badKeys
    for name in ["ixvm.vk", "aggr.vk", "Freeze.lean"] do
      IO.FS.writeBinFile (badKeys / name) (← IO.FS.readBinFile (inputs / name))
    for name in ["ixvm.vk", "aggr.vk"] do
      let original ← IO.FS.readBinFile (badKeys / name)
      IO.FS.writeBinFile (badKeys / name) (original.set! 0 (original[0]! ^^^ 1))
      let output := directory / s!"bad-{name}.lean"
      let result ← IO.Process.output { cmd := fixture, args := #["--freeze", badKeys.toString, output.toString] }
      need (result.exitCode == 1 && result.stderr.contains "key differs" && !(← output.pathExists))
        "changed fixed key was accepted"
      IO.FS.writeBinFile (badKeys / name) original
    IO.println "Ixby Stage2 check ok: 2 original closures, complete fixed key data, 2 key mutations, reproducible source, explicit missing image/reflection"
