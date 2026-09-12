import Compilatrix.IxIR2.WireTests
import Compilatrix.IxIR2.WireIO
import Compilatrix.Tools.Check

open Lean System Compilatrix.Ixon Compilatrix.IxIR2.Wire Compilatrix.Tools.Check

private def rootOfHex (value : String) : Except String Address := do
  let bytes ← unhex value
  if size : bytes.size = 32 then return ⟨bytes, size⟩
  else throw "expected a 32-byte content root"

private def checkFileLimits : IO Nat := do
  IO.FS.withTempDir fun directory => do
    let path := directory / "bounded-input"
    let mut count := 0
    for (limit, size, expected) in [
        (0, 0, true), (0, 1, false), (1, 1, true), (1, 2, false),
        (65535, 65535, true), (65535, 65536, false),
        (65536, 65536, true), (65536, 65537, false)] do
      let bytes := ByteArray.mk (Array.replicate size 0x7a)
      IO.FS.writeBinFile path bytes
      let accepted ← try
          let decoded ← readBounded path limit
          need (decoded == bytes) "bounded file reader changed bytes"
          pure true
        catch _ => pure false
      need (accepted == expected) s!"wrong file read limit: {limit}/{size}"
      count := count + 1
    return count

private def probe (stage : String) (path : FilePath) (root : String)
    (limits : Compilatrix.IxIR.Bounded.Limits) : IO Unit := do
  let bytes ← readBounded path limits.maxBytes
  let root ← checked (rootOfHex root)
  match stage with
  | "syntax" => let _ ← checked (Artifact.decodePreimage limits bytes); pure ()
  | "address" => let _ ← checked (Artifact.decodeAddressed limits bytes root); pure ()
  | "ingress" => let _ ← checked (Artifact.ingest limits {} bytes root); pure ()
  | _ => throw (IO.userError "unknown IxIR2 ingress stage")
  IO.println s!"ixir2 probe ok: {stage}"

private def limitOfString (value : String) : IO Nat :=
  present value.toNat? "expected a natural-number decoder limit"

private def produce (directory : FilePath) : IO Unit := do
  need (!(← directory.pathExists)) "ixir2-fixture requires a new output directory"
  let cases ← checked Examples.cases
  let mutations ← checked Examples.checkIdentityMutations
  checked Examples.checkScalarFactOwners
  let boundaries := Examples.boundaries cases
  let boundaryReports ← boundaries.mapM (fun b => checked b.check)
  let truncations ← checked (Examples.checkTruncations cases)
  let fileLimits ← checkFileLimits
  IO.FS.createDirAll directory
  for artifact in cases do
    IO.FS.writeBinFile (directory / s!"{artifact.name}.ixir2") artifact.bytes
    IO.FS.writeFile (directory / s!"{artifact.name}.json") (artifact.snapshot.pretty 100 ++ "\n")
  for boundary in boundaries do
    IO.FS.writeBinFile (directory / s!"boundary-{boundary.name}.bin") boundary.bytes
  let report := Json.mkObj [("format", toJson formatId), ("cases", toJson (cases.map (·.summary))),
    ("mutations", toJson mutations), ("boundaries", toJson boundaryReports),
    ("proper_prefix_rejections", toJson truncations), ("file_limit_checks", toJson fileLimits)]
  IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
  IO.println s!"ixir2 fixture ok: {cases.size} canonical snapshots, {mutations.size} identity mutations, {boundaries.size} boundaries, {truncations} proper prefixes, {fileLimits} file limits"

def main (args : List String) : IO UInt32 := cli "ixir2 fixture failed" do
  match args with
  | ["--decode", path, root] =>
      probe "address" path root {}
  | ["--ingest", path, root] =>
      probe "ingress" path root {}
  | ["--probe", stage, path, root, maxBytes, maxNatBytes, maxSequence, maxBlobBytes] =>
      probe stage path root {
        maxBytes := ← limitOfString maxBytes
        maxNatBytes := ← limitOfString maxNatBytes
        maxSequence := ← limitOfString maxSequence
        maxBlobBytes := ← limitOfString maxBlobBytes }
  | [directory] => produce directory
  | _ => throw (IO.userError "usage: ixir2-fixture NEW-DIRECTORY | --decode FILE ROOT | --ingest FILE ROOT")
