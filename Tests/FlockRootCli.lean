import Lean

/- Run after `IX_FLOCK=1 lake build ix`. These checks invoke the linked binary,
so the JSONL contract, feature-enabled FFI, and early file handling are covered.
The current singleton aggregate exercises count-before-compile admission;
the historical fixture remains rejected at the protocol boundary. -/

private def runIx (args : Array String) (trace : Bool := false) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := ".lake/build/bin/ix"
    args := #["flock-root"] ++ args
    env := #[("IX_FLOCK_TIMING", if trace then some "1" else none)] }

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

private def jsonErrors (args : Array String) (fragments : Array String)
    (exact : Bool := false) (trace : Bool := false) : IO Unit := do
  let output ← runIx (args ++ #["--jsonl"]) trace
  require (output.exitCode == 1) s!"expected failure: {output.stdout}\n{output.stderr}"
  let lines := output.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  require (lines.size == fragments.size) s!"stdout is not one record per root: {output.stdout}"
  for (line, fragment) in lines.zip fragments do
    let json ← IO.ofExcept <| Lean.Json.parse line
    require ((← IO.ofExcept <| json.getObjValAs? String "schema") == "ix.flock-stage3.root") line
    require ((← IO.ofExcept <| json.getObjValAs? Nat "version") == 1) line
    require ((← IO.ofExcept <| json.getObjValAs? String "status") == "error") line
    let error ← IO.ofExcept <| json.getObjValAs? String "error"
    require (if exact then error == fragment else (error.splitOn fragment).length > 1)
      s!"expected {fragment}: {error}"
  if trace then
    require ((output.stderr.splitOn "\"schema\":\"ix.flock-stage3.shape-count\"").length > 1)
      "admission failure did not emit its count-only diagnostic on stderr"
    require ((output.stderr.splitOn "\"compiled\":false").length > 1)
      "count-only diagnostic must not claim the relation was compiled"

def main : IO Unit := do
  let temp ← IO.Process.output { cmd := "mktemp", args := #["-d", "/tmp/ix-flock-cli-test.XXXXXX"] }
  require (temp.exitCode == 0) "create CLI test directory"
  let directory : System.FilePath := temp.stdout.trimAscii.toString
  let rootsFile := directory / "roots.txt"
  let occupied := directory / "occupied.flock"
  let abandoned := directory / "abandoned.flock"
  let historical := "Tests/Fixtures/Aggregate/mathlib-2026-09-03/c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f.ixon-proof"
  let protocolError := "expand verified Aiur proof: Verification(\"InvalidProofShape\")"
  let current := "Tests/Fixtures/Aggregate/singleton-2026-09-05/root.ixon-proof"
  let compactDirectory := "Tests/Fixtures/Aggregate/singleton-min-opening-2026-09-05"
  try
    jsonErrors #["invalid-one", "invalid-two"] #["64-char hex", "64-char hex"]
    IO.FS.writeFile rootsFile "# a comment\n\ninvalid-two\ninvalid-three\n"
    jsonErrors #["invalid-one", "--roots-file", rootsFile.toString]
      #["64-char hex", "64-char hex", "64-char hex"]
    jsonErrors #["--root-file", (directory / "missing.ixon").toString] #["no such file"]
    -- Compare the complete backend error across fresh processes. A mismatched
    -- Rust IO.Error constructor tag used to attach a garbage OS error code.
    for _ in [:2] do
      jsonErrors #["--root-file", historical] #[protocolError] (exact := true)
    -- This is a genuine, current-protocol production aggregate, natively
    -- verified in the fixture job. Count its full relation without allocating
    -- its 192 GiB padded witness or compiling its capacity-sized wiring.
    jsonErrors #["--root-file", current]
      #["Stage 3 padded union witness requires 206158430208 bytes; admission limit is 34359738368 (PCS/compiler scratch is additional)"]
      (exact := true) (trace := true)
    jsonErrors #["--root-file", current, "--max-table-capacity", "2097152"]
      #["Stage 3 table capacity 4194304 (nu=22) exceeds admission limit 2097152"]
      (exact := true)
    -- The experiment has a distinct aggregate key. Default production
    -- verification must never infer/adopt that key from fixture metadata.
    jsonErrors #["--root-file", compactDirectory ++ "/root.ixon-proof"]
      #[protocolError] (exact := true)
    let wrongProfile ← IO.Process.output {
      cmd := ".lake/build/bin/bench-flock-root-fixture"
      args := #["--verify", compactDirectory] }
    require (wrongProfile.exitCode == 1 &&
      (wrongProfile.stderr.splitOn "explicitly requested profile").length > 1)
      "experimental fixture verified without its explicit key profile"
    let compactCount ← IO.Process.output {
      cmd := ".lake/build/bin/bench-flock-root-fixture"
      args := #["--min-opening-width", "--count", compactDirectory]
      env := #[("IX_FLOCK_TIMING", some "1")] }
    require (compactCount.exitCode == 0) compactCount.stderr
    let countJson ← IO.ofExcept (Lean.Json.parse compactCount.stdout)
    require ((← IO.ofExcept <| countJson.getObjValAs? String "schema") ==
      "ix.flock-stage3.fixture-count") compactCount.stdout
    require (!(← IO.ofExcept <| countJson.getObjValAs? Bool "compiled")) compactCount.stdout
    require ((← IO.ofExcept <| countJson.getObjValAs? String "admission_error") ==
      "Stage 3 padded union witness requires 206158430208 bytes; admission limit is 1 (PCS/compiler scratch is additional)")
      compactCount.stdout
    require ((compactCount.stderr.splitOn "\"schema\":\"ix.flock-stage3.shape-count\"").length > 1)
      "experimental count did not emit its table census on stderr"

    IO.FS.writeFile occupied "retained artifact"
    jsonErrors #["--root-file", historical, "--mode", "prove", "--output", occupied.toString]
      #["refusing to overwrite"]
    require ((← IO.FS.readFile occupied) == "retained artifact") "existing artifact changed"
    jsonErrors #["--root-file", historical, "--mode", "prove", "--output", abandoned.toString]
      #[protocolError] (exact := true)
    require (!(← abandoned.pathExists)) "failed preflight installed an artifact"
    require ((← directory.readDir).size == 2) "failed preflight left temporary files"

    for args in [#["invalid", "--max-witness-mib", "0"],
        #["invalid", "--max-advice-mib", "18446744073709551615"],
        #["invalid", "--mode", "verify"],
        #["one", "two", "--mode", "prove", "--output", abandoned.toString],
        #["invalid", "--root-file", historical]] do
      let output ← runIx args
      require (output.exitCode == 1 && output.stdout.isEmpty) s!"invalid options started root work: {output.stdout}\n{output.stderr}"
  finally
    for path in [rootsFile, occupied] do
      if ← path.pathExists then IO.FS.removeFile path
    IO.FS.removeDir directory
  IO.println "Flock Stage 3 CLI regressions passed"
