import Ix.Compiler.Coverage.Report
import Ix.Compiler.Coverage.UpstreamNative

/-! Emit a deterministic coverage report and complete compiler snapshots.
The independent Lean gate runs this executable in two fresh directories. -/

open Ix.Compiler Ix.Compiler.Coverage

private def usage : String :=
  "usage: lake exe compiler-source-coverage <new-output-directory> [ixon-std-contact-directory [ixon-upstream-directory]]"

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def writeJson (path : System.FilePath) (value : Lean.Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty 100 ++ "\n")

def main (args : List String) : IO UInt32 := do
  let some (output, contact, upstream) := (match args with
      | [output] => some (output, CatalogContactFixture.directory, Upstream.directory)
      | [output, contact] => some (output, contact, Upstream.directory)
      | [output, contact, upstream] => some (output, contact, upstream)
      | _ => none)
    | IO.eprintln usage
      return 2
  try
    let output : System.FilePath := output
    if ← output.pathExists then
      throw (IO.userError "source-coverage requires a new output directory")
    -- Finish every gate before publishing any snapshot or report.
    let sources ← checked Coverage.sources
    let synthetic ← checked (sources.mapM fun source =>
      (runSource source).mapError (fun error => s!"{source.name}: {error}"))
    let loaded ← checked (← CatalogContactFixture.load contact)
    let production ← checked (productionCases loaded)
    let upstream ← checked (← UpstreamNative.cases upstream)
    let corpus ← checked generatedCorpus
    let results := synthetic ++ production ++ upstream
    IO.FS.createDirAll output
    for result in results do
      writeJson (output / s!"{result.name}.json") result.snapshot
      if let some object := result.object then
        IO.FS.writeBinFile (output / s!"{result.name}.o") object
    writeJson (output / "report.json") (report results corpus)
    IO.println s!"source-coverage ok: {results.length} Ixon cases, {results.countP (·.object.isSome)} ELF objects, {IxIR1.WellModedGen.defaultCases} generated IxIR0 cases"
    return 0
  catch error =>
    IO.eprintln s!"source-coverage: {error}"
    return 1
