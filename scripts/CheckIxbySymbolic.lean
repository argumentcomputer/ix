import Compilatrix.Tools.Check

/-! An independent process gate imports only host checking utilities. Each
guest is certified before its input loop; original canonical executions then
reuse that one certificate for all the admitted argument arrays. -/

open Lean System Compilatrix.Tools.Check

private def inventory (root : FilePath) : IO (List String) := do
  let root ← IO.FS.realPath root
  return ((← files root).map fun path =>
    (path.toString.drop (root.toString.length + 1)).toString).mergeSort (· ≤ ·)

private def same (first second : FilePath) : IO Unit := do
  need ((← IO.FS.readBinFile first) == (← IO.FS.readBinFile second)) s!"symbolic artifact drift: {first}"

private def runImage (runner : String) (program input output : FilePath) : IO Unit := do
  let _ ← run runner #[(program / "profile.ixbp").toString, (program / "program.ixby").toString,
    (input / "input.ixbi").toString, output.toString, "100000"]
  same (input / "output.ixbo") output

private def corrupt (runner : String) (program input output file : FilePath)
    (change : ByteArray → ByteArray) : IO Unit := do
  let original ← IO.FS.readBinFile file
  try
    IO.FS.writeBinFile file (change original)
    let result ← IO.Process.output { cmd := runner, args := #[
      (program / "profile.ixbp").toString, (program / "program.ixby").toString,
      (input / "input.ixbi").toString, output.toString, "100000"] }
    need (result.exitCode == 1 && result.stderr.contains "ixby-run:" && !(← output.pathExists))
      s!"symbolic corrupt artifact accepted: {file}"
  finally IO.FS.writeBinFile file original

def main (args : List String) : IO UInt32 := cli "Ixby symbolic check failed" do
  let args ← checked (parseArgs ["--fixture", "--runner", "--compiler", "--expected", "--upstream"] args)
  let fixture ← present (optional args "--fixture") "--fixture required"
  let runner ← present (optional args "--runner") "--runner required"
  let compiler ← present (optional args "--compiler") "--compiler required"
  let upstream : FilePath := option args "--upstream" "fixtures/ixon-upstream"
  let expected ← readJson (option args "--expected" "fixtures/ixby-symbolic/expected.json")
  need ((← strField expected "format") == "compilatrix/ixby-symbolic-check/1") "symbolic report version"
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture #[output.toString, upstream.toString])
        ["source-ixby-symbolic ok: 44 cases, 576 reference runs, 203 canonical runs, 30 rejections"]
        "symbolic source matrix"
      need ((← readJson (output / "report.json")) == expected) "reviewed symbolic report drifted"
    let paths ← inventory first
    need (paths == (← inventory second)) "symbolic artifact inventory differs across processes"
    for path in paths do same (first / path) (second / path)
    let mut count := 0
    for row in ← arrField expected "cases" do
      if (← field row "wire") != Json.null then
        let name ← strField row "name"
        let program := first / name / "wire"
        let runs ← checked (← readJson (program / "runs.json")).getArr?
        for index in [:runs.size] do
          runImage runner program (program / toString index) (directory / s!"{name}-{index}.ixbo")
          count := count + 1
    need (count == 203) "canonical reuse run count differs"
    let program := first / "identity" / "wire"
    let input := program / "0"
    let mut mutations := 0
    for (file, change) in [
        (program / "program.ixby", fun bytes : ByteArray => bytes.push 0),
        (program / "program.ixby", fun bytes : ByteArray => bytes.extract 0 (bytes.size - 1)),
        (program / "program.ixby", fun bytes : ByteArray => bytes.set! 4 1),
        (program / "program.ixby", fun bytes : ByteArray => bytes.set! 8 255),
        (input / "input.ixbi", fun bytes : ByteArray => bytes.push 0),
        (input / "input.ixbi", fun bytes : ByteArray => bytes.extract 0 (bytes.size - 1)),
        (program / "profile.ixbp", fun bytes : ByteArray => bytes.set! 40 1)] do
      corrupt runner program input (directory / s!"bad-{mutations}.ixbo") file change
      mutations := mutations + 1
    for (name, root) in [
        ("applyClosed", "b81b754f02c1b63279a609ab4b55b609fd6f87fab7b14879f4021c3327c2eb40"),
        ("captureClosed", "5628cfe1b4f959fb116661fc50ae8e9e4bfa470ac5d0e639a75b9d23aed12953"),
        ("letClosed", "6c737171f1a3c482ba96cbe4998ea660fda824c578fe668ab9fdc4aae1b9754f")] do
      let catalog := directory / s!"{name}.ixc"
      IO.FS.createDirAll catalog
      IO.FS.writeBinFile (catalog / "manifest") (← checked (unhex (← IO.FS.readFile (upstream / s!"{name}.manifest.hex"))))
      IO.FS.writeBinFile (catalog / s!"CompilatrixUpstream.{name}.ixe")
        (← checked (unhex (← IO.FS.readFile (upstream / s!"{name}.ixe.hex"))))
      let output := directory / s!"compiled-{name}"
      let _ ← run compiler #[catalog.toString, root, output.toString, "proving", "--symbolic"]
      for file in ["program.ixby", "profile.ixbp", "source.json", "program.txt", "config.txt", "symbolic.json"] do
        same (first / s!"upstream-{name}" / "wire" / file) (output / file)
    IO.println s!"Ixby symbolic check ok: 44 certificates, 576 reference runs, {count} canonical runs, 30 rejections, {mutations} byte mutations, 3 catalog certifications"
