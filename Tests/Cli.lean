module

public import Ix.Ixon
public import Ix.Cli.CompileCmd

/-!
  Integration tests for the Ix CLI.
-/

/-- Spawn env for nested `lake` invocations: drop the LD_LIBRARY_PATH that
    `lake test` set for this process. It puts the Lean toolchain's lib dir,
    with its bundled libLLVM, ahead of the system libraries, so cargo build
    scripts in a nested build load the system libclang against the wrong
    libLLVM when both share a major version. lake finds its own libraries
    through RUNPATH. -/
private def Tests.Cli.spawnEnv : Array (String × Option String) :=
  #[("LD_LIBRARY_PATH", none)]

def Tests.Cli.run (buildCmd: String) (buildArgs : Array String) (buildDir : Option System.FilePath) : IO Unit := do
  let proc : IO.Process.SpawnArgs :=
    match buildDir with
    | some bd => { cmd := buildCmd, args := buildArgs, cwd := bd, env := Tests.Cli.spawnEnv }
    | none => { cmd := buildCmd, args := buildArgs, env := Tests.Cli.spawnEnv }
  let out ← IO.Process.output proc
  if out.exitCode ≠ 0 then
    IO.eprintln out.stderr
    throw $ IO.userError out.stderr
  else
    IO.println out.stdout

private def Tests.Cli.testCompileNoBuild : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  let source := dir / "NoBuild.lean"
  let output := dir / "no-build.ixe"
  let leanOutput := dir / "no-build-lean.ixe"
  let report := dir / "compile.json"
  try
    -- No Lake project or compiled target exists here. Only the toolchain's
    -- implicit Init imports are available; the CLI must elaborate this body.
    IO.FS.writeFile source
      "def noBuildMarker : Nat := 7\ntheorem noBuildProof : noBuildMarker = 7 := rfl\n"
    let args := #["compile", source.toString, "--consts", "noBuildProof",
      "--out", output.toString, "--report", report.toString]
    let built ← IO.Process.output { cmd := ix.toString, args := args.push "--no-build" }
    unless built.exitCode == 0 do
      throw <| IO.userError s!"compile --no-build failed:\n{built.stdout}\n{built.stderr}"
    unless (← output.pathExists) && !(← IO.FS.readBinFile output).isEmpty do
      throw <| IO.userError "compile --no-build did not write a nonempty .ixe"
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
    let schema ← IO.ofExcept (json.getObjValAs? Nat "schemaVersion")
    let version ← IO.ofExcept (json.getObjValAs? Nat "ixeFormatVersion")
    unless schema == 2 && version == 5 do
      throw <| IO.userError "compile report did not identify its emitted bound v5 envelope under schema2"
    -- Both declarations are in the proof's dependency closure, so the
    -- local selector asks both CLI commands to compile the same input.
    let leanArgs := #["compile-lean", source.toString, "--local",
      "--out", leanOutput.toString]
    let leanBuilt ← IO.Process.output { cmd := ix.toString, args := leanArgs.push "--no-build" }
    unless leanBuilt.exitCode == 0 do
      throw <| IO.userError s!"compile-lean --no-build failed:\n{leanBuilt.stdout}\n{leanBuilt.stderr}"
    unless (← leanOutput.pathExists) && (← IO.FS.readBinFile leanOutput) == (← IO.FS.readBinFile output) do
      throw <| IO.userError "compile-lean --no-build differs from the certified compile output"
    for ext in ["olean", "c"] do
      if ← (source.withExtension ext).pathExists then
        throw <| IO.userError s!"compile --no-build unexpectedly wrote a .{ext} file"
    -- The default path must still require a Lake project/build.
    let defaultRun ← IO.Process.output { cmd := ix.toString, args }
    if defaultRun.exitCode == 0 then
      throw <| IO.userError "compile without --no-build unexpectedly skipped the Lake build"
    let leanDefault ← IO.Process.output { cmd := ix.toString, args := leanArgs }
    if leanDefault.exitCode == 0 then
      throw <| IO.userError "compile-lean without --no-build unexpectedly skipped the Lake build"
    -- Missing imports must fail instead of silently fetching/building them.
    IO.FS.removeFile output
    IO.FS.removeFile leanOutput
    IO.FS.writeFile source "import IxCliNoBuildMissingImport\n"
    let missing ← IO.Process.output { cmd := ix.toString, args := args.push "--no-build" }
    if missing.exitCode == 0 || (← output.pathExists) then
      throw <| IO.userError "compile --no-build accepted a missing import"
    let leanMissing ← IO.Process.output { cmd := ix.toString, args := leanArgs.push "--no-build" }
    if leanMissing.exitCode == 0 || (← leanOutput.pathExists) then
      throw <| IO.userError "compile-lean --no-build accepted a missing import"
    IO.println "compile and compile-lean --no-build: output parity, default builds, and missing-import checks passed"
  finally
    IO.FS.removeDirAll dir

/-- `ix compile` refuses annotated source, in every output mode and for a
contract registered in an imported module, and writes no artifact. -/
private def Tests.Cli.testCompileContracts : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  let source := dir / "Contracts.lean"
  let output := dir / "contracts.ixe"
  try
    IO.FS.writeFile source
      "import Ix.Compile.SourceContract.Elab\n\
       import Tests.Ix.SourceContract.Imported\n\
       def cliLocal (~1 x : Nat) : ~ Nat := x\n\
       def cliEscape (~1 x : Nat) : Nat := x\n"
    let compile := fun name flags => IO.Process.output {
      cmd := ix.toString
      args := #["compile", source.toString, "--no-build", "--consts", name,
        "--out", output.toString] ++ flags }
    for name in ["cliLocal", "cliEscape", "Tests.Ix.SourceContract.Imported.opaqueIdentity"] do
      for flags in [#[], #["--anon"], #["--allow-partial"]] do
        let result ← compile name flags
        if result.exitCode == 0 || (← output.pathExists) then
          throw <| IO.userError s!"CLI emitted an artifact for annotated source: {name} {flags}"
        let said := result.stderr ++ result.stdout
        unless (said.splitOn "annotated source is refused").length > 1 ||
            (said.splitOn "mode checking requires the complete requested closure").length > 1 do
          throw <| IO.userError s!"CLI refused {name} {flags} for another reason:\n{result.stderr}\n{result.stdout}"
    IO.println "CLI: annotated source, local and imported, refused in every output mode"
  finally
    IO.FS.removeDirAll dir

/-- `ix compile --local`: the file's own constants with their selected
    closure. The output's named section holds the file's definition and its
    inductive's recursor (the selected closure carries recursors) but not an
    unrelated import-env constant; `--local` with `--consts` is refused
    (exit 1) and writes nothing. -/
private def Tests.Cli.testCompileLocal : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  let source := dir / "LocalScope.lean"
  let output := dir / "local.ixe"
  try
    IO.FS.writeFile source
      "inductive LocalTree where\n  | leaf\n  | node (l r : LocalTree)\n\
def localSize : LocalTree → Nat\n  | .leaf => 1\n  | .node l r => localSize l + localSize r\n"
    let args := #["compile", source.toString, "--no-build", "--local", "--out", output.toString]
    let run ← IO.Process.output { cmd := ix.toString, args }
    unless run.exitCode == 0 do
      throw <| IO.userError s!"compile --local failed:\n{run.stdout}\n{run.stderr}"
    let env ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile output))
    let has (s : String) : Bool := env.named.toList.any fun (n, _) => n.pretty == s
    for required in ["localSize", "LocalTree", "LocalTree.rec"] do
      unless has required do
        throw <| IO.userError s!"compile --local: the output lacks {required}"
    if has "Nat.gcd" then
      throw <| IO.userError "compile --local: the output holds the unrelated import Nat.gcd"
    IO.FS.removeFile output
    let both ← IO.Process.output
      { cmd := ix.toString, args := args ++ #["--consts", "localSize"] }
    if both.exitCode != 1 || (← output.pathExists) then
      throw <| IO.userError s!"compile --local --consts: expected exit 1 and no output, \
        got exit {both.exitCode}"
    IO.println s!"compile --local: {env.named.size} named entries (own constants, recursor, \
      no unrelated import); --local with --consts refused"
  finally
    IO.FS.removeDirAll dir

/-- Exercise the report-emitting fail-closed path with an actual ungrounded
status. -/
private def Tests.Cli.testCompileReportAbort : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.FS.withTempDir fun dir => do
    let source := dir / "ReportAbort.lean"
    let output := dir / "stale.ixe"
    let report := dir / "report.json"
    -- As in the kernel tutorial fixtures, skip the kernel only to inject
    -- an absent reference. The compiler must report that axiom ungrounded.
    IO.FS.writeFile source <| String.intercalate "\n"
      [ "import Lean", "open Lean Elab Command in", "run_elab do"
      , "  withOptions (fun o => debug.skipKernelTC.set o true) do"
      , "    addDecl (.axiomDecl {"
      , "      name := `reportBad, levelParams := [],"
      , "      type := .const `reportMissing [], isUnsafe := false })", "" ]
    let stale := ByteArray.mk #[0xE5, 0xDE, 0xAD]
    IO.FS.writeBinFile output stale
    IO.FS.writeFile report "stale report"
    let result ← IO.Process.output {
      cmd := ix.toString
      args := #["compile", source.toString, "--no-build", "--consts", "reportBad",
        "--out", output.toString, "--report", report.toString] }
    unless result.exitCode == 1 && (← IO.FS.readBinFile output) == stale do
      throw <| IO.userError s!"report abort changed the artifact or exit code:\n{result.stderr}"
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile report))
    let schema ← IO.ofExcept (json.getObjValAs? Nat "schemaVersion")
    let written ← IO.ofExcept (json.getObjValAs? Bool "written")
    let version ← IO.ofExcept (json.getObjVal? "ixeFormatVersion")
    let ungrounded ← IO.ofExcept (json.getObjValAs? Nat "ungroundedCount")
    unless schema == 2 && !written && version == .null && ungrounded == 1 do
      throw <| IO.userError "report abort did not emit schema2/null for this invocation"
    IO.println "compile report: actual ungrounded abort writes null and preserves stale output"

private def Tests.Cli.testPublishedEnvelopeVersion : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let path := dir / "version.ixe"
    let payload := ByteArray.mk #[1, 2, 3]
    let env : Ixon.Env := { roleBinding := some ⟨Address.admissionHash payload, payload⟩ }
    IO.FS.writeBinFile path (← IO.ofExcept (Ixon.serEnv env))
    unless (← Ix.Cli.publishedEnvelopeVersion true path) == some 5 do
      throw <| IO.userError "published report did not read v5"
    unless (← Ix.Cli.publishedEnvelopeVersion false path).isNone &&
        (← Ix.Cli.publishedEnvelopeVersion false (dir / "absent.ixe")).isNone do
      throw <| IO.userError "aborted report inspected an output path"
    IO.FS.writeBinFile path (← IO.ofExcept (Ixon.serEnv {}))
    unless (← Ix.Cli.publishedEnvelopeVersion true path) == some 4 do
      throw <| IO.userError "published report did not read v4"

/-- `ix compile-export` binds another toolchain's roles where its export puts
them. The 4.35.0 fixture publishes `Int.decLt` at an address the default role
table does not bind it at (its `Decidable` has one constructor); it compiles
to an artifact with its own role binding. -/
private def Tests.Cli.testCompileExportForeignRoles : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.FS.withTempDir fun dir => do
    let export_ := dir / "lean-4.35.0.ndjson"
    let unpacked ← IO.Process.output { cmd := "zstd", args := #["-dc", "-q", "-o",
      export_.toString, "Tests/Fixtures/toolchains/lean-4.35.0.ndjson.zst"] }
    unless unpacked.exitCode == 0 do
      throw <| IO.userError s!"zstd -dc lean-4.35.0.ndjson.zst: {unpacked.stderr}"
    let output := dir / "lean-4.35.0.ixe"
    let compiled ← IO.Process.output {
      cmd := ix.toString
      args := #["compile-export", export_.toString, "--out", output.toString, "--workers", "8"] }
    unless compiled.exitCode == 0 do
      throw <| IO.userError s!"compile-export of the 4.35.0 fixture failed:\n{compiled.stdout}\n{compiled.stderr}"
    let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile output))
    unless env.roleBinding.isSome do
      throw <| IO.userError "compile-export of the 4.35.0 fixture wrote no role binding"
    IO.println "compile-export: the 4.35.0 export compiles with its own role binding"

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  Tests.Cli.testCompileContracts
  Tests.Cli.testCompileLocal
  Tests.Cli.testCompileReportAbort
  Tests.Cli.testPublishedEnvelopeVersion
  Tests.Cli.testCompileExportForeignRoles
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
