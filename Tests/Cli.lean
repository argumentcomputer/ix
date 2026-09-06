module

/- Integration tests for the Ix CLI -/

def Tests.Cli.run (buildCmd: String) (buildArgs : Array String) (buildDir : Option System.FilePath) : IO Unit := do
  let proc : IO.Process.SpawnArgs :=
    match buildDir with
    | some bd => { cmd := buildCmd, args := buildArgs, cwd := bd }
    | none => { cmd := buildCmd, args := buildArgs }
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
  try
    -- No Lake project or compiled target exists here. Only the toolchain's
    -- implicit Init imports are available; the CLI must elaborate this body.
    IO.FS.writeFile source
      "def noBuildMarker : Nat := 7\ntheorem noBuildProof : noBuildMarker = 7 := rfl\n"
    let args := #["compile", source.toString, "--consts", "noBuildProof",
      "--out", output.toString]
    let built ← IO.Process.output { cmd := ix.toString, args := args.push "--no-build" }
    unless built.exitCode == 0 do
      throw <| IO.userError s!"compile --no-build failed:\n{built.stdout}\n{built.stderr}"
    unless (← output.pathExists) && !(← IO.FS.readBinFile output).isEmpty do
      throw <| IO.userError "compile --no-build did not write a nonempty .ixe"
    for ext in ["olean", "c"] do
      if ← (source.withExtension ext).pathExists then
        throw <| IO.userError s!"compile --no-build unexpectedly wrote a .{ext} file"
    -- The default path must still require a Lake project/build.
    let defaultRun ← IO.Process.output { cmd := ix.toString, args }
    if defaultRun.exitCode == 0 then
      throw <| IO.userError "compile without --no-build unexpectedly skipped the Lake build"
    -- Missing imports must fail instead of silently fetching/building them.
    IO.FS.removeFile output
    IO.FS.writeFile source "import IxCliNoBuildMissingImport\n"
    let missing ← IO.Process.output { cmd := ix.toString, args := args.push "--no-build" }
    if missing.exitCode == 0 || (← output.pathExists) then
      throw <| IO.userError "compile --no-build accepted a missing import"
    IO.println "compile --no-build: source elaboration, output, default build, and missing-import checks passed"
  finally
    IO.FS.removeDirAll dir

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
