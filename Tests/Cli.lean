module

public import Ix.Ixon

/- Integration tests for the Ix CLI -/

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
    for flags in [#[], #["--anon"]] do
      let result ← compile "cliLocal" flags
      unless result.exitCode == 0 do
        throw <| IO.userError s!"annotated CLI compile failed: {result.stderr}\n{result.stdout}"
      let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv (← IO.FS.readBinFile output))
      let preserved := env.consts.toList.any fun (addr, _) =>
        match env.getConst? addr with
        | some { info := .defn d, .. } =>
          match d.typ, d.value with
          | .all input result _ _, .lam bodyInput _ _ =>
            input == ⟨.linear, .localShared⟩ && result == .localShared && bodyInput == input
          | _, _ => false
        | _ => false
      unless preserved do
        throw <| IO.userError "CLI output lost its linear/local contract"
      IO.FS.removeFile output
    -- The registry is loaded from an imported .olean in this fresh process.
    let imported ← compile "Tests.Ix.SourceContract.Imported.opaqueIdentity" #[]
    unless imported.exitCode == 0 do
      throw <| IO.userError s!"imported contract CLI compile failed: {imported.stderr}"
    let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv (← IO.FS.readBinFile output))
    unless env.consts.toList.any (fun (addr, _) =>
        match env.getConst? addr with
        | some { info := .defn d, .. } =>
          match d.typ, d.value with
          | .all input _ _ _, .lam bodyInput _ _ =>
            d.kind == .opaq && input.uses == .linear && bodyInput == input
          | _, _ => false
        | _ => false) do
      throw <| IO.userError "CLI output lost its imported opaque contract"
    IO.FS.removeFile output
    for flags in [#[], #["--anon"], #["--allow-partial"]] do
      let result ← compile "cliEscape" flags
      if result.exitCode == 0 || (← output.pathExists) then
        throw <| IO.userError "CLI emitted an artifact for an escaping local input"
    IO.println "v3 CLI: source/import contracts preserved; local escape rejected in every output mode"
  finally
    IO.FS.removeDirAll dir

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  Tests.Cli.testCompileContracts
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
