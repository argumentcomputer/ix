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
    IO.println "CLI: source/import contracts preserved; local escape rejected in every output mode"
  finally
    IO.FS.removeDirAll dir

/-- `ix compile --sharing-limits`: a malformed override is rejected before
    compiling (nothing written), a valid one (Lean and Rust keys mixed)
    compiles, and a limit no constant fits in fails the compile naming the
    limit (so an override that never reached the compiler would be caught).
    An invalid `IX_SHARING_LIMITS` set directly fails the compile once. -/
private def Tests.Cli.testCompileSharingLimits : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  let source := dir / "SharingLimits.lean"
  let output := dir / "sharing-limits.ixe"
  let occurrences (out : IO.Process.Output) (s : String) : Nat :=
    (out.stdout.splitOn s).length - 1 + ((out.stderr.splitOn s).length - 1)
  try
    IO.FS.writeFile source
      "def limitsMarker : Nat := 7\ntheorem limitsProof : limitsMarker = 7 := rfl\n"
    let args := #["compile", source.toString, "--no-build", "--consts", "limitsProof",
      "--out", output.toString]
    let run := fun (spec : String) => IO.Process.output {
      cmd := ix.toString, args := args ++ #["--sharing-limits", spec] }
    let bad ← run "bogus=1"
    if bad.exitCode == 0 || (← output.pathExists) then
      throw <| IO.userError s!"compile accepted --sharing-limits bogus=1:\n{bad.stdout}\n{bad.stderr}"
    unless (bad.stderr.splitOn "unknown sharing limit bogus").length > 1 do
      throw <| IO.userError s!"--sharing-limits bogus=1: unexpected error:\n{bad.stderr}"
    -- Every serialized constant is longer than one byte: the override must
    -- reach the compiler and fail it, naming the limit to raise.
    let tight ← run "output_bytes=1"
    if tight.exitCode == 0 || (← output.pathExists) then
      throw <| IO.userError s!"compile ignored --sharing-limits output_bytes=1:\n\
        {tight.stdout}\n{tight.stderr}"
    unless occurrences tight "--sharing-limits output_bytes=N" > 0 do
      throw <| IO.userError s!"--sharing-limits output_bytes=1: unexpected error:\n\
        {tight.stdout}\n{tight.stderr}"
    -- An invalid override set directly in the environment (no flag, so no
    -- Lean pre-check) fails the compile once, before any block.
    let direct ← IO.Process.output {
      cmd := ix.toString, args, env := #[("IX_SHARING_LIMITS", some "bogus=1")] }
    if direct.exitCode == 0 || (← output.pathExists) then
      throw <| IO.userError s!"compile accepted IX_SHARING_LIMITS=bogus=1:\n\
        {direct.stdout}\n{direct.stderr}"
    unless occurrences direct "IX_SHARING_LIMITS: unknown sharing limit bogus" == 1 do
      throw <| IO.userError s!"IX_SHARING_LIMITS=bogus=1: expected one error:\n\
        {direct.stdout}\n{direct.stderr}"
    let good ← run "states=2^44, depth=2^22, work=max"
    unless good.exitCode == 0 && (← output.pathExists) do
      throw <| IO.userError s!"compile --sharing-limits failed:\n{good.stdout}\n{good.stderr}"
    IO.println "compile --sharing-limits: malformed override rejected, tight limit enforced, \
      invalid IX_SHARING_LIMITS rejected once, valid override compiled"
  finally
    IO.FS.removeDirAll dir

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  Tests.Cli.testCompileContracts
  Tests.Cli.testCompileSharingLimits
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
