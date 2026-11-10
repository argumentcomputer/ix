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

/-- `ix compile --equations` on a file with a structurally recursive, a
well-founded and a mutual definition, reached from a non-recursive root: the
associations it writes are the same for the anonymous, named and bound
compiles, list each local definition with its `eq_def` and no failure, and
the named artifact resolves every theorem. `--unbound` writes the version-4
envelope without a role binding, whose constants and publications the bound
compile keeps; `--equations-out` without `--equations` is refused. -/
private def Tests.Cli.testCompileEquations : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  IO.FS.withTempDir fun dir => do
    let source := dir / "Equations.lean"
    IO.FS.writeFile source <| String.intercalate "\n"
      [ "def eqLen : List Nat → Nat", "  | [] => 0", "  | _ :: t => eqLen t + 1"
      , "def eqLog (n : Nat) : Nat :=", "  if h : n < 2 then 0 else eqLog (n / 2) + 1"
      , "termination_by n", "decreasing_by omega"
      , "mutual", "def eqEven : Nat → Bool", "  | 0 => true", "  | n + 1 => eqOdd n"
      , "def eqOdd : Nat → Bool", "  | 0 => false", "  | n + 1 => eqEven n", "end"
      , "def eqEntry (l : List Nat) (n : Nat) : Nat := eqLen l + eqLog n + (if eqEven n then 1 else 0)", "" ]
    let compile (out : String) (flags : Array String) : IO (Lean.Json × ByteArray) := do
      let ixe := dir / s!"{out}.ixe"
      let json := dir / s!"{out}.json"
      let result ← IO.Process.output { cmd := ix.toString, args := #["compile", source.toString,
        "--no-build", "--consts", "eqEntry", "--equations", "--out", ixe.toString,
        "--equations-out", json.toString] ++ flags }
      unless result.exitCode == 0 do
        throw <| IO.userError s!"compile --equations {flags} failed:\n{result.stdout}\n{result.stderr}"
      return (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile json)), ← IO.FS.readBinFile ixe)
    let (anonJson, anonBytes) ← compile "anon" #["--anon", "--unbound"]
    let (namedJson, namedBytes) ← compile "named" #["--unbound"]
    let (boundJson, boundBytes) ← compile "bound" #[]
    unless anonJson == namedJson && namedJson == boundJson do
      throw <| IO.userError "compile --equations: the anonymous, named and bound associations differ"
    let rows ← IO.ofExcept (namedJson.getObjValAs? (Array Lean.Json) "equations")
    let pairs := rows.toList.filterMap fun row =>
      match row.getObjValAs? String "definition", row.getObjValAs? String "equation" with
      | .ok d, .ok e => some (d, e)
      | _, _ => none
    let failures ← IO.ofExcept (namedJson.getObjValAs? (Array Lean.Json) "failures")
    for d in ["eqLen", "eqLog", "eqEven", "eqOdd"] do
      unless pairs.contains (d, s!"{d}.eq_def") do
        throw <| IO.userError s!"compile --equations: no association for {d}: {namedJson.compress}"
      let addrArgs := #["addr-of", "--ixe", (dir / "named.ixe").toString, s!"{d}.eq_def"]
      let addr ← IO.Process.output { cmd := ix.toString, args := addrArgs }
      unless addr.exitCode == 0 && addr.stdout.trimAscii.toString.length == 64 do
        throw <| IO.userError s!"addr-of {d}.eq_def in the named artifact: {addr.stdout}{addr.stderr}"
    if pairs.any (·.1 == "eqEntry") || !failures.isEmpty then
      throw <| IO.userError s!"compile --equations: unexpected association or failure: {namedJson.compress}"
    unless anonBytes[0]? == some 0xE4 && namedBytes[0]? == some 0xE4 && boundBytes[0]? == some 0xE5 do
      throw <| IO.userError "compile --unbound: expected the 0xE4 envelope, and 0xE5 without it"
    let anon ← IO.ofExcept (Ixon.deEnv anonBytes)
    let named ← IO.ofExcept (Ixon.deEnv namedBytes)
    let bound ← IO.ofExcept (Ixon.deEnv boundBytes)
    unless anon.roleBinding.isNone && named.roleBinding.isNone && anon.named.isEmpty do
      throw <| IO.userError "compile --unbound: a role binding, or names under --anon"
    unless anon.consts.size == named.consts.size &&
        named.consts.toList.all (fun (a, _) => anon.consts.contains a && bound.consts.contains a) &&
        named.named.toList.all (fun (n, e) => (bound.named.get? n).map (·.addr) == some e.addr) do
      throw <| IO.userError "compile --unbound: the bound compile does not keep the unbound one's constants"
    let refused ← IO.Process.output { cmd := ix.toString, args := #["compile", source.toString,
      "--no-build", "--consts", "eqEntry", "--equations-out", (dir / "alone.json").toString,
      "--out", (dir / "alone.ixe").toString] }
    if refused.exitCode == 0 || (← (dir / "alone.ixe").pathExists) then
      throw <| IO.userError "compile accepted --equations-out without --equations"
    IO.println s!"compile --equations: {pairs.length} associations, the same for the anonymous, \
      named and bound compiles; --unbound: {named.consts.size} of the bound compile's \
      {bound.consts.size} constants, version-4 envelope"

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  Tests.Cli.testCompileContracts
  Tests.Cli.testCompileLocal
  Tests.Cli.testCompileReportAbort
  Tests.Cli.testPublishedEnvelopeVersion
  Tests.Cli.testCompileExportForeignRoles
  Tests.Cli.testCompileEquations
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
