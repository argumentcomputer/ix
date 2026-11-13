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
    -- `--no-equations`: the parity below is with `compile-lean`, which realizes no equations.
    let args := #["compile", source.toString, "--consts", "noBuildProof", "--no-equations",
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

/-- The kernel's conversion does not compare result contracts, so it accepts
    `rfl` between two arrow types that differ only in one. A `cast` along
    such an equality, from a theorem or from an erased proof argument, must
    not change the contract: `ix compile` refuses both in resource admission.
    A transport between equal types and equation theorems of an annotated
    function are accepted, including one whose proof needs recursor
    reduction (`Nat.add n 0` to `n`), which resource admission does not
    perform: it leaves a proof of an equation between `Nat` values
    uninspected. -/
private def Tests.Cli.testCompileContractTransport : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  let source := dir / "Transport.lean"
  let output := dir / "transport.ixe"
  try
    IO.FS.writeFile source <| "\n".intercalate
      [ "import Ix.Compile.SourceContract.Elab"
      , "def localId (~ x : Nat) : ~ Nat := x"
      , "def T1 : Type := (~ x : Nat) → ~ Nat"
      , "def T2 : Type := (~ x : Nat) → Nat"
      , "theorem launder : ((~ x : Nat) → ~ Nat) = ((~ x : Nat) → Nat) := rfl"
      , "def esc (~ x : Nat) : Nat := cast launder localId x"
      , "theorem viaZero : ∀ (A B : Type) (0 h : A = B), A = B := fun _ _ h => h"
      , "def escZero (~ x : Nat) : Nat :="
      , "  (cast (viaZero T1 T2 (Eq.trans (rfl : T1 = T1) (rfl : T1 = T2))) localId : T2) x"
      , "theorem same : T1 = T1 := rfl"
      , "def keepLocal (~ x : Nat) : ~ Nat := (cast same localId : T1) x"
      , "theorem localId_eq (x : Nat) : localId x = x := rfl"
      , "theorem localId_add_zero (n : Nat) : localId (Nat.add n 0) = n := rfl"
      , "" ]
    let compile := fun (names : String) => IO.Process.output {
      cmd := ix.toString
      args := #["compile", source.toString, "--no-build", "--consts", names,
        "--out", output.toString] }
    for name in ["esc", "escZero"] do
      let result ← compile name
      if result.exitCode == 0 || (← output.pathExists) then
        throw <| IO.userError s!"CLI emitted an artifact for {name}, which changes a result contract"
      unless ((result.stderr ++ result.stdout).splitOn "resource admission").length > 1 do
        throw <| IO.userError s!"{name} was not refused by resource admission:\n\
          {result.stderr}\n{result.stdout}"
    let accepted ← compile "keepLocal,localId_eq,localId_add_zero"
    unless accepted.exitCode == 0 && (← output.pathExists) do
      throw <| IO.userError s!"CLI refused a transport between equal types or an equation \
        theorem:\n{accepted.stderr}\n{accepted.stdout}"
    IO.println "CLI: transports that change a result contract refused; a transport between \
      equal types and equation theorems accepted"
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

/-- `ix compile`'s equations on a file with a structurally recursive, a
well-founded and a mutual definition, reached from a non-recursive root: the
associations it writes are the same for the anonymous and named compiles,
list each local definition with its `eq_def` and no failure, and the named
artifact resolves every theorem. They are the default for a selected closure:
without `--equations` the compile writes the same associations and, since
`eqLog`'s `omega` termination proof is a theorem, no word equation (the
`theorems` list is empty); `--no-word-equations` keeps the associations;
`--no-equations` writes none and refuses `--equations-out`; each flag and its
`--no-` form together, and `--word-equations` with `--no-equations`, are
refused. -/
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
    let run (out : String) (flags : Array String) : IO IO.Process.Output :=
      IO.Process.output { cmd := ix.toString, args := #["compile", source.toString,
        "--no-build", "--consts", "eqEntry", "--out", (dir / s!"{out}.ixe").toString] ++ flags }
    let compile (out : String) (flags : Array String) : IO (Lean.Json × ByteArray) := do
      let json := dir / s!"{out}.json"
      let result ← run out (#["--equations-out", json.toString] ++ flags)
      unless result.exitCode == 0 do
        throw <| IO.userError s!"compile {flags} failed:\n{result.stdout}\n{result.stderr}"
      return (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile json)),
        ← IO.FS.readBinFile (dir / s!"{out}.ixe"))
    let (anonJson, anonBytes) ← compile "anon" #["--equations", "--anon"]
    let (namedJson, _) ← compile "named" #["--equations"]
    unless anonJson == namedJson do
      throw <| IO.userError "compile --equations: the anonymous and named associations differ"
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
    let anon ← IO.ofExcept (Ixon.deEnv anonBytes)
    unless anon.named.isEmpty do
      throw <| IO.userError "compile --equations --anon: names in the anonymous artifact"
    -- The default for a selected closure: the same associations, no word equation (the omega
    -- proof that reaches word operations is a theorem).
    let (defaultJson, defaultBytes) ← compile "default" #[]
    let (explicitJson, explicitBytes) ← compile "explicit" #["--equations", "--word-equations"]
    unless defaultJson == namedJson && explicitJson == namedJson && defaultBytes == explicitBytes do
      throw <| IO.userError s!"compile without flags differs from --equations: {defaultJson.compress}"
    unless (defaultJson.getObjValAs? (Array Lean.Json) "theorems").toOption.map (·.size) == some 0 do
      throw <| IO.userError s!"compile: a word equation for an omega proof: {defaultJson.compress}"
    let (noWordsJson, _) ← compile "no-words" #["--no-word-equations"]
    unless noWordsJson == namedJson do
      throw <| IO.userError s!"compile --no-word-equations changed the associations: {noWordsJson.compress}"
    let off ← run "off" #["--no-equations"]
    if off.exitCode != 0 || (← (dir / "off.ixe.equations.json").pathExists) then
      throw <| IO.userError s!"compile --no-equations: exit {off.exitCode} or an equations file written"
    for (flags, what) in [(#["--no-equations", "--equations-out", (dir / "x.json").toString],
          "--equations-out with --no-equations"),
        (#["--equations", "--no-equations"], "--equations with --no-equations"),
        (#["--word-equations", "--no-word-equations"], "--word-equations with --no-word-equations"),
        (#["--word-equations", "--no-equations"], "--word-equations with --no-equations")] do
      let refused ← run "refused" flags
      if refused.exitCode == 0 || (← (dir / "refused.ixe").pathExists) then
        throw <| IO.userError s!"compile accepted {what}"
    IO.println s!"compile: {pairs.length} associations by default and with --equations, the same \
      for the anonymous and named compiles; no word equation for an omega proof; the --no- forms \
      turn them off; contradictory flags refused"

/-- `kernel-check-ixe` ends when its check raises after the watchdog started. It used to hang
there, with no CPU and nothing printed: the watchdog, a dedicated task, ran until a flag that
only the normal path cleared, and the runtime waits for its tasks before it reports an
uncaught error. Two such errors, each under a 60 s bound: a record nested 20,000 levels, which
the artifact's admission declines by the depth limit (`Binding.context`, `.limit .depth`), and
an artifact cut in half, which the loader refuses. -/
private def Tests.Cli.testCheckIxeExits : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let kci ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
  let dir ← IO.FS.createTempDir
  try
    -- a theorem whose proof is `@id True (@id True (… True.intro))`, built by a loop and added
    -- without Lean's kernel check, so nothing on Lean's side recurses on its depth
    let source := dir / "KjDeep.lean"
    IO.FS.writeFile source
      "import Lean\nopen Lean\n\
       def kjNest (n : Nat) : Expr := Id.run do\n\
       \x20 let mut e : Expr := .const ``True.intro []\n\
       \x20 for _ in [0:n] do\n\
       \x20   e := mkApp2 (.const ``id [Level.zero]) (.const ``True []) e\n\
       \x20 return e\n\
       set_option debug.skipKernelTC true\n\
       run_cmd Lean.Elab.Command.liftCoreM do\n\
       \x20 addDecl (.thmDecl { name := `kjDeep, levelParams := [], type := .const ``True [], value := kjNest 20000 })\n"
    let deep := dir / "deep.ixe"
    let built ← IO.Process.output {
      cmd := ix.toString, env := Tests.Cli.spawnEnv
      args := #["compile", source.toString, "--no-build", "--consts", "kjDeep", "--out", deep.toString] }
    unless built.exitCode == 0 do
      throw <| IO.userError s!"compile of the 20,000-level record failed:\n{built.stdout}\n{built.stderr}"
    let truncated := dir / "truncated.ixe"
    let bytes ← IO.FS.readBinFile deep
    IO.FS.writeBinFile truncated (bytes.extract 0 (bytes.size / 2))
    for (label, input, needle) in [("deep", deep, "Resource.depth"), ("truncated", truncated, "")] do
      let out ← IO.Process.output {
        cmd := "timeout", env := Tests.Cli.spawnEnv
        args := #["--kill-after=5", "60", kci.toString, input.toString, (dir / s!"{label}.jsonl").toString] }
      if out.exitCode == 124 || out.exitCode == 137 then
        throw <| IO.userError s!"kernel-check-ixe on the {label} artifact ran past 60 s"
      unless out.exitCode == 1 && (needle.isEmpty || (out.stderr.splitOn needle).length > 1) do
        throw <| IO.userError s!"kernel-check-ixe on the {label} artifact: exit {out.exitCode}, \
expected 1 with '{needle}'\n{out.stdout}\n{out.stderr}"
  finally
    IO.FS.removeDirAll dir

public def Tests.Cli.suite : IO UInt32 := do
  Tests.Cli.run "lake" (#["exe", "ix", "--help"]) none
  Tests.Cli.testCompileNoBuild
  Tests.Cli.testCompileContracts
  Tests.Cli.testCompileContractTransport
  Tests.Cli.testCompileLocal
  Tests.Cli.testCompileReportAbort
  Tests.Cli.testPublishedEnvelopeVersion
  Tests.Cli.testCompileExportForeignRoles
  Tests.Cli.testCompileEquations
  Tests.Cli.testCheckIxeExits
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
