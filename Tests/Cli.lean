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
    -- the depth decline exits 6 (`Ix.Kernel.Host.exitDeclined`) naming the setting; the loader's refusal 1
    for (label, input, code, needle) in [("deep", deep, 6, "declined by the depth limit (16384, default)"),
        ("truncated", truncated, 1, "")] do
      let out ← IO.Process.output {
        cmd := "timeout", env := Tests.Cli.spawnEnv
        args := #["--kill-after=5", "60", kci.toString, input.toString, (dir / s!"{label}.jsonl").toString] }
      if out.exitCode == 124 || out.exitCode == 137 then
        throw <| IO.userError s!"kernel-check-ixe on the {label} artifact ran past 60 s"
      unless out.exitCode == code && (needle.isEmpty || (out.stderr.splitOn needle).length > 1) do
        throw <| IO.userError s!"kernel-check-ixe on the {label} artifact: exit {out.exitCode}, \
expected {code} with '{needle}'\n{out.stdout}\n{out.stderr}"
  finally
    IO.FS.removeDirAll dir

/-- Run `cmd args` with `env` added; exit code, stdout, stderr. -/
private def Tests.Cli.runEnv (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, env := Tests.Cli.spawnEnv ++ env }

private def Tests.Cli.expect (what : String) (out : IO.Process.Output) (code : UInt32)
    (needles : List String := []) : IO Unit := do
  unless out.exitCode == code do
    throw <| IO.userError s!"{what}: exit {out.exitCode}, expected {code}\n{out.stdout}\n{out.stderr}"
  for n in needles do
    unless (out.stderr.splitOn n).length > 1 || (out.stdout.splitOn n).length > 1 do
      throw <| IO.userError s!"{what}: no '{n}' in its output\n{out.stdout}\n{out.stderr}"

/-- Compile, into `dir`, an artifact whose one theorem `kjDeep`'s proof is
`@id True (… True.intro)` nested `n` levels (built by a loop, added without Lean's kernel
check). The producer runs on a 4 GiB stack: it recurses on the depth and is not under test. -/
private def Tests.Cli.compileDeep (ix dir : System.FilePath) (n : Nat) : IO System.FilePath := do
  let source := dir / s!"KjDeep{n}.lean"
  IO.FS.writeFile source
    s!"import Lean\nopen Lean\n\
     def kjNest (n : Nat) : Expr := Id.run do\n\
     \x20 let mut e : Expr := .const ``True.intro []\n\
     \x20 for _ in [0:n] do\n\
     \x20   e := mkApp2 (.const ``id [Level.zero]) (.const ``True []) e\n\
     \x20 return e\n\
     set_option debug.skipKernelTC true\n\
     run_cmd Lean.Elab.Command.liftCoreM do\n\
     \x20 addDecl (.thmDecl \{ name := `kjDeep, levelParams := [], type := .const ``True [], value := kjNest {n} })\n"
  let out := dir / s!"deep{n}.ixe"
  let built ← IO.Process.output {
    cmd := ix.toString, env := Tests.Cli.spawnEnv ++ #[("LEAN_STACK_SIZE_KB", some "4194304")]
    args := #["compile", source.toString, "--no-build", "--consts", "kjDeep", "--out", out.toString] }
  unless built.exitCode == 0 do
    throw <| IO.userError s!"compile of the {n}-level record failed:\n{built.stdout}\n{built.stderr}"
  return out

/-- **A deep record is declined, not a crash** (the root loaders scan a record's depth before
they decode it: `Ix/Ixon.lean`'s `getEnv`/`getEnvVerifiedLazy`, the stream's `decodeOwn`). A
record nested 20,000 levels, past the default depth limit (16,384): `ix check-lean`, `ix
verify-host` (a statement issued for a 10-level artifact, replayed against the deep one; the
loader runs first) and `kernel-check-ixe` exit 6 naming the limit. A record nested 100,000
levels on an 8 MiB stack (`LEAN_STACK_SIZE_KB=8192`), on which `check-lean` used to abort
with a stack overflow while it decoded: every host exits 6 (`kernel-check-ixe` keeps its
caller's stack). Each run under a 120 s bound. -/
private def Tests.Cli.testDeepRecordExits : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let kci ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
  let dir ← IO.FS.createTempDir
  try
    let shallow ← Tests.Cli.compileDeep ix dir 10
    let deep ← Tests.Cli.compileDeep ix dir 20000
    let deeper ← Tests.Cli.compileDeep ix dir 100000
    let stmt := dir / "deep10.stmt"
    let issued ← Tests.Cli.runEnv ix.toString #["check-lean", shallow.toString, "--host-out", stmt.toString]
    Tests.Cli.expect "check-lean on the 10-level artifact" issued 0
    let some line := issued.stdout.splitOn "\n" |>.find? (·.startsWith "[check-lean] host admission statement: ")
      | throw <| IO.userError s!"no host statement line\n{issued.stdout}"
    let address := (line.drop "[check-lean] host admission statement: ".length).toString.trimAscii.toString
    let bounded := fun (cmd : System.FilePath) (args : Array String) => #["--kill-after=5", "120", cmd.toString] ++ args
    let declined := "declined by the depth limit (16384, default)"
    for (input, label, vars) in [(deep, "20,000 levels, defaults",
          (#[("LEAN_STACK_SIZE_KB", none)] : Array (String × Option String))),
        (deeper, "100,000 levels, 8 MiB stack", #[("LEAN_STACK_SIZE_KB", some "8192")])] do
      for (host, args) in [("check-lean", bounded ix #["check-lean", input.toString]),
          ("verify-host", bounded ix #["verify-host", address, input.toString, "--statement-file", stmt.toString]),
          ("kernel-check-ixe", bounded kci #[input.toString, (dir / "rows.jsonl").toString])] do
        let out ← Tests.Cli.runEnv "timeout" args vars
        if out.exitCode == 124 || out.exitCode == 137 then
          throw <| IO.userError s!"{host} on the record of {label} ran past 120 s"
        Tests.Cli.expect s!"{host} on the record of {label}" out 6 [declined]
    IO.println "deep records: 20,000 levels at the defaults and 100,000 on an 8 MiB stack \
      declined (exit 6) by check-lean, verify-host and kernel-check-ixe"
  finally
    IO.FS.removeDirAll dir

/-! ## The kernel's limits as settings (`IxCK/Host/Limits.lean`, `docs/kernel.md`, "Limits at
the command line, and exit codes"): each limit lowered and raised by its flag and by its
variable, the flag over the variable, malformed values, the address-space refusal, on
`ix check-lean`, `ix verify-host`, `ix compile` and `kernel-check-ixe`. -/

private def Tests.Cli.testKernelLimits : IO Unit := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let kci ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
  let dir ← IO.FS.createTempDir
  let source := dir / "Limits.lean"
  let art := dir / "limits.ixe"
  try
    IO.FS.writeFile source
      "def kjText : String := \"kernel limits\"\ndef kjNum : Nat := 123456789\n\
       theorem kjProof : kjNum = 123456789 := rfl\n"
    let built ← Tests.Cli.runEnv ix.toString #["compile", source.toString, "--no-build",
      "--consts", "kjText,kjProof", "--out", art.toString]
    Tests.Cli.expect "compile the limits artifact" built 0
    let env ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv (← IO.FS.readBinFile art))
    let sizes := env.consts.toList.map fun (_, c) => c.len
    let total := sizes.foldl (· + ·) 0 + env.blobs.fold (fun n _ b => n + b.size) 0
    let largest := sizes.foldl max 0
    let checkLean := fun (flags : Array String) (vars : Array (String × Option String)) =>
      Tests.Cli.runEnv ix.toString (#["check-lean", art.toString] ++ flags) vars
    Tests.Cli.expect "check-lean at the defaults" (← checkLean #[] #[]) 0
    -- each limit below what the artifact needs: a decline, exit 6, naming its source
    let mut lowered : List (String × String × String × Nat) := [
      ("max-records", "IX_KERNEL_MAX_RECORDS", "record count", env.consts.size - 1),
      ("max-total-bytes", "IX_KERNEL_MAX_TOTAL_BYTES", "total bytes", total - 1),
      ("max-record-bytes", "IX_KERNEL_MAX_RECORD_BYTES", "record bytes", largest - 1),
      ("max-record-univ-nodes", "IX_KERNEL_MAX_RECORD_UNIV_NODES", "universe nodes per record", 1),
      ("max-depth", "IX_KERNEL_MAX_DEPTH", "depth", 2)]
    if env.blobs.size > 1 then
      lowered := ("max-blobs", "IX_KERNEL_MAX_BLOBS", "blob count", env.blobs.size - 1) :: lowered
    for (flag, var, word, n) in lowered do
      Tests.Cli.expect s!"--{flag} {n}" (← checkLean #[s!"--{flag}", toString n] #[]) 6
        [s!"declined by the {word} limit ({n}, --{flag}); raise it with --{flag} N or {var}=N"]
      Tests.Cli.expect s!"{var}={n}" (← checkLean #[] #[(var, some (toString n))]) 6
        [s!"declined by the {word} limit ({n}, {var})"]
      -- raised past the default, by the flag and by the variable: accepted, the source printed
      -- (the depth limit sizes the threads' stacks, 16 KiB a level: raised to 100,000, not 2^40)
      let up := if flag == "max-depth" then "100000" else "1099511627776"
      Tests.Cli.expect s!"--{flag} raised" (← checkLean #[s!"--{flag}", up] #[]) 0
        [s!"{flag} {up} (--{flag})"]
      Tests.Cli.expect s!"{var} raised" (← checkLean #[] #[(var, some up)]) 0
        [s!"{flag} {up} ({var})"]
    -- the flag wins over the variable
    Tests.Cli.expect "flag over variable" (← checkLean #["--max-depth", "2"]
      #[("IX_KERNEL_MAX_DEPTH", some "100000")]) 6 ["(2, --max-depth)"]
    for w in ["1", "3"] do
      Tests.Cli.expect s!"--workers {w}" (← checkLean #["--workers", w] #[]) 0 [s!"workers {w} (--workers)"]
      Tests.Cli.expect s!"IX_KERNEL_WORKERS={w}" (← checkLean #[] #[("IX_KERNEL_WORKERS", some w)]) 0
        [s!"workers {w} (IX_KERNEL_WORKERS)"]
    -- malformed values: usage errors naming the flag or the variable
    for (flags, vars, needle) in [(#["--max-depth", "abc"], #[], "--max-depth takes a positive whole number"),
        (#["--max-depth", "0"], #[], "--max-depth takes a positive whole number"),
        (#["--workers", "0"], #[], "--workers takes a positive whole number"),
        (#[], #[("IX_KERNEL_MAX_DEPTH", some "-1")], "IX_KERNEL_MAX_DEPTH takes a positive whole number"),
        (#[], #[("IX_KERNEL_WORKERS", some "x")], "IX_KERNEL_WORKERS takes a positive whole number")] do
      Tests.Cli.expect s!"malformed {flags} {vars.map (·.1)}" (← checkLean flags vars) 2 [needle]
    -- the address-space check (`Ix.Kernel.Host.spaceCheck`), each run under `ulimit -v` and a
    -- 120 s bound: exit 2 only when the run certainly cannot fit; a warning line when the
    -- estimate (twice the runtime's pool plus 8 threads) does not fit, and the run goes on
    let capped := fun (cap : Nat) (vars cmd : String) => do
      let out ← Tests.Cli.runEnv "bash" #["-c",
        s!"ulimit -v {cap * 1024 * 1024}; exec env {vars} timeout --kill-after=5 120 {cmd}"]
      if out.exitCode == 124 || out.exitCode == 137 then
        throw <| IO.userError s!"under a {cap} GiB cap, '{cmd}' ran past 120 s"
      pure out
    let warning := "may fail to create a thread under the address-space limit"
    -- one stack (16 KiB a level: 15.3 GiB at a depth of 1,000,000) over an 8 GiB cap
    Tests.Cli.expect "one stack over the cap" (← capped 8 "-u LEAN_STACK_SIZE_KB"
      s!"{ix} check-lean {art} --max-depth 1000000") 2 ["one thread stack", "--max-depth"]
    -- 64 workers' 256 MiB stacks over an 8 GiB cap
    Tests.Cli.expect "64 workers over the cap" (← capped 8 "-u LEAN_STACK_SIZE_KB"
      s!"{ix} check-lean {art} --workers 64") 2 ["64 worker threads", "--workers"]
    -- the estimate over the cap (a pool of 64: 136 threads of 320 MiB), the run within it
    let warned ← capped 32 "LEAN_NUM_THREADS=64" s!"{ix} check-lean {art}"
    Tests.Cli.expect "the estimate over a 32 GiB cap" warned 0 [warning, "LEAN_NUM_THREADS"]
    -- a pool of 2 and two workers under 8 GiB: no line
    let small ← capped 8 "LEAN_NUM_THREADS=2" s!"{ix} check-lean {art} --workers 2"
    Tests.Cli.expect "a pool of 2 under 8 GiB" small 0
    if (small.stderr.splitOn warning).length > 1 then
      throw <| IO.userError s!"a pool of 2 under 8 GiB: a warning\n{small.stderr}"
    -- kernel-check-ixe keeps the caller's stack: 16 workers on 1 GiB stacks over 8 GiB; 8 MiB
    -- stacks with a pool of 2 fit
    Tests.Cli.expect "kernel-check-ixe, 16 workers over the cap" (← capped 8
      "LEAN_STACK_SIZE_KB=1048576 IX_KERNEL_WORKERS=16" s!"{kci} {art} {dir / "capped.jsonl"}") 2
      ["16 worker threads", "LEAN_STACK_SIZE_KB"]
    let kciSmall ← capped 8 "LEAN_STACK_SIZE_KB=8192 LEAN_NUM_THREADS=2" s!"{kci} {art} {dir / "capped.jsonl"}"
    Tests.Cli.expect "kernel-check-ixe, 8 MiB stacks and a pool of 2 under 8 GiB" kciSmall 0
    if (kciSmall.stderr.splitOn warning).length > 1 then
      throw <| IO.userError s!"kernel-check-ixe under 8 GiB: a warning\n{kciSmall.stderr}"
    -- verify-host: a statement issued at the defaults, replayed under each setting
    let stmt := dir / "limits.stmt"
    let issued ← checkLean #["--host-out", stmt.toString] #[]
    Tests.Cli.expect "issue a host statement" issued 0
    let some line := issued.stdout.splitOn "\n" |>.find? (·.startsWith "[check-lean] host admission statement: ")
      | throw <| IO.userError s!"no host statement line\n{issued.stdout}"
    let address := (line.drop "[check-lean] host admission statement: ".length).toString.trimAscii.toString
    let verify := fun (flags : Array String) (vars : Array (String × Option String)) =>
      Tests.Cli.runEnv ix.toString (#["verify-host", address, art.toString, "--statement-file",
        stmt.toString] ++ flags) vars
    Tests.Cli.expect "verify-host at the defaults" (← verify #[] #[]) 0
    Tests.Cli.expect "verify-host lowered" (← verify #["--max-depth", "2"] #[]) 6
      ["declined by the depth limit (2, --max-depth)"]
    Tests.Cli.expect "verify-host variable" (← verify #[] #[("IX_KERNEL_MAX_DEPTH", some "2")]) 6
      ["declined by the depth limit (2, IX_KERNEL_MAX_DEPTH)"]
    Tests.Cli.expect "verify-host raised" (← verify #["--max-depth", "100000"] #[]) 0
    Tests.Cli.expect "verify-host malformed" (← verify #["--max-depth", "x"] #[]) 2
      ["--max-depth takes a positive whole number"]
    -- kernel-check-ixe: the variables; a decline exits 6
    let rows := dir / "rows.jsonl"
    Tests.Cli.expect "kernel-check-ixe lowered" (← Tests.Cli.runEnv kci.toString
      #[art.toString, rows.toString] #[("IX_KERNEL_MAX_DEPTH", some "2")]) 6
      ["declined by the depth limit (2, IX_KERNEL_MAX_DEPTH)"]
    Tests.Cli.expect "kernel-check-ixe malformed" (← Tests.Cli.runEnv kci.toString
      #[art.toString, rows.toString] #[("IX_KERNEL_MAX_DEPTH", some "0")]) 2
    -- ix compile: the typing of an input with semantic contracts declines by a lowered limit
    let contracts := dir / "Contracts.lean"
    IO.FS.writeFile contracts
      "import Ix.Compile.SourceContract.Elab\nimport Tests.Ix.SourceContract.Imported\n\
       def cliLocal (~1 x : Nat) : ~ Nat := x\n"
    let compile := fun (flags : Array String) (vars : Array (String × Option String)) =>
      Tests.Cli.runEnv ix.toString (#["compile", contracts.toString, "--no-build", "--consts",
        "cliLocal", "--out", (dir / "contracts.ixe").toString] ++ flags) vars
    Tests.Cli.expect "compile, contracts, defaults" (← compile #[] #[]) 0
    Tests.Cli.expect "compile, contracts, lowered" (← compile #["--max-depth", "2"] #[]) 6
      ["declined by the depth limit (2, --max-depth)"]
    Tests.Cli.expect "compile, contracts, variable" (← compile #[] #[("IX_KERNEL_MAX_DEPTH", some "2")]) 6
      ["declined by the depth limit (2, IX_KERNEL_MAX_DEPTH)"]
    Tests.Cli.expect "compile, --workers 0" (← compile #["--workers", "0"] #[]) 2
      ["--workers takes a positive whole number"]
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
  Tests.Cli.testDeepRecordExits
  Tests.Cli.testKernelLimits
  --Tests.Cli.run "ix" (#["store", "ix_test/IxTest.lean"]) none
  --Tests.Cli.run "ix" (#["prove", "ix_test/IxTest.lean", "one"]) none
  return 0
