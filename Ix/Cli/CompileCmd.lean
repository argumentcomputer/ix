module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.RoleBinding.Compile
public import Ix.CompileCertified
public import Ix.Meta
public import Ix.TracingTexray
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile
public import Ix.Cli.ValidateCmd
public import Ix.Cli.DriverOptions
import Std.Internal.UV.System

public section

open System (FilePath)
open Ix.EnvScope

private def defaultOutPathFor (pathStr : String) : String :=
  let path := FilePath.mk pathStr
  let stem := path.fileStem.getD (path.fileName.getD pathStr)
  stem.toLower ++ ".ixe"

/-- `--sharing-limits SPEC`: validate the override (the format of
`Ix.Sharing.Exact.Limits.withOverrides`, which also accepts the Rust limit
keys) and publish it through `IX_SHARING_LIMITS`, which both compilers read.
Returns the parse error, if any. -/
def applySharingLimitsFlag (p : Cli.Parsed) : IO (Option String) := do
  let some flag := p.flag? "sharing-limits" | return none
  let spec := flag.as! String
  match Ix.CompileM.compilerSharingLimits.withOverrides spec with
  | .error e => return some s!"--sharing-limits: {e}"
  | .ok _ =>
    Std.Internal.UV.System.osSetenv Ix.CompileM.sharingLimitsEnvVar spec
    return none

/-- The certified compiler runs at the default sharing limits: `Ix.Cert.compileReport`,
the function its correctness theorem is about, fixes them, and other limits can
change which constants compile. A valid override (`--sharing-limits`, or a nonempty
`IX_SHARING_LIMITS`) is therefore refused there, with the reason; the uncertified
compilers (`--streamed`, `--rust`) take one. An invalid override is reported by its
parser first. -/
def certifiedLimitsRefusal (p : Cli.Parsed) : IO (Option String) := do
  let inherited := (← IO.getEnv Ix.CompileM.sharingLimitsEnvVar).any (!·.trimAscii.isEmpty)
  unless (p.flag? "sharing-limits").isSome || inherited do return none
  return some "the certified compiler runs at the default sharing limits, which its \
correctness theorem fixes; --sharing-limits and IX_SHARING_LIMITS apply only to the \
uncertified compilers (--streamed, --rust)"

/-- Failures listed root causes first: a constant that failed only because a
    dependency is missing is a cascade, listed after the ones that name the
    cause (a refusal's message must be visible in the bounded listing). -/
private def rootCausesFirst {α : Type} (xs : List (α × String)) : List (α × String) :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  xs.filter (!cascade ·.2) ++ xs.filter (cascade ·.2)

/-- The report describes this invocation's published envelope. An abort
never opens a possibly pre-existing output file. The supported headers are
one byte; checked object/claim versions are independent of this value. -/
def Ix.Cli.publishedEnvelopeVersion (published : Bool) (path : FilePath) : IO (Option Nat) := do
  unless published do return none
  let file ← IO.FS.Handle.mk path .read
  let header ← file.read 1
  match (header[0]? : Option UInt8) with
  | some 0xE4 => return some 4
  | some 0xE5 => return some 5
  | _ => throw <| IO.userError s!"compile report: invalid published envelope header in {path}"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  -- Keep the environment-variable interface for scripts, while giving the
  -- CLI an ordinary discoverable switch. The Rust compiler and serializer
  -- both consult IX_VERBOSE, so setting it once enables the whole pipeline.
  if p.hasFlag "verbose" then
    Std.Internal.UV.System.osSetenv "IX_VERBOSE" "1"
  if let some e ← applySharingLimitsFlag p then
    p.printError s!"error: {e}"
    return 1
  -- The certified compiler (`Ix.Cert.compileReport`) is the default, at the
  -- default sharing limits; `--rust` selects the uncertified Rust compiler and
  -- `--streamed` the uncertified streamed pipeline. The streamed pipeline's
  -- options: the sharing limits (`--sharing-limits` / `IX_SHARING_LIMITS`) and,
  -- with `--verbose`, its phase timings.
  let useRust := p.hasFlag "rust"
  let streamed := p.hasFlag "streamed"
  if useRust && streamed then
    p.printError "error: --rust and --streamed select different compilers"
    return 1
  let workers := match p.flag? "workers" with
    | some f => max 1 (f.as! Nat)
    | none => 32
  let opts ← if useRust then pure {} else
    match ← Ix.Cli.driverOptionsFromEnv (dbg := p.hasFlag "verbose") with
    | .ok opts => pure opts
    | .error e =>
      p.printError s!"error: {e}"
      return 1
  unless useRust || streamed do
    if let some e ← certifiedLimitsRefusal p then
      p.printError s!"error: {e}"
      return 1

  let some path := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a Lean source file"
      return 1
  let pathStr := path.as! String
  let outPath : String :=
    (p.flag? "out").map (·.as! String) |>.getD (defaultOutPathFor pathStr)

  -- Reuse existing imports when retrying the Ix compiler. The frontend still
  -- elaborates the input file; only Lake's dependency build/cache step is skipped.
  unless p.hasFlag "no-build" do
    buildFile pathStr
  let fe ← getFileEnvCore pathStr
  let leanEnv := fe.env

  println! "Running Ix compiler on {pathStr}"

  -- Build the exclusion set from `--exclude` (comma-separated) +
  -- `--exclude-file` (one per line). Names in this set are stripped
  -- from the seed list before transitive closure; if no other seed
  -- references them, they don't make it into the compiled env. Note
  -- the exclusion only affects the SEED set, not the closure — a
  -- referenced excluded name still gets pulled in via deps.
  let excludeSet : Std.HashSet Lean.Name ← do
    let mut s : Std.HashSet Lean.Name := {}
    if let some flag := p.flag? "exclude" then
      for n in parsePrefixes (flag.as! String) do s := s.insert n
    if let some flag := p.flag? "exclude-file" then
      -- Shared names-file grammar (Ix.Cli.ConstsFile); names resolve here
      -- via `toName` like the `--exclude` comma-list.
      for n in ← Ix.Cli.ConstsFile.read (flag.as! String) do
        s := s.insert n.toName
    pure s
  if !excludeSet.isEmpty then
    IO.println s!"[compile] exclude: {excludeSet.size} name(s) will be dropped from seed set"

  -- Optional `--module Foo.Bar,Baz` filter. Filters by the SOURCE MODULE
  -- a constant came from (via `Lean.Environment.getModuleIdxFor?` +
  -- `allImportedModuleNames`), not by the constant's own name. This
  -- catches consts whose name doesn't carry the namespace prefix —
  -- e.g. macro-emitted decls like `good_def basicDef : Type := Prop`
  -- inside `namespace Tests.Ix.Kernel.TutorialDefs` that register
  -- under bare `basicDef`. The module that elaborated them is
  -- `Tests.Ix.Kernel.TutorialDefs`, so the prefix still matches.
  -- Seeds pass through `collectSelectedDeps` (a selected input's closure:
  -- recursors, whole logical units and checker support included), as do
  -- `--consts` and `--exclude` seeds.
  -- Flag name is `--module` (not `--ns`) because the match is against
  -- the source module name, not the decl's own namespace.
  -- `--consts` / `--consts-file`: seed by EXACT constant name, transitive
  -- deps via `collectSelectedDeps` — a closure-only env (e.g. one benchmark constant
  -- + deps) instead of the whole import env. Resolution tries `String.toName`
  -- first, then a displayed-form scan so `_private`/numeric components
  -- round-trip. Mutually exclusive with `--module`; `--exclude` doesn't
  -- apply (the seed list is already explicit).
  let constsSeeds ← Ix.Cli.ConstsFile.gather p
  if !constsSeeds.isEmpty && (p.flag? "module").isSome then
    p.printError "error: --consts/--consts-file and --module are mutually exclusive"
    return 1
  let constList ←
    if p.hasFlag "local" then do
      if !constsSeeds.isEmpty || (p.flag? "module").isSome || !excludeSet.isEmpty then
        p.printError "error: --local excludes --consts/--consts-file, --module and --exclude"
        return 1
      let closed := localConstList fe
      IO.println s!"[compile] local: {closed.length} constants (the file's own and their dependencies)"
      pure closed
    else if !constsSeeds.isEmpty then do
      let mut seeds : List Lean.Name := []
      let mut missing : List String := []
      -- Displayed-form fallback, built at most once: a fresh
      -- `constants.toList.find?` scan per missing name is O(names × env),
      -- seconds of allocation per name at mathlib scale.
      let mut byDisplayed : Option (Std.HashMap String Lean.Name) := none
      for n in constsSeeds do
        let name := n.toName
        if leanEnv.constants.contains name then
          seeds := name :: seeds
        else
          let map := byDisplayed.getD <| .ofList <|
            leanEnv.constants.toList.map fun (m, _) => (toString m, m)
          byDisplayed := some map
          match map.get? n with
          | some m => seeds := m :: seeds
          | none => missing := n :: missing
      if !missing.isEmpty then
        p.printError s!"error: no constant(s) named {missing} in the environment"
        return 1
      IO.println s!"[compile] consts: {seeds.length} seed constant(s)"
      let closed := collectSelectedDeps leanEnv seeds
      IO.println s!"[compile] consts: {closed.length} constants after transitive-dep closure"
      pure closed
    else match p.flag? "module" with
    | none =>
      if excludeSet.isEmpty then defaultConstList fe pathStr
      else
        -- Exclusion applies on top of the default scope (full env for classic
        -- files, module-visible closure for module-mode files).
        let base ← defaultConstList fe pathStr
        let seeds := base.filterMap fun (n, _) =>
          if excludeSet.contains n then none else some n
        IO.println s!"[compile] exclude applied: {seeds.length} seed constants"
        pure (collectSelectedDeps leanEnv seeds)
    | some flag =>
      let raw := flag.as! String
      let prefixes := parsePrefixes raw
      if prefixes.isEmpty then
        IO.println s!"[compile] warning: --module '{raw}' parsed to empty list; compiling full env"
        pure leanEnv.constants.toList
      else
        let moduleNames := leanEnv.allImportedModuleNames
        let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
          if excludeSet.contains n then none
          else match leanEnv.getModuleIdxFor? n with
          | none => none  -- locally-elaborated, no module — drop under `--ns`
          | some idx =>
            let mod := moduleNames[idx.toNat]!
            if prefixes.any (·.isPrefixOf mod) then some n else none
        IO.println s!"[compile] filter: {prefixes.length} module-prefix(es), {seeds.length} seed constants"
        let closed := collectSelectedDeps leanEnv seeds
        IO.println s!"[compile] filter: {closed.length} constants after transitive-dep closure"
        pure closed

  let totalConsts := constList.length
  println! "Total constants: {totalConsts}"

  -- Window the tree-RSS sampler around the compile so the row's peak-rss
  -- is the compile step's own high-water (the loaded Lean env is still in
  -- the baseline — RSS is absolute).
  let benched := (p.flag? "json").isSome
  if benched then
    TracingTexray.startSampler
    TracingTexray.resetPeakTreeRss

  -- Keep the raw compile private until its actual support, evidence and
  -- binding are generated. Publication is atomic after final serialization.
  let allowPartial := p.hasFlag "allow-partial"
  let strictAnon := p.hasFlag "anon"
  let start ← IO.monoMsNow
  -- The requested constants, whose publications and failures `finalize` keeps.
  let requested := Ix.Compile.CompileInput.plain constList
  let rootOf (env : Ixon.Env) : String :=
    toString ((Ix.Merkle.merkleRootCanonical (env.consts.toArray.map (·.1))).getD Ix.Merkle.zeroAddress)
  let statusOf (original : Ixon.Env) (failures : Std.HashMap Ix.Name String) :
      Ix.CompileM.CompileEnvStatus :=
    let ungrounded := (failures.toArray.map fun (n, r) => (n.pretty, r)).qsort (fun a b => a.1 < b.1)
    { root := rootOf original, ungrounded, nonCanonical := #[], bytes := 0, named := 0, uniqueAnon := 0 }
  -- Finalize (support, certificates, binding; the finalized artifact is checked
  -- again), strip names under `--anon`, serialize, publish atomically.
  let publish (backend : Ix.RoleBinding.Compile.Backend) (original : Ixon.Env)
      (status : Ix.CompileM.CompileEnvStatus) (postStep : Ixon.Env → Except String Unit) :
      IO Ix.CompileM.CompileEnvStatus := do
    let artifact ← Ix.RoleBinding.Compile.finalize backend leanEnv
      Ix.RoleBinding.Compile.nativeCertSource requested original Ix.Resource.typingLimits
    IO.ofExcept (postStep artifact)
    let artifact := if strictAnon then { artifact with
      named := {}, names := {}, comms := {}, addrToName := {} } else artifact
    let bytes ← IO.ofExcept (Ixon.serEnv artifact)
    Ix.RoleBinding.Compile.writeAtomic (FilePath.mk outPath) bytes
    return { status with
      bytes := bytes.size.toUInt64
      named := artifact.named.size.toUInt64
      uniqueAnon := artifact.consts.size.toUInt64
      root := rootOf artifact }
  let verbose := (← IO.getEnv "IX_VERBOSE").isSome || (← IO.getEnv "IX_COMPILE_DBG").isSome
  let status ← if useRust then
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv leanEnv constList).mapError toString)
    let constList ← IO.ofExcept input.prepare
    if verbose then
      IO.eprintln s!"[compile] source contract preparation: {((← IO.monoMsNow) - start).formatMs}"
    IO.FS.withTempDir fun dir => do
      let rawPath := dir / "original.ixe"
      let status ← Ix.CompileM.rsCompileEnvBytesFFI constList rawPath.toString allowPartial
      if !allowPartial && !status.ungrounded.isEmpty then return status
      let original ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile rawPath))
      publish Ix.RoleBinding.Compile.rustBackend original status fun _ => pure ()
  else if streamed then
    -- The streamed pipeline with its post-steps (`compileLeanInputValidated`):
    -- uncertified, kept for comparison.
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv leanEnv constList).mapError toString)
    let out ← match ← Ix.CompileM.compileLeanInputValidated input (numWorkers := workers) (opts := opts) with
      | .ok out => pure out
      | .error e => throw (IO.userError s!"compile refused: {e}")
    let status := statusOf out.env out.cenv.ungrounded
    if !allowPartial && !status.ungrounded.isEmpty then pure status
    else
      publish (Ix.RoleBinding.Compile.leanBackend workers opts) out.env status fun artifact =>
        Ix.CompileM.resourcePostStep { out with env := artifact }
  else
    -- The certified compiler (`Ix.CompileM.compileCertified`: `Ix.Cert.compileReport`
    -- on the canonical input), as `ix compile-lean` runs it.
    let log (s : String) : IO Unit := if verbose then IO.eprintln s!"[compile] {s}" else pure ()
    let out ← match ← Ix.CompileM.compileCertified leanEnv constList workers log with
      | .ok out => pure out
      | .error e => throw (IO.userError s!"compile refused: {e}")
    let status := statusOf out.env out.failures.toMap
    if !allowPartial && !status.ungrounded.isEmpty then pure status
    else
      publish (Ix.RoleBinding.Compile.certifiedBackend workers) out.env status
        (Ix.CompileM.validateFinalized out.annotated)
  let size := status.bytes.toNat
  let elapsed := (← IO.monoMsNow) - start

  let ungroundedCount := status.ungrounded.size
  -- Fail-closed default: the compile wrote nothing when `!allowPartial` and
  -- anything requested is ungrounded (the final path was never created).
  let failClosed := !allowPartial && ungroundedCount > 0

  -- `--report`: machine-readable compile status, written on success,
  -- fail-closed abort, and partial publish alike.
  if let some flag := p.flag? "report" then
    let envelopeVersion ← Ix.Cli.publishedEnvelopeVersion (!failClosed) (FilePath.mk outPath)
    let flagStr (name : String) : Lean.Json :=
      (p.flag? name).map (Lean.Json.str <| ·.as! String) |>.getD Lean.Json.null
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (2 : Nat))
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("ixeFormatVersion", Lean.toJson envelopeVersion)
      , ("input", Lean.Json.str pathStr)
      , ("output", Lean.Json.str outPath)
      , ("seeds", Lean.Json.mkObj
          [ ("consts", flagStr "consts")
          , ("constsFile", flagStr "consts-file")
          , ("module", flagStr "module")
          , ("exclude", flagStr "exclude")
          , ("excludeFile", flagStr "exclude-file") ])
      , ("requested", Lean.toJson totalConsts)
      , ("named", Lean.toJson status.named.toNat)
      , ("uniqueAnon", Lean.toJson status.uniqueAnon.toNat)
      , ("ungroundedCount", Lean.toJson ungroundedCount)
      , ("ungrounded", Lean.Json.arr <| status.ungrounded.map fun (n, r) =>
          Lean.Json.mkObj
            [("name", Lean.Json.str n), ("reason", Lean.Json.str r)])
      , ("root", Lean.Json.str status.root)
      , ("allowPartial", Lean.toJson allowPartial)
      , ("written", Lean.toJson (!failClosed))
      , ("bytes", Lean.toJson size)
      , ("elapsedMs", Lean.toJson elapsed) ]
    IO.FS.writeFile (flag.as! String) (report.pretty ++ "\n")

  if ungroundedCount > 0 then
    let stream ← if failClosed then IO.getStderr else IO.getStdout
    let verdict := if failClosed then
      s!"error: {ungroundedCount} requested constant(s) failed to compile; \
nothing written to {outPath} (use --allow-partial to serialize the \
grounded subset)"
    else
      s!"PARTIAL: {ungroundedCount} requested constant(s) failed to compile; \
serialized the grounded subset ({status.named} named, \
{status.uniqueAnon} unique constants)"
    stream.putStrLn verdict
    for (n, r) in (rootCausesFirst status.ungrounded.toList).take 10 do
      stream.putStrLn s!"  [ungrounded] {n}: {(r.replace "\n" " ").take 200}"
    if ungroundedCount > 10 then
      stream.putStrLn s!"  … and {ungroundedCount - 10} more (see --report for the full list)"
    if failClosed then
      return 1

  println! "Compiled and wrote {fmtBytes size} env to {outPath} in {elapsed.formatMs}"
  IO.println s!"##benchmark## {elapsed} {size} {totalConsts}"
  if let some flag := p.flag? "json" then
    let key := (p.flag? "json-name").map (·.as! String)
      |>.getD ((FilePath.mk pathStr).fileStem.getD "env")
    let secs := elapsed.toFloat / 1000.0
    let tput := if elapsed > 0
      then totalConsts.toFloat * 1000.0 / elapsed.toFloat else 0.0
    let peakRss ← TracingTexray.peakTreeRssBytes
    Ix.Benchmark.Results.writeRow (flag.as! String) key "ok"
      [ ("compile-time", Ix.Benchmark.Results.jsonRound 3 secs)
      , ("file-size", Lean.toJson size)
      , ("constants", Lean.toJson totalConsts)
      , ("throughput", Ix.Benchmark.Results.jsonRound 2 tput)
      , ("peak-rss", Lean.toJson peakRss) ]
  return 0


def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile a Lean file to Ixon with the certified compiler (`Ix.Cert.compileReport`, as `ix compile-lean`); `--rust` selects the uncertified Rust compiler, `--streamed` the uncertified streamed pipeline"

  FLAGS:
    v, verbose;               "Print compiler phase timings, scheduler progress, and serialization progress. Equivalent to IX_VERBOSE=1."
    rust;                     "Compile with the uncertified Rust compiler instead of Ix.Cert.compileReport. Shared finalization and artifact checks still run before writing the output. This backend is outside CompileCorrect; `ix compile-lean --rust-check` provides byte-comparison evidence for a selected input."
    streamed;                 "Compile with the streamed Lean pipeline instead of the certified compiler. UNCERTIFIED: only its fold is proved to be the certified compiler's; its streamed front end is tested, not proved. Kept for comparison."
    workers        : Nat;    "Worker count for the certified compiler's parallel phases (default 32). Ignored with --rust."
    "no-build";               "Skip the Lake build/cache step and reuse existing import artifacts. The input file is still elaborated. The caller must ensure all imports are built and up to date."
    out            : String; "Output path for serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe` (e.g. CompileMathlib.lean -> compilemathlib.ixe)"
    consts         : String; "Comma-separated EXACT constant names to compile (transitive deps pulled in automatically) instead of the whole import env — e.g. `Nat.add_comm`. Same flag/shape as `ix check --consts`. Mutually exclusive with --module; --exclude does not apply."
    "consts-file"  : String; "Additionally read seed constant names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    "local" ;               "Compile only the constants the input file itself declares, with their transitive dependencies, instead of the whole import env. Mutually exclusive with --consts, --consts-file, --module and --exclude."
    module         : String; "Comma-separated module-name prefixes to filter on (e.g. 'Tests.Ix.Kernel.TutorialDefs,Tests.Ix.Kernel.NatReduction'). Match is against the SOURCE MODULE a constant came from (via `Lean.Environment.getModuleIdxFor?`), not the constant's own name — so macro-emitted decls that register under unqualified names still get caught when their host module's name matches. Transitive deps are pulled in automatically."
    exclude        : String; "Comma-separated exact Lean.Name(s) to strip from the seed set. Excluded names that are still referenced by another seed will reappear via the transitive-dep closure."
    "exclude-file" : String; "Path to a file with one Lean.Name per line to strip from the seed set. Same semantics as --exclude; same line format as `ix check --consts-file`."
    json           : String; "Write the compile's benchmark results row (compile-time, file-size, constants, throughput) to this path, merging into any existing rows object."
    "json-name"    : String; "Row key for the --json row (default: the input file's stem, e.g. `CompileInitStd`)"
    "allow-partial" ;        "Serialize the grounded subset and exit 0 even when some requested constants fail to compile. Default is fail-closed: any ungrounded constant means a nonzero exit and NO output file."
    anon           ;         "Strict-anonymous output: clear §4 names, §5 metadata, and §6 commitments (after hint finalization, so §3 anon hints survive). The env root is unchanged — it covers §2 only. Default keeps names: they are harmless to catalog semantics and valuable for fidelity/debugging."
    "sharing-limits" : String; "Override resource limits of the canonical sharing construction: comma-separated key=value items (values: digits, 2^k or max) or `unbounded`. Keys: expr_visits, depth, nodes, states, transitions, cost_evals, output_bytes, materialize, materialize_work, knapsack_cells (Lean); input_nodes, distinct_nodes, height, candidates, states, layer_states, transitions, work, output_bytes, knapsack_cells (Rust). The defaults are far above every corpus maximum; a constant that reaches one fails to compile and names the limit. Only with --rust or --streamed: the certified compiler's theorem fixes the default limits. Sets IX_SHARING_LIMITS."
    report         : String; "Write a machine-readable JSON compile report (versions, seed spec, requested/named/unique-anon/ungrounded counts, full ungrounded list, canonical consts merkle root, bytes, elapsed ms) to this path — written on success, fail-closed abort, and partial publish alike."

  ARGS:
    path : String; "Path to the Lean source file to compile."
]

end

