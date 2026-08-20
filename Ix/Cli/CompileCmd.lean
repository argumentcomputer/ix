module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta
public import Ix.TracingTexray
public import Ix.Benchmark.Results
public import Ix.Cli.ConstsFile
public import Ix.Cli.ValidateCmd

public section

open System (FilePath)
open Ix.EnvScope

private def defaultOutPathFor (pathStr : String) : String :=
  let path := FilePath.mk pathStr
  let stem := path.fileStem.getD (path.fileName.getD pathStr)
  stem.toLower ++ ".ixe"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a Lean source file"
      return 1
  let pathStr := path.as! String
  let outPath : String :=
    (p.flag? "out").map (·.as! String) |>.getD (defaultOutPathFor pathStr)

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
  -- Seeds pass through `collectDeps` for the transitive-dep closure.
  -- Flag name is `--module` (not `--ns`) because the match is against
  -- the source module name, not the decl's own namespace.
  -- `--consts` / `--consts-file`: seed by EXACT constant name, transitive
  -- deps via `collectDeps` — a closure-only env (e.g. one benchmark constant
  -- + deps) instead of the whole import env. Resolution tries `String.toName`
  -- first, then a displayed-form scan so `_private`/numeric components
  -- round-trip. Mutually exclusive with `--module`; `--exclude` doesn't
  -- apply (the seed list is already explicit).
  let constsSeeds ← Ix.Cli.ConstsFile.gather p
  if !constsSeeds.isEmpty && (p.flag? "module").isSome then
    p.printError "error: --consts/--consts-file and --module are mutually exclusive"
    return 1
  let constList ←
    if !constsSeeds.isEmpty then do
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
      let closed := collectDeps leanEnv seeds
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
        pure (collectDeps leanEnv seeds)
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
        let closed := collectDeps leanEnv seeds
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

  -- Rust compiles and writes the `.ixe` directly (streamed — no
  -- env-sized ByteArray crosses the FFI; `<out>.tmp` + atomic rename).
  -- The file is the canonical `Ixon.Env::put` format and round-trips
  -- through `Ixon.Env::get`, so later runs (e.g. `ix check-ixon`) can
  -- skip the Lean → IxOn compile step.
  let allowPartial := p.hasFlag "allow-partial"
  let start ← IO.monoMsNow
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constList outPath allowPartial
  let size := status.bytes.toNat
  let elapsed := (← IO.monoMsNow) - start

  let ungroundedCount := status.ungrounded.size
  -- Fail-closed default: the FFI wrote nothing when `!allowPartial` and
  -- anything requested is ungrounded (the final path was never created).
  let failClosed := !allowPartial && ungroundedCount > 0

  -- `--report`: machine-readable compile status, written on success,
  -- fail-closed abort, and partial publish alike.
  if let some flag := p.flag? "report" then
    let flagStr (name : String) : Lean.Json :=
      (p.flag? name).map (Lean.Json.str <| ·.as! String) |>.getD Lean.Json.null
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (1 : Nat))
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("ixeFormatVersion", Lean.toJson Ixon.Env.VERSION.toNat)
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
    for (n, r) in status.ungrounded.toList.take 10 do
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
  "Compile Lean file to Ixon"

  FLAGS:
    out            : String; "Output path for serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe` (e.g. CompileMathlib.lean -> compilemathlib.ixe)"
    consts         : String; "Comma-separated EXACT constant names to compile (transitive deps pulled in automatically) instead of the whole import env — e.g. `Nat.add_comm`. Same flag/shape as `ix check-rs --consts`. Mutually exclusive with --module; --exclude does not apply."
    "consts-file"  : String; "Additionally read seed constant names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    module         : String; "Comma-separated module-name prefixes to filter on (e.g. 'Tests.Ix.Kernel.TutorialDefs,Tests.Ix.Kernel.NatReduction'). Match is against the SOURCE MODULE a constant came from (via `Lean.Environment.getModuleIdxFor?`), not the constant's own name — so macro-emitted decls that register under unqualified names still get caught when their host module's name matches. Transitive deps are pulled in automatically."
    exclude        : String; "Comma-separated exact Lean.Name(s) to strip from the seed set. Excluded names that are still referenced by another seed will reappear via the transitive-dep closure."
    "exclude-file" : String; "Path to a file with one Lean.Name per line to strip from the seed set. Same semantics as --exclude; same line format as `ix check-rs --consts-file`."
    json           : String; "Write the compile's benchmark results row (compile-time, file-size, constants, throughput) to this path, merging into any existing rows object."
    "json-name"    : String; "Row key for the --json row (default: the input file's stem, e.g. `CompileInitStd`)"
    "allow-partial" ;        "Serialize the grounded subset and exit 0 even when some requested constants fail to compile. Default is fail-closed: any ungrounded constant means a nonzero exit and NO output file."
    report         : String; "Write a machine-readable JSON compile report (versions, seed spec, requested/named/unique-anon/ungrounded counts, full ungrounded list, canonical consts merkle root, bytes, elapsed ms) to this path — written on success, fail-closed abort, and partial publish alike."

  ARGS:
    path : String; "Path to the Lean source file to compile."
]

end
