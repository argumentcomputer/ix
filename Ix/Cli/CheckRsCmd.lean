/-
  `ix check <path>`: typecheck a serialized `.ixe` environment through
  the Ix Rust kernel. Path is positional and required.

  Two kernel modes:

  - Default (Meta): kernel runs with metadata fields populated (Lean.Name,
    binder info, mdata). Supports `--ns` / `--consts` / `--consts-file`
    for seed filtering and `--fail-out` for bisect-loop workflows. Seeded
    meta checks are SUBJECT-ONLY: each seed is checked with its deps
    lazily ingressed but trusted, not re-checked.
  - `--anon` (metadata-free): the env is loaded via `Env::get_anon` —
    `named`/`names`/`comms` sections are discarded at load time, never
    reaching the kernel. The kernel's typechecking logic structurally
    cannot read metadata (`M::MField<T>` is `()` in Anon mode); progress
    labels are `@<hex>` addresses, not names.

    Without a filter, every kernel-checkable address is checked (whole
    env). With `--consts` / `--consts-file`, the named constants are
    checked together with their FULL dependency closures — the same mode
    and scope as the zkVM hosts' `--consts` execute path, so an
    out-of-circuit run is directly comparable to the in-circuit one. Add
    `--skip-deps` for a subject-only check (deps trusted), mirroring
    `zisk-host --skip-deps`. `--ns` prefix filtering stays meta-only.

  Direct Lean → kernel typechecking (compile-and-check from source) is
  available via the `rsCheckConstsFFI` API for tests
  (`Tests/Ix/Kernel/Tutorial.lean`, `Tests/Ix/Kernel/CheckEnv.lean`).
  Use `ix compile <file>` first, then `ix check <output.ixe>`.
-/
module
public import Cli
public import Ix.Common
public import Ix.KernelCheck
public import Ix.Meta
public import Ix.TracingTexray
public import Ix.Benchmark.Neutral
public import Ix.Cli.ConstsFile
public import Ix.Cli.ValidateCmd
public import Std.Internal.UV.System

public section

open System (FilePath)
open Ix.KernelCheck

namespace Ix.Cli.CheckRsCmd

/-- Combined seed selector: prefixes (`--ns`) ∪ exact names
    (`--consts`, `--consts-file`). Meta-mode only. -/
private structure SeedSpec where
  prefixes : List Lean.Name := []
  exacts   : List Lean.Name := []

private def SeedSpec.isEmpty (s : SeedSpec) : Bool :=
  s.prefixes.isEmpty && s.exacts.isEmpty

/-- Build a `SeedSpec` from `--ns`, `--consts`, and `--consts-file`. -/
private def resolveSeedSpec (p : Cli.Parsed) : IO (Option SeedSpec) := do
  let nsFlag     := p.flag? "ns"
  let constsFlag := p.flag? "consts"
  let fileFlag   := p.flag? "consts-file"
  if nsFlag.isNone && constsFlag.isNone && fileFlag.isNone then
    return none
  let mut prefixes : List Lean.Name := []
  let mut exacts   : List Lean.Name := []
  if let some flag := nsFlag then
    let raw := flag.as! String
    prefixes := parsePrefixes raw
    if prefixes.isEmpty then
      IO.println s!"[check] warning: --ns '{raw}' parsed to empty list"
  if let some flag := constsFlag then
    let raw := flag.as! String
    let parsed := parsePrefixes raw
    if parsed.isEmpty then
      IO.println s!"[check] warning: --consts '{raw}' parsed to empty list"
    exacts := exacts ++ parsed
  if let some flag := fileFlag then
    let path := flag.as! String
    -- Shared grammar (Ix.Cli.ConstsFile); meta seeds resolve via `toName`.
    let parsed := (← ConstsFile.read path).toList.map (·.toName)
    if parsed.isEmpty then
      IO.println s!"[check] warning: --consts-file '{path}' yielded zero names"
    else
      IO.println s!"[check] --consts-file '{path}': read {parsed.length} name(s)"
    exacts := exacts ++ parsed
  let spec : SeedSpec := { prefixes, exacts }
  if spec.isEmpty then
    IO.println "[check] warning: filter flags supplied but parsed to empty selection; checking full env"
    return none
  return some spec

/-- Filter an `.ixe`'s checkable names down to the seed spec. -/
private def selectNamesIxon (allNames : Array Lean.Name)
    (spec : Option SeedSpec) : IO (Array Lean.Name) := do
  match spec with
  | none => pure allNames
  | some s =>
    let exactSet : Std.HashSet Lean.Name :=
      s.exacts.foldl (fun acc n => acc.insert n) (Std.HashSet.emptyWithCapacity s.exacts.length)
    -- O(|allNames|) build-up to O(1)-per-check; the previous
    -- `allNames.contains n` was O(|allNames|) per missing-name check,
    -- which at mathlib scale (~700k env × thousands of seed names)
    -- could spend seconds on the preflight alone.
    let allNamesSet : Std.HashSet Lean.Name :=
      allNames.foldl (fun acc n => acc.insert n) (Std.HashSet.emptyWithCapacity allNames.size)
    let mut missing : Array Lean.Name := #[]
    for n in s.exacts do
      if !allNamesSet.contains n then
        missing := missing.push n
    if !missing.isEmpty then
      IO.println s!"[check] warning: {missing.size}/{s.exacts.length} exact name(s) not in env:"
      let shown := min 20 missing.size
      for n in missing[:shown] do
        IO.println s!"  - {n}"
      if missing.size > 20 then
        IO.println s!"  … ({missing.size - 20} more not shown)"
    let seeds := allNames.filter fun n =>
      exactSet.contains n || s.prefixes.any (·.isPrefixOf n)
    IO.println s!"[check] filter: {s.prefixes.length} prefix(es), {s.exacts.length} exact(s) → {seeds.size} seed constants"
    pure seeds

/-- Print up to `limit` failures, then a summary line if truncated. -/
private def reportFailures (failures : Array (String × String))
    (limit : Nat := 30) : IO Unit := do
  if failures.isEmpty then return
  IO.println s!"[check] {failures.size} failure(s):"
  let shown := min limit failures.size
  for (label, msg) in failures[:shown] do
    IO.println s!"  ✗ {label}: {msg}"
  if failures.size > limit then
    IO.println s!"  … ({failures.size - limit} more failures suppressed)"

/-- Anon-mode runner: dispatch to `rsCheckAnonFFI`. The Rust side checks
    every kernel-checkable address in the env and streams failures to
    `failOutPath` (when nonempty). With `--json`, the run is additionally
    recorded as one env-keyed neutral row (key from `--json-name`). -/
private def runCheckAnon (envPath : String) (p : Cli.Parsed) : IO UInt32 := do
  let verbose := p.flag? "verbose" |>.isSome
  let failOutPath : String :=
    match p.flag? "fail-out" with
    | some flag => flag.as! String
    | none      => ""

  IO.println s!"Running Ix kernel check (anon mode) on {envPath}"
  let start ← IO.monoMsNow
  let results ← rsCheckAnonFFI envPath (!verbose) failOutPath
  let elapsed := (← IO.monoMsNow) - start

  let mut passed := 0
  let mut failures : Array (String × String) := #[]
  for (hex, res) in results do
    match res with
    | none => passed := passed + 1
    -- Label with the full content address (`#<hex>`) to match the
    -- Rust-side progress / fail-out output. Pre-#48 we emitted
    -- `#{i}` (result index), which made the CLI summary unjoinable
    -- with the fail-out file's `#<hex>` entries.
    | some err => failures := failures.push (s!"#{hex}", err.message)

  IO.println s!"[check] checked {results.size} constants in {elapsed.formatMs}"
  IO.println s!"[check] {passed}/{results.size} passed"
  reportFailures failures

  if !failOutPath.isEmpty then
    IO.println s!"[check] streamed {failures.size} failure(s) to {failOutPath}"

  if let some flag := p.flag? "json" then
    let key := (p.flag? "json-name").map (·.as! String) |>.getD "env"
    let secs := elapsed.toFloat / 1000.0
    let tput := if elapsed > 0
      then results.size.toFloat * 1000.0 / elapsed.toFloat else 0.0
    let peakRss ← TracingTexray.peakTreeRssBytes
    let status := if failures.isEmpty then "ok" else "rejected"
    Ix.Benchmark.Neutral.writeRow (flag.as! String) key status
      [ ("constants", Lean.toJson results.size)
      , ("check-time", Ix.Benchmark.Neutral.jsonRound 3 secs)
      , ("throughput", Ix.Benchmark.Neutral.jsonRound 2 tput)
      , ("peak-rss", Lean.toJson peakRss) ]

  return if failures.isEmpty then 0 else Ix.Benchmark.Neutral.exitRejected

/-- Anon-mode per-constant runner: dispatch to `rsCheckAnonConstsFFI`. Checks
    the named constants and (by default) their full dependency closures — the
    zkVM hosts' semantics — or subject-only under `--skip-deps`. With
    `--json`, each name runs as its own closure check and records a neutral
    per-name row (see `Ix.Benchmark.Neutral`); without it, the names union
    into one check set. -/
private def runCheckAnonConsts (envPath : String) (p : Cli.Parsed) : IO UInt32 := do
  let verbose := p.flag? "verbose" |>.isSome
  let skipDeps := p.hasFlag "skip-deps"
  let failOutPath : String :=
    match p.flag? "fail-out" with
    | some flag => flag.as! String
    | none      => ""
  let jsonPath : String :=
    match p.flag? "json" with
    | some flag => flag.as! String
    | none      => ""
  if !jsonPath.isEmpty && !failOutPath.isEmpty then
    p.printError "error: --json per-name rows and --fail-out cannot be combined"
    return Ix.Benchmark.Neutral.exitUsage
  -- Raw strings (no toName round-trip): the FFI resolves displayed forms
  -- against the env's `named` map, matching the zkVM hosts' resolution.
  let names ← ConstsFile.gather p
  if names.isEmpty then
    IO.println "[check] error: --consts/--consts-file resolved to zero names"
    return Ix.Benchmark.Neutral.exitUsage

  let scope := if skipDeps then "subject-only" else "full-closure"
  let shape := if jsonPath.isEmpty then "union" else "per-name rows"
  IO.println s!"Running Ix kernel check (anon mode, {scope}, {shape}) on {envPath}"
  IO.println s!"[check] {names.size} seed constant(s): {", ".intercalate names.toList}"
  let start ← IO.monoMsNow
  let results ← rsCheckAnonConstsFFI envPath names skipDeps (!verbose)
    failOutPath jsonPath
  let elapsed := (← IO.monoMsNow) - start

  let mut passed := 0
  let mut failures : Array (String × String) := #[]
  for (hex, res) in results do
    match res with
    | none => passed := passed + 1
    | some err => failures := failures.push (s!"#{hex}", err.message)

  IO.println s!"[check] checked {results.size} constants in {elapsed.formatMs}"
  IO.println s!"[check] {passed}/{results.size} passed"
  reportFailures failures

  if !failOutPath.isEmpty then
    IO.println s!"[check] streamed {failures.size} failure(s) to {failOutPath}"

  return if failures.isEmpty then 0 else Ix.Benchmark.Neutral.exitRejected

/-- Meta-mode runner: dispatch to `rsCheckIxonFFI` with seed filtering. -/
private def runCheckMeta (envPath : String) (p : Cli.Parsed) : IO UInt32 := do
  let verbose := p.flag? "verbose" |>.isSome
  IO.println s!"Running Ix kernel check (meta mode) on {envPath}"
  let spec ← resolveSeedSpec p

  let seedNames ←
    match spec with
    | some s =>
        if s.prefixes.isEmpty && !s.exacts.isEmpty then
          IO.println s!"[check] exact-only filter: {s.exacts.length} name(s); skipping full env name preflight"
          pure s.exacts.toArray
        else
          let namesInEnv ← rsIxonNamesFFI envPath
          IO.println s!"Total checkable names in env: {namesInEnv.size}"
          selectNamesIxon namesInEnv spec
    | none =>
        let namesInEnv ← rsIxonNamesFFI envPath
        IO.println s!"Total checkable names in env: {namesInEnv.size}"
        pure namesInEnv
  if spec.isSome && seedNames.isEmpty then
    IO.println "[check] error: filter resolved to zero constants; refusing to run full-env check"
    return 1
  IO.println s!"[check] checking {seedNames.size} seed constant(s)"

  let expectPass : Array Bool := Array.replicate seedNames.size true
  let failOutPath : String :=
    match p.flag? "fail-out" with
    | some flag => flag.as! String
    | none      => ""
  let start ← IO.monoMsNow
  let results ← rsCheckIxonFFI envPath seedNames expectPass (!verbose) failOutPath
  let elapsed := (← IO.monoMsNow) - start

  let mut passed := 0
  let mut failures : Array (String × String) := #[]
  for i in [:seedNames.size] do
    match results[i]! with
    | none => passed := passed + 1
    | some err => failures := failures.push (toString seedNames[i]!, err.message)

  IO.println s!"[check] checked {seedNames.size} constants in {elapsed.formatMs}"
  IO.println s!"[check] {passed}/{seedNames.size} passed"
  reportFailures failures

  if !failOutPath.isEmpty then
    IO.println s!"[check] streamed {failures.size} failure(s) to {failOutPath}"

  return if failures.isEmpty then 0 else Ix.Benchmark.Neutral.exitRejected

def runCheckRsCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String

  -- Start the process-tree RSS sampler so `--json` rows can report an
  -- accurate peak-rss (the parallel kernel check's high-water mark).
  TracingTexray.startSampler

  -- `--workers N` is plumbed through the existing
  -- `IX_KERNEL_CHECK_WORKERS` env var that `resolve_kernel_check_workers`
  -- (`src/ffi/kernel.rs`) reads. Setting `1` forces a single-threaded
  -- runner, useful for isolating per-worker memory usage and timing.
  if let some flag := p.flag? "workers" then
    let n := flag.as! Nat
    if n == 0 then
      p.printError "error: --workers must be > 0"
      return 1
    Std.Internal.UV.System.osSetenv "IX_KERNEL_CHECK_WORKERS" (toString n)

  let anon := p.flag? "anon" |>.isSome
  let hasConsts := (p.flag? "consts").isSome || (p.flag? "consts-file").isSome
  if p.hasFlag "skip-deps" && !(anon && hasConsts) then
    p.printError "error: --skip-deps only applies to `--anon --consts/--consts-file` \
      (meta-mode seeded checks are always subject-only)"
    return 1
  if anon then
    if p.flag? "ns" |>.isSome then
      p.printError "error: --ns prefix filtering is meta-only; --anon supports --consts/--consts-file"
      return 1
    if hasConsts then
      runCheckAnonConsts envPath p
    else
      runCheckAnon envPath p
  else
    runCheckMeta envPath p

end Ix.Cli.CheckRsCmd

open Ix.Cli.CheckRsCmd in
def checkRsCmd : Cli.Cmd := `[Cli|
  "check-rs" VIA runCheckRsCmd;
  "Typecheck a `.ixe` through the Rust kernel. Exits 0 when everything passes, 3 when the kernel rejects any constant (with --json, the rejected rows are on disk), nonzero otherwise on infrastructure failures."

  FLAGS:
    anon;                   "Run the kernel in anon mode (no metadata read from .ixe)"
    ns            : String; "Comma-separated Lean.Name prefixes to filter on (meta mode only)"
    consts        : String; "Comma-separated EXACT constant names. Meta mode: subject-only seed check. Anon mode: full-closure check of each name (the zkVM hosts' semantics; --skip-deps for subject-only)."
    "consts-file" : String; "Path to a file with one constant name per line (`#` comments); unions with --consts."
    "skip-deps";            "With --anon --consts: check each named constant subject-only, trusting its deps (same flag as zisk-host/sp1-host/bench-typecheck)."
    "fail-out"    : String; "Write failing constants to this path (consumable by --consts-file)"
    json          : String; "Write neutral benchmark rows to this path (anon mode). Whole-env: one row keyed by --json-name. With --consts: each name runs as its OWN closure check (the zkVM hosts' per-constant scope) and records its own timed row, env loaded once."
    "json-name"   : String; "Row key for the whole-env --json row (default: `env`)"
    workers       : Nat;    "Number of parallel kernel-check workers; 1 disables parallelism (default: available_parallelism). Plumbs via IX_KERNEL_CHECK_WORKERS env var."
    verbose;                "Log every constant on its own line (default: quiet)"

  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
