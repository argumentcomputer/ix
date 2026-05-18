/-
  `ix check <path>`: typecheck a serialized `.ixe` environment through
  the Ix Rust kernel. Path is positional and required.

  Two kernel modes:

  - Default (Meta): kernel runs with metadata fields populated (Lean.Name,
    binder info, mdata). Supports `--ns` / `--consts` / `--consts-file`
    for seed filtering and `--fail-out` for bisect-loop workflows.
  - `--anon` (metadata-free): the env is loaded via `Env::get_anon` —
    `named`/`names`/`comms` sections are discarded at load time, never
    reaching the kernel. Every kernel-checkable address (every constant
    except Muts blocks and projections — projections are covered by
    their parent block) is checked. The kernel's typechecking logic
    structurally cannot read metadata (`M::MField<T>` is `()` in Anon
    mode); progress labels are `@<hex>` addresses, not names.

    `--anon` is incompatible with `--ns` / `--consts` / `--consts-file`:
    the anon path checks everything in the env. Add `--addrs <hex,…>`
    in the future if address-based filtering is needed.

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
public import Ix.Cli.ValidateCmd
public import Std.Internal.UV.System

public section

open System (FilePath)
open Ix.KernelCheck

namespace Ix.Cli.CheckCmd

/-- Combined seed selector: prefixes (`--ns`) ∪ exact names
    (`--consts`, `--consts-file`). Meta-mode only. -/
private structure SeedSpec where
  prefixes : List Lean.Name := []
  exacts   : List Lean.Name := []

private def SeedSpec.isEmpty (s : SeedSpec) : Bool :=
  s.prefixes.isEmpty && s.exacts.isEmpty

/-- Read one constant name per line from `path`. Blank lines and lines
    starting with `#` (after trimming) are ignored. -/
private def readNamesFile (path : String) : IO (List Lean.Name) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let names : List Lean.Name := lines.filterMap fun raw =>
    let cs := raw.toList.dropWhile Char.isWhitespace
    let trimmed := String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse
    if trimmed.isEmpty || trimmed.startsWith "#" then none
    else some trimmed.toName
  pure names

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
    let parsed ← readNamesFile path
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
    let mut missing : Array Lean.Name := #[]
    for n in s.exacts do
      if !allNames.contains n then
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
    `failOutPath` (when nonempty). -/
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
  for i in [:results.size] do
    match results[i]! with
    | none => passed := passed + 1
    | some err => failures := failures.push (s!"#{i}", err.message)

  IO.println s!"[check] checked {results.size} constants in {elapsed.formatMs}"
  IO.println s!"[check] {passed}/{results.size} passed"
  reportFailures failures

  if !failOutPath.isEmpty then
    IO.println s!"[check] streamed {failures.size} failure(s) to {failOutPath}"

  IO.println s!"##check## {elapsed} {passed} {failures.size} {results.size}"
  return if failures.isEmpty then 0 else 1

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

  IO.println s!"##check## {elapsed} {passed} {failures.size} {seedNames.size}"
  return if failures.isEmpty then 0 else 1

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String

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
  if anon then
    let hasConsts := p.flag? "consts" |>.isSome
    let hasNs := p.flag? "ns" |>.isSome
    let hasConstsFile := p.flag? "consts-file" |>.isSome
    if hasConsts || hasNs || hasConstsFile then
      p.printError "error: --anon checks the entire env; --consts/--ns/--consts-file are unsupported"
      return 1
    runCheckAnon envPath p
  else
    runCheckMeta envPath p

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck a serialized Ixon environment through the Ix Rust kernel"

  FLAGS:
    anon;                   "Run the kernel in anon mode (no metadata read from .ixe)"
    ns            : String; "Comma-separated Lean.Name prefixes to filter on (meta mode only)"
    consts        : String; "Comma-separated EXACT constant names to seed (meta mode only)"
    "consts-file" : String; "Path to a file with one constant name per line (meta mode only)"
    "fail-out"    : String; "Write failing constants to this path (consumable by --consts-file)"
    workers       : Nat;    "Number of parallel kernel-check workers; 1 disables parallelism (default: available_parallelism). Plumbs via IX_KERNEL_CHECK_WORKERS env var."
    verbose;                "Log every constant on its own line (default: quiet)"

  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
