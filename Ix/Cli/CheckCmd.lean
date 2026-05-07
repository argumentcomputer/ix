/-
  `ix check --path <file>`: typecheck a Lean environment through the Rust
  kernel. Mirrors the shape of `ix compile` (build the file, load its env,
  ship to Rust) but pipes the env through `rs_kernel_check_consts` instead
  of `rs_compile_env`.

  Pipeline (Rust side, `src/ffi/kernel.rs`):
    Lean env  →  compile_env  →  ixon_ingress  →  TypeChecker.check_const
                                                 (one batch of names)

  This is the CLI entry point for "does Mathlib typecheck under Ix?". Use
  it like `lake exe ix check --path Benchmarks/Compile/CompileMathlib.lean`
  to run the full pipeline against an entire imported environment.

  Flags:
  - `--path <file>`         (required): file whose env should be checked.
  - `--ns <prefixes>`       (optional, comma-separated): only seed
    constants whose name matches one of the prefixes. Transitive deps
    are still pulled in so the kernel sees a closed sub-environment, but
    we only assert the seeded constants and the closure beneath them.
  - `--consts <names>`      (optional, comma-separated): exact constant
    names to seed (e.g.
    `--consts 'Aesop.GoalUnsafe.rec_6,IntermediateField.LinearDisjoint.trace_algebraMap'`).
    Same closure semantics as `--ns`. Combine with `--ns` and the seed
    set is the union.
  - `--consts-file <path>`  (optional): file with one constant name per
    line. Useful for long `_private.Mathlib.…` names pasted from a
    failing run. Lines starting with `#` and blank lines are ignored.
  - `--fail-out <path>`     (optional): write the names of all failing
    constants to `<path>`, one per line, with the error message as a
    `#`-comment on the previous line. The output is directly consumable
    by `--consts-file` so a typical workflow is:
        # First run: full env, capture failures
        ix check --path X.lean --fail-out fails.txt
        # Bisect: re-run only the failures with verbose output
        ix check --path X.lean --consts-file fails.txt --verbose
  - `--verbose`             (optional): one log line per constant
    (default is quiet/ephemeral, periodic done/total + ETA).

  The dep-closure helper is the same one used by `ix validate` and the
  `kernel-tutorial` test runner — see `Ix.Cli.ValidateCmd.collectDeps`.

  When any of `--ns`, `--consts`, `--consts-file` are set, the *whole*
  pipeline (compile → ingress → check) is restricted to the transitive
  closure of the matched seeds. This is the fast path for bisecting a
  specific failure out of a full-Mathlib run without re-paying the 30s
  compile + 130s ingress for the whole environment.
-/
module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.KernelCheck
public import Ix.Meta
public import Ix.Cli.ValidateCmd

public section

open System (FilePath)
open Ix.KernelCheck

namespace Ix.Cli.CheckCmd

/-- Combined seed selector: prefixes (`--ns`) ∪ exact names
    (`--consts`, `--consts-file`). All seeds are intersected with
    `env.constants` before the dep walk. -/
private structure SeedSpec where
  /-- `--ns` prefix list. Matches via `Lean.Name.isPrefixOf`. -/
  prefixes : List Lean.Name := []
  /-- `--consts` + `--consts-file` exact names. Matched against
      `env.constants` via structural equality. -/
  exacts : List Lean.Name := []

private def SeedSpec.isEmpty (s : SeedSpec) : Bool :=
  s.prefixes.isEmpty && s.exacts.isEmpty

/-- Read one constant name per line from `path`. Blank lines and lines
    starting with `#` (after trimming) are ignored. Trailing whitespace
    on each line is trimmed before `String.toName`. -/
private def readNamesFile (path : String) : IO (List Lean.Name) := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let names : List Lean.Name := lines.filterMap fun raw =>
    -- Strip CR (Windows line endings) and surrounding ASCII whitespace.
    let cs := raw.toList.dropWhile Char.isWhitespace
    let trimmed := String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse
    if trimmed.isEmpty || trimmed.startsWith "#" then none
    else some trimmed.toName
  pure names

/-- Build a `SeedSpec` from `--ns`, `--consts`, and `--consts-file`.
    Returns `none` if none of the flags were supplied (caller should
    check the full env). Returns `some spec` even when individual flags
    parsed to empty (with a warning) as long as at least one source
    contributed a seed; otherwise warns and falls back to full-env. -/
private def resolveSeedSpec (p : Cli.Parsed) : IO (Option SeedSpec) := do
  let nsFlag      := p.flag? "ns"
  let constsFlag  := p.flag? "consts"
  let fileFlag    := p.flag? "consts-file"
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

/-- Apply the seed spec (if any) and return both the seed names (the
    constants the user explicitly asked about) and the closed list of
    `(Name × ConstantInfo)` to ship to Rust.

    Without a filter: every constant in the env is a seed and gets shipped.
    With a filter: only constants matching one of the prefixes / exact names
    seed the walk, but the *transitive closure* is shipped so the kernel
    can resolve every reference. -/
private def selectConsts (leanEnv : Lean.Environment)
    (spec : Option SeedSpec)
    : IO (Array Lean.Name × List (Lean.Name × Lean.ConstantInfo)) := do
  match spec with
  | none =>
    let consts := leanEnv.constants.toList
    let names := consts.toArray.map (·.fst)
    pure (names, consts)
  | some s =>
    -- Verify exact-name seeds exist in the env; warn (don't fail) on misses
    -- so a typo or refactored name doesn't abort the run silently.
    let exactSet : Std.HashSet Lean.Name :=
      s.exacts.foldl (fun acc n => acc.insert n) (Std.HashSet.emptyWithCapacity s.exacts.length)
    let mut missing : Array Lean.Name := #[]
    for n in s.exacts do
      if !leanEnv.constants.contains n then
        missing := missing.push n
    if !missing.isEmpty then
      IO.println s!"[check] warning: {missing.size}/{s.exacts.length} exact name(s) not in env:"
      let shown := min 20 missing.size
      for n in missing[:shown] do
        IO.println s!"  - {n}"
      if missing.size > 20 then
        IO.println s!"  … ({missing.size - 20} more not shown)"
    let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
      if exactSet.contains n || s.prefixes.any (·.isPrefixOf n) then some n else none
    IO.println s!"[check] filter: {s.prefixes.length} prefix(es), {s.exacts.length} exact(s) → {seeds.length} seed constants"
    let closed := collectDeps leanEnv seeds
    IO.println s!"[check] filter: {closed.length} constants after transitive-dep closure"
    -- `seeds` (not the closure) are the names we actually assert on.
    -- Transitive deps still need to be in the shipped env so the kernel
    -- can resolve references; they're checked implicitly via the seeds
    -- that depend on them.
    pure (seeds.toArray, closed)

/-- Print up to `limit` failures, then a summary line if truncated. -/
private def reportFailures (failures : Array (Lean.Name × String))
    (limit : Nat := 30) : IO Unit := do
  if failures.isEmpty then return
  IO.println s!"[check] {failures.size} failure(s):"
  let shown := min limit failures.size
  for (name, msg) in failures[:shown] do
    IO.println s!"  ✗ {name}: {msg}"
  if failures.size > limit then
    IO.println s!"  … ({failures.size - limit} more failures suppressed; raise the printed limit if needed)"

/-- Render the error message safely as a single-line `#`-comment.
    Newlines (kernel diagnostics often have them) get joined with ` ⏎ `
    so each entry stays one line; this keeps `readNamesFile`'s
    "preceding `#` line is a comment" parser happy when the file is fed
    back through `--consts-file`. -/
private def commentLine (msg : String) : String :=
  let oneLine := msg.replace "\n" " ⏎ "
  s!"# {oneLine}"

/-- Write the failure list to `path` in a format directly consumable by
    `--consts-file`. Layout:
      # header block (source path, seed count, failure count)
      <blank line>
      # <error message for failure 1>
      <name 1>
      <blank line>
      # <error message for failure 2>
      <name 2>
      …
    Always overwrites; always writes (even on zero failures, so callers
    have a deterministic "no-news-is-good-news" artifact). -/
private def writeFailuresFile
    (path : String)
    (sourcePath : String)
    (seedCount : Nat)
    (failures : Array (Lean.Name × String))
    : IO Unit := do
  let mut buf : String :=
    "# ix check failures — feed this file back via `--consts-file`\n"
    ++ s!"# source: {sourcePath}\n"
    ++ s!"# seeds: {seedCount}\n"
    ++ s!"# failures: {failures.size}\n"
    ++ "\n"
  for (name, msg) in failures do
    buf := buf ++ commentLine msg ++ "\n" ++ s!"{name}\n\n"
  IO.FS.writeFile path buf
  IO.println s!"[check] wrote {failures.size} failure(s) to {path}"

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String
  let verbose := p.flag? "verbose" |>.isSome

  -- `buildFile` also runs `lake exe cache get` if the target depends on
  -- Mathlib, so a fresh checkout works without a prior `lake build`.
  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  let totalConsts := leanEnv.constants.toList.length
  IO.println s!"Running Ix kernel check on {pathStr}"
  IO.println s!"Total constants in env: {totalConsts}"

  let spec ← resolveSeedSpec p
  let (seedNames, allConsts) ← selectConsts leanEnv spec

  IO.println s!"[check] checking {seedNames.size} seed constant(s) against {allConsts.length} env constants"

  -- Every checked constant is expected to typecheck — `expectPass` is just
  -- a Rust-side progress-log hint (see `src/ffi/kernel.rs::ErrKind`).
  -- Defaulting to all-true keeps the `[ok]` / `[FAIL]` lines consistent.
  let expectPass : Array Bool := Array.replicate seedNames.size true

  let start ← IO.monoMsNow
  -- `verbose=false` (= `quiet=true` on the FFI side) is the default
  -- because full-Mathlib runs ship tens of thousands of constants and
  -- per-constant logs swamp the terminal. `--verbose` flips back to
  -- per-constant lines for small batches.
  let results ← rsCheckConstsFFI allConsts seedNames expectPass (!verbose)
  let elapsed := (← IO.monoMsNow) - start

  let mut passed := 0
  let mut failures : Array (Lean.Name × String) := #[]
  for i in [:seedNames.size] do
    match results[i]! with
    | none => passed := passed + 1
    | some err =>
      failures := failures.push (seedNames[i]!, err.message)

  IO.println s!"[check] checked {seedNames.size} constants in {elapsed.formatMs}"
  IO.println s!"[check] {passed}/{seedNames.size} passed"
  reportFailures failures

  -- Persist failures for the bisect-loop workflow described in the
  -- module docstring. Always written when `--fail-out` is set, even on
  -- zero failures, so an automation can `test -s fails.txt` for a clean
  -- pass/fail signal.
  if let some flag := p.flag? "fail-out" then
    let outPath := flag.as! String
    writeFailuresFile outPath pathStr seedNames.size failures

  -- Machine-readable line for CI tracking, matches `ix compile`'s shape.
  IO.println s!"##check## {elapsed} {passed} {failures.size} {seedNames.size}"

  return if failures.isEmpty then 0 else 1

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck a Lean file's environment through the Ix Rust kernel"

  FLAGS:
    path        : String; "Path to file whose env should be typechecked"
    ns          : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are asserted; transitive deps are pulled in so the kernel sees a closed env."
    consts        : String; "Comma-separated EXACT constant names to seed (e.g. 'Aesop.GoalUnsafe.rec_6,IntermediateField.LinearDisjoint.trace_algebraMap'). Transitive deps pulled in. Combine with --ns for a union."
    "consts-file" : String; "Path to a file with one constant name per line. '#' comments and blank lines ignored. Useful for long _private.Mathlib.… names pasted from a failing run."
    "fail-out"    : String; "Write all failing constant names to this path (one per line, error message as preceding '#' comment). Output is directly consumable by --consts-file for a bisect-loop workflow."
    verbose;                "Log every constant on its own line (default: quiet ephemeral progress)"
]

end
