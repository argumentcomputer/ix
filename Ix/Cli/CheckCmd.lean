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
  - `--verbose`             (optional): one log line per constant
    (default is quiet/ephemeral, periodic done/total + ETA).

  The dep-closure helper is the same one used by `ix validate` and the
  `kernel-tutorial` test runner — see `Ix.Cli.ValidateCmd.collectDeps`.
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

/-- Interpret the `--ns` flag. Returns `none` if the user didn't pass it
    (caller should check the full env), otherwise returns the parsed
    prefix list. Empty / all-whitespace inputs are rejected with a
    warning so we don't silently fall back to "check everything". -/
private def resolveNamespaceFilter (p : Cli.Parsed)
    : IO (Option (List Lean.Name)) := do
  match p.flag? "ns" with
  | none => pure none
  | some flag =>
    let raw := flag.as! String
    let prefixes := parsePrefixes raw
    if prefixes.isEmpty then
      IO.println s!"[check] warning: --ns '{raw}' parsed to empty list; checking full env"
      pure none
    else
      pure (some prefixes)

/-- Apply the `--ns` filter (if any) and return both the seed names (the
    constants the user explicitly asked about) and the closed list of
    `(Name × ConstantInfo)` to ship to Rust.

    Without a filter: every constant in the env is a seed and gets shipped.
    With a filter: only constants matching one of the prefixes seed the
    walk, but the *transitive closure* is shipped so the kernel can resolve
    every reference. -/
private def selectConsts (leanEnv : Lean.Environment)
    (filter : Option (List Lean.Name))
    : IO (Array Lean.Name × List (Lean.Name × Lean.ConstantInfo)) := do
  match filter with
  | none =>
    let consts := leanEnv.constants.toList
    let names := consts.toArray.map (·.fst)
    pure (names, consts)
  | some prefixes =>
    let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
      if prefixes.any (·.isPrefixOf n) then some n else none
    IO.println s!"[check] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
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

  let filter ← resolveNamespaceFilter p
  let (seedNames, allConsts) ← selectConsts leanEnv filter

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

  -- Machine-readable line for CI tracking, matches `ix compile`'s shape.
  IO.println s!"##check## {elapsed} {passed} {failures.size} {seedNames.size}"

  return if failures.isEmpty then 0 else 1

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck a Lean file's environment through the Ix Rust kernel"

  FLAGS:
    path    : String; "Path to file whose env should be typechecked"
    ns      : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are asserted; transitive deps are pulled in so the kernel sees a closed env."
    verbose;          "Log every constant on its own line (default: quiet ephemeral progress)"
]

end
