/-
  Full-environment typechecking test for the Rust kernel.

  Mirrors ix_old's `Tests/Ix/Kernel/CheckEnv.lean::testRustCheckEnv`:
  capture the `get_env!` environment, ship every constant through the Rust
  FFI pipeline (Lean env → Ixon compile → kernel ingress → typecheck), pass
  iff every constant typechecks.

  Reuses `CheckError` and `rsCheckConstsFFI` from `Tests.Ix.Kernel.Tutorial`
  so the FFI ABI (ctor tags 0 = kernelException, 1 = compileError) has a
  single Lean-side source of truth.

  Run with: `lake test -- kernel-check-env --ignored`
-/
import Ix.Common
import Ix.Meta
import Ix.KernelCheck
import Tests.Ix.Kernel.Tutorial
import Tests.Ix.Kernel.TutorialMeta
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckConstsFFI)
open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.CheckEnv

private def tutorialDefsNamespace : Lean.Name :=
  `Tests.Ix.Kernel.TutorialDefs

private def isFromTutorialDefsModule (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some modIdx =>
    match env.header.moduleNames[modIdx]? with
    | some modName => modName == tutorialDefsNamespace
    | none => false
  | none => false

private def tutorialFixtureNames (env : Lean.Environment) : Std.HashSet Lean.Name :=
  Id.run do
    let mut names : Std.HashSet Lean.Name := Std.HashSet.emptyWithCapacity 256
    for tc in getTestCases env do
      for n in tc.decls do
        if isFromTutorialDefsModule env n then
          names := names.insert n
    for ci in getRawConsts env do
      if isFromTutorialDefsModule env ci.name then
        names := names.insert ci.name
    return names

private def isTutorialDefsName (fixtures : Std.HashSet Lean.Name) (name : Lean.Name) : Bool :=
  tutorialDefsNamespace.isPrefixOf name
    || name.toString.contains "_private.Tests.Ix.Kernel.TutorialDefs."
    || fixtures.contains name

def testRustCheckEnv : TestSeq :=
  .individualIO "Rust kernel check_env" none (do
    let leanEnv ← get_env!
    let envConsts := leanEnv.constants.toList
    let tutorialFixtures := tutorialFixtureNames leanEnv
    let allConsts := envConsts.filter fun (name, _) =>
      !isTutorialDefsName tutorialFixtures name
    -- Pass `Lean.Name` structurally across the FFI; Rust's
    -- `decode_name_array` reconstructs the same `Name` value (same
    -- component strings, same content hash) that the kernel uses
    -- internally, so name lookup is an exact structural match.
    let allNames : Array Lean.Name :=
      allConsts.toArray.map fun (name, _) => name
    -- Every env constant is expected to typecheck; `expect_pass` is an
    -- FFI-side progress-log hint (see `src/ffi/kernel.rs`'s `ErrKind`
    -- and `check_consts_loop`), but all-true keeps the `[ok]` / `[FAIL]`
    -- log lines consistent.
    let expectPass : Array Bool := Array.replicate allNames.size true
    let skippedCount := envConsts.length - allConsts.length

    IO.println s!"[check-env] Environment has {envConsts.length} constants; checking {allNames.size} (skipping {skippedCount} TutorialDefs constants)"

    let start ← IO.monoMsNow
    -- Full-env runs ship tens of thousands of constants: `quiet=true`
    -- keeps the console usable by rewriting the current-constant label
    -- in place and only persisting slow (>=7s by default) / failing /
    -- not-found entries. Parallel quiet mode also prints periodic
    -- done/total, rate, ETA, and oldest in-flight constants.
    --
    -- Rust returns results in the same order as `allNames`, so
    -- `results[i]` pairs with `allNames[i]`.
    let results ← rsCheckConstsFFI allConsts allNames expectPass true
    let elapsed := (← IO.monoMsNow) - start

    let mut passed := 0
    let mut failures : Array (Lean.Name × String) := #[]
    for i in [:allNames.size] do
      match results[i]! with
      | none => passed := passed + 1
      | some err =>
        -- Unpack the `CheckError` ctor manually; `repr err` on multi-line
        -- kernel messages is seconds-slow per call (see the same comment
        -- in `Tutorial.lean`).
        let msg := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError    m => s!"compile: {m}"
        failures := failures.push (allNames[i]!, msg)

    IO.println s!"[check-env] Checked {allNames.size} constants in {elapsed}ms"
    IO.println s!"[check-env] {passed}/{allNames.size} passed"

    if !failures.isEmpty then
      IO.println s!"[check-env] {failures.size} failure(s):"
      for (name, err) in failures[:min 30 failures.size] do
        IO.println s!"  ✗ {name}: {err}"

    let total := passed + failures.size
    if failures.isEmpty then
      return (true, passed, total, none)
    else
      return (false, passed, total,
        some s!"Kernel check failed with {failures.size} failure(s)")
  ) .done

/-- Known failing / hanging constants from a `testRustCheckEnv` run.
    Used by `testRustCheckConsts` for fast reproduction without paying for
    the full env pass. Edit when bisecting a regression; grouped by root
    cause in order of discovery.

    The *Rust side* prints `[i/N] name ... ok/FAIL` per constant as the
    check proceeds, so a hang is recognisable by a missing terminator
    after `[i/N] name ...` — look for the last printed name. -/
def focusConsts : Array Lean.Name := #[
  -- Current full-env residue from 2026-04-26 after the LRAT/SInt fixes.
  `System.Platform.numBits_eq,
  `BitVec.umulOverflow_eq,
  `Char.ofOrdinal_ordinal,
  Lean.mkPrivateNameCore `Init.Data.Char.Ordinal
    `Char.ofOrdinal_ordinal._proof_1_4,
  `String.toByteArray_empty,
  -- Nested auxiliary recursor canonical-order mismatch.
  `Lean.Json.rec_1,
  -- Extended-structure projection regression coverage. These exercise
  -- chained projections generated for `structure HeaderParsedSnapshot extends
  -- Snapshot`.
  `Lean.Language.Lean.HeaderParsedSnapshot.stx,
  `Lean.Language.Lean.HeaderParsedSnapshot.result?,
  `Lean.Language.Lean.HeaderParsedSnapshot.metaSnap,
  `Lean.Language.Lean.HeaderParsedSnapshot.toSnapshot,
  `Lean.Language.Lean.HeaderParsedSnapshot.ictx
]

def expectedPass (_name : Lean.Name) : Bool := true

/-- Focus-mode helper: typecheck each constant in `names` through the
    same Rust FFI pipeline as `testRustCheckEnv`, but restricted to a
    small list. Compile + ingress still pays ~20s (full env), but the
    check loop is short. Default `names` = `focusConsts`. -/
private def filterFocusConsts (names : Array Lean.Name) : IO (Array Lean.Name) := do
  match (← IO.getEnv "IX_KERNEL_FOCUS_CONST") with
  | none => pure names
  | some filter =>
    let filtered := names.filter fun name => name.toString.contains filter
    IO.println s!"[check-focus] IX_KERNEL_FOCUS_CONST={filter} matched {filtered.size}/{names.size}"
    pure filtered

def testRustCheckConsts (names : Array Lean.Name := focusConsts) : TestSeq :=
  .individualIO s!"kernel check {names.size} focus consts" none (do
    let leanEnv ← get_env!
    let names ← filterFocusConsts names
    let tutorialFixtures := tutorialFixtureNames leanEnv
    let allConsts := leanEnv.constants.toList.filter fun (name, _) =>
      !isTutorialDefsName tutorialFixtures name
    let expectPass : Array Bool := names.map expectedPass
    let start ← IO.monoMsNow
    -- Focus batches are intentionally tiny — keep verbose output so each
    -- targeted constant prints its elapsed time and depth inline.
    let results ← rsCheckConstsFFI allConsts names expectPass false
    let elapsed := (← IO.monoMsNow) - start

    let mut passed := 0
    let mut failures : Array (Lean.Name × String) := #[]
    -- Rust preserves input order, so `results[i]` lines up with `names[i]`.
    -- We still build a `Name → result` map so we can report names in the
    -- same order as `focusConsts` and surface any gap (shouldn't happen
    -- with order-preserving results, but kept defensively).
    let mut resultMap : Std.HashMap Lean.Name (Option CheckError) :=
      Std.HashMap.emptyWithCapacity results.size
    for i in [:names.size] do
      resultMap := resultMap.insert names[i]! results[i]!
    for name in names do
      let shouldPass := expectedPass name
      match resultMap.get? name with
      | some none =>
        if shouldPass then
          passed := passed + 1
        else
          failures := failures.push (name, "unexpected pass")
      | some (some err) =>
        let msg := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError    m => s!"compile: {m}"
        if shouldPass then
          failures := failures.push (name, msg)
        else
          passed := passed + 1
      | none =>
        failures := failures.push (name, "not reported by FFI")

    IO.println s!"[check-focus] {passed}/{names.size} passed in {elapsed}ms"
    if !failures.isEmpty then
      IO.println s!"[check-focus] {failures.size} failure(s):"
      for (name, msg) in failures do
        IO.println s!"  ✗ {name}: {msg}"

    let total := passed + failures.size
    if failures.isEmpty then
      return (true, passed, total, none)
    else
      return (false, passed, total,
        some s!"Focus check failed with {failures.size} failure(s)")
  ) .done

def suite : List TestSeq := [testRustCheckEnv]
def constSuite : List TestSeq := [testRustCheckConsts]

end Tests.Ix.Kernel.CheckEnv
