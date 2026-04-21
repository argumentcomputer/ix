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
import Tests.Ix.Kernel.Tutorial
import LSpec

open LSpec
open Tests.Ix.Kernel.Tutorial (CheckError rsCheckConstsFFI)

namespace Tests.Ix.Kernel.CheckEnv

def testRustCheckEnv : TestSeq :=
  .individualIO "Rust kernel check_env" none (do
    let leanEnv ← get_env!
    let allConsts := leanEnv.constants.toList
    let allNames : Array String :=
      allConsts.toArray.map fun (name, _) => name.toString
    -- Every env constant is expected to typecheck; `expect_pass` is an
    -- FFI-side progress-log hint (see `src/ffi/kernel.rs:264, 326-335`),
    -- but all-true keeps the `[ok]` / `[FAIL]` log lines consistent.
    let expectPass : Array Bool := Array.replicate allNames.size true

    IO.println s!"[check-env] Environment has {allNames.size} constants"

    let start ← IO.monoMsNow
    let results ← rsCheckConstsFFI allConsts allNames expectPass
    let elapsed := (← IO.monoMsNow) - start

    let mut passed := 0
    let mut failures : Array (String × String) := #[]
    for (name, result) in results do
      match result with
      | none => passed := passed + 1
      | some err =>
        -- Unpack the `CheckError` ctor manually; `repr err` on multi-line
        -- kernel messages is seconds-slow per call (see the same comment
        -- in `Tutorial.lean:226`).
        let msg := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError    m => s!"compile: {m}"
        failures := failures.push (name, msg)

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
def focusConsts : Array String := #[
  -- Kernel typecheck failures (AppTypeMismatch / DeclTypeMismatch):
  "Int64.toInt_minValue",
  "_private.Batteries.Data.List.Lemmas.0.List.findIdxNth_cons._proof_1_6",
  "Int32.neg_eq_neg_one_mul",
  "_private.Init.Data.SInt.Lemmas.0.Int16.toInt32_ne_minValue._proof_1_2",
  "Int64.neg_nonpos_iff",
  "Int64.ofIntLE_bitVecToInt._proof_1",
  "_private.Batteries.Data.List.Lemmas.0.List.Nodup.idxOf_getElem._proof_1_14",
  -- Recursors that reach the kernel with compile-time rejections
  -- suppressed (good-path sanity check; currently `compile: original rec
  -- rejected` in kernel-check-env):
  "Lean.IR.IRType.rec",
  "Lean.Syntax.rec",
  "Lean.PrefixTreeNode.rec_2",
  "Lean.Lsp.DocumentSymbol.rec_4",
  "Lean.Widget.TaggedText.rec_2",
  "Lean.Doc.Inline.rec_1",
  "Lean.Server.Test.Runner.Client.HighlightedMsgEmbed.rec_2",
  "Lean.Widget.HighlightedMsgEmbed.rec_1",
  -- Known non-terminating typecheck (investigate WHNF / defeq loop):
  --"Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_le_size._unary"
]

/-- Focus-mode helper: typecheck each constant in `names` through the
    same Rust FFI pipeline as `testRustCheckEnv`, but restricted to a
    small list. Compile + ingress still pays ~20s (full env), but the
    check loop is short. Default `names` = `focusConsts`. -/
def testRustCheckConsts (names : Array String := focusConsts) : TestSeq :=
  .individualIO s!"kernel check {names.size} focus consts" none (do
    let leanEnv ← get_env!
    let allConsts := leanEnv.constants.toList
    let expectPass : Array Bool := Array.replicate names.size true
    let start ← IO.monoMsNow
    let results ← rsCheckConstsFFI allConsts names expectPass
    let elapsed := (← IO.monoMsNow) - start

    let mut passed := 0
    let mut failures : Array (String × String) := #[]
    -- Build a name → result map so we can report names in the same order
    -- as `focusConsts`, regardless of FFI output ordering.
    let mut resultMap : Std.HashMap String (Option CheckError) :=
      Std.HashMap.emptyWithCapacity results.size
    for (name, result) in results do
      resultMap := resultMap.insert name result
    for name in names do
      match resultMap.get? name with
      | some none => passed := passed + 1
      | some (some err) =>
        let msg := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError    m => s!"compile: {m}"
        failures := failures.push (name, msg)
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
