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

    IO.println s!"[check-env] Environment has {allNames.size} constants"

    let start ← IO.monoMsNow
    -- Full-env runs ship tens of thousands of constants: `quiet=true`
    -- keeps the console usable by rewriting the current-constant label
    -- in place and only persisting slow (>=1s) / failing / not-found
    -- entries. Any genuinely pathological constant shows up in the log.
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
  -- =========================================================================
  -- Category A: `_sizeOf_N` with nested-aux motive/minor ordering mismatch.
  --
  -- Source `.rec` has motives in Lean's internal nested-aux expansion order;
  -- our canonical `.rec` emits nested aux motives in `expand_nested_block`
  -- order. When the two orderings diverge within the nested region, surgery
  -- permutes the user-type motives correctly but leaves a residual
  -- mismatch across the nested slots. See grouping in
  -- `plans/kernel-check-env.md` (category A).
  -- =========================================================================
  --
  -- LCNF [Alt, FunDecl, Cases, Code] (+ nested aux) — original probe.
  -- Alt/Cases motive swap at sizeOf-call-sites; still failing under nested
  -- aux ordering divergence.
  `Lean.Compiler.LCNF.Alt._sizeOf_4,
  `Lean.Compiler.LCNF.Alt._sizeOf_6,
  --
  -- Cutsat EqCnstr block (6 failures) — nested Array (Prod Expr (Prod Int
  -- EqCnstr)) motive landing in Option DvdCnstr motive slot.
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_1,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_2,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_3,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_5,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_11,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_12,
  --
  -- Linear EqCnstr block — DiseqCnstr minor vs dependent UnsatProof-indexed
  -- motive. Different flavor of the same nested-region mis-ordering.
  `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_3,
  `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_7,

  -- =========================================================================
  -- Category B: regenerated `.rec_N` (nested auxiliary recursor) fails its
  -- own `check_recursor: type mismatch`. Our regenerator produces a type
  -- that doesn't match its rules. Same nested-aux-ordering root cause as
  -- A, surfacing at the recursor-decl level rather than a call site.
  -- =========================================================================
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstr.rec_4,
  `Lean.Doc.Block.rec_2,
  `Lean.Doc.Block.rec_5,
  `Lean.Doc.Block.rec_6,

  -- =========================================================================
  -- Category C: `.sizeOf_spec` and related theorems with `declaration type
  -- mismatch`. The theorem's body (a recursor-based equational proof) no
  -- longer reduces to the declared type after canonicalization. Downstream
  -- of A/B — expect these to clear once A/B are fixed.
  -- =========================================================================
  `Lean.Compiler.LCNF.Alt.alt.sizeOf_spec,
  `Lean.Meta.Grind.Arith.Cutsat.EqCnstrProof.pow.sizeOf_spec,
  `Lean.Meta.Grind.Arith.Linear.IneqCnstrProof.subst.sizeOf_spec,
  `accRecNoEta,
  `String.endPos_empty,

  -- =========================================================================
  -- Category D: `max recursion depth exceeded`. Unclear whether this is
  -- a whnf/def_eq loop, missing reduction rule, or an actual deep term.
  -- Some are `._sparseCasesOn_N` which fail at shallow depth (likely
  -- related to the sparseCasesOn not being regenerated — category I in
  -- the task list).
  -- =========================================================================
  -- depth=2001 — extreme; likely a genuine runaway.
  `Char.succ?_eq,
  -- depth=19
  `Std.IterM.stepAsHetT_filterMapWithPostcondition,
  -- depth=44 in 52s — slow runaway.
  `Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go._unary.eq_def,
  -- `._sparseCasesOn_N` failures at depth=3 — fast; probably the
  -- `_sparseCasesOn` aux isn't decompiling / regenerating correctly.
  Lean.mkPrivateNameCore `Lean.Server.FileWorker.WidgetRequests
    `Lean.Widget.makePopup._sparseCasesOn_3,
  Lean.mkPrivateNameCore `Lean.Server.References
    `Lean.Server.identOf._sparseCasesOn_4,
  Lean.mkPrivateNameCore `Lean.Server.InfoUtils
    `Lean.Elab.Info.type?._sparseCasesOn_1,

  -- =========================================================================
  -- Category E: `Lean.reduceBool` / `_nativeDecide_` proofs. Our kernel
  -- doesn't execute `Lean.reduceBool` as a native reducer, so proofs that
  -- rely on `reduceBool X = true` computing don't check.
  -- =========================================================================
  Lean.mkPrivateNameCore `Blake3
    `Blake3.HasherOps.hash._proof_1,
  Lean.mkPrivateNameCore `Ix.CanonM
    `Ix.CanonM.internDataValue._proof_1,

  -- =========================================================================
  -- Category F: LCNF Alt↔Cases mutual-member swap at user-code call sites.
  -- Same root as A, user-code side.
  -- =========================================================================
  Lean.mkPrivateNameCore `Lean.Compiler.LCNF.Basic
    `Lean.Compiler.LCNF.Decl.isCasesOnParam?.go,
  -- eqAlt.sparseCasesOn (LCNF private) — also from same block.
  Lean.mkPrivateNameCore `Lean.Compiler.LCNF.Basic
    `Lean.Compiler.LCNF.eqAlt._sparseCasesOn_1,

  -- =========================================================================
  -- Category G: LRAT proof auto-generated by the `match` elaborator.
  -- Huge `Prod.fst/snd` towers over `confirmRupHint.match_*`. Likely a
  -- match-eliminator vs aux issue, but the trace is too big to read
  -- directly — treat as a stress-test for whatever we fix in A/B/F.
  -- =========================================================================
  Lean.mkPrivateNameCore `Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
    `Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.derivedLitsInvariant_confirmRupHint._proof_1_18,
  Lean.mkPrivateNameCore `Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
    `Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.derivedLitsInvariant_confirmRupHint._proof_1_26,
  Lean.mkPrivateNameCore `Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult
    `Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.derivedLitsInvariant_confirmRupHint._proof_1_30,

  -- =========================================================================
  -- Category H: `String.Legacy.back ""` not reducing to `Char.ofNat 65`.
  -- Orthogonal to surgery; needs a String primitive reduction hook.
  -- =========================================================================
  `String.back_eq,

  -- =========================================================================
  -- Category I: adversarial test that *should* fail. Verify the error
  -- message matches expectation (universe param count) — if it does, this
  -- is NOT a bug. Keep for regression coverage of the failure path.
  -- =========================================================================
  `adv_constlevels_too_few,
]

/-- Focus-mode helper: typecheck each constant in `names` through the
    same Rust FFI pipeline as `testRustCheckEnv`, but restricted to a
    small list. Compile + ingress still pays ~20s (full env), but the
    check loop is short. Default `names` = `focusConsts`. -/
def testRustCheckConsts (names : Array Lean.Name := focusConsts) : TestSeq :=
  .individualIO s!"kernel check {names.size} focus consts" none (do
    let leanEnv ← get_env!
    let allConsts := leanEnv.constants.toList
    let expectPass : Array Bool := Array.replicate names.size true
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
