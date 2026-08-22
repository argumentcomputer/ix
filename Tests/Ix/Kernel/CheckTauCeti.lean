/-
  TauCeti-corpus focus constants for the Rust kernel.

  The TauCeti analogue of `Tests.Ix.Kernel.CheckEnv.focusConsts`: known
  failing / slow constants from full `ix check-rs tauceti.ixe` runs, kept
  here for fast reproduction without paying for the ~557k-constant env
  pass. Unlike `CheckEnv`'s list, these names do not exist in this test
  binary's own Lean environment (TauCeti builds against Mathlib in the
  `Benchmarks/Compile` workspace), so instead of `get_env!` the suite
  checks them through the serialized-env pipeline: `rsCheckIxonFFI` on
  `tauceti.ixe` with the focus names as exact seeds. That is the same
  subject-only seeded meta check as

    ix check-rs tauceti.ixe --consts <name1,name2,…>

  (deps lazily ingressed and trusted, only the seeds re-checked), so a
  single constant can also be cherry-picked straight from the CLI, e.g.
  with `IX_MAX_REC_FUEL=<n>` when bisecting a fuel exhaustion.

  Requires `tauceti.ixe` at the repo root (gitignored, ~2.8 GB):
  `ix compile Benchmarks/Compile/TauCeti.lean` after `lake build ix`,
  with the `Benchmarks/Compile` workspace fetched at its pinned rev.

  Run with: `lake test -- kernel-check-tauceti --ignored`
-/
import Ix.KernelCheck
import LSpec

open LSpec
open Ix.KernelCheck (CheckError rsCheckIxonFFI)

namespace Tests.Ix.Kernel.CheckTauCeti

/-- Repo-root serialized TauCeti env (see the module docstring). -/
def ixePath : System.FilePath := "tauceti.ixe"

/-- Known failing / slow constants from a full `ix check-rs tauceti.ixe`
    run. Edit when bisecting a regression; grouped by root cause in order
    of discovery. Timings below are from the 2026-08-22 full-env run
    (10M-fuel default, `MAX_REC_FUEL` in `crates/kernel/src/tc.rs`). -/
def focusConsts : Array Lean.Name := #[
  -- 2026-08-22: recursive fuel exhausted (FAIL at ~800s/838s in the
  -- full-env sweep, def-eq peak depth 47/50). Not divergence: both pass
  -- with `IX_MAX_REC_FUEL=20000000` (_apply ok 312s isolated at 50M,
  -- 483s at 20M; _symm_apply ok 949s at 20M), so the true cost sits in
  -- (10M, 20M] and the default 10M budget is what's short. Both theorems
  -- embed a `have … := rfl` equating `chebyshevWeightL2Isometry 𝕜 f`
  -- (resp. `.symm g`) with its unfolding through
  -- `LinearIsometryEquiv.trans`/`.symm`; the def-eq grinds through the
  -- Mathlib `Lp` instance tower, and `castLpₗᵢ` is an `Eq.rec` in Type
  -- position over a PROPOSITIONAL measure equality
  -- (`chebyshevMeasureT_eq_withDensity`, proved by measure ext), so
  -- every whnf of the stuck cast retries K-like reduction, whose
  -- `measureT ≟ withDensity …` def-eq must exhaust unfoldings and fail.
  -- Optimization work items: plans/kernel-rec-fuel.md.
  `TauCeti.chebyshevWeightL2Isometry_apply,
  `TauCeti.chebyshevWeightL2Isometry_symm_apply,

  -- 2026-08-22: pass, but slow — same bundled-morphism def-eq shape,
  -- inside the fuel budget. Kept as canaries: a kernel regression that
  -- deepens unfolding shows up here as slow→FAIL before anything else.
  -- isLocallyConstant_windingNumber: ok 239.0s, depth=62 (53s isolated).
  -- fullyBlockedCyclesSwapMarkingsEquiv_apply: ok 434.6s, depth=72;
  -- _symm_apply: ok 400.7s, depth=72. The swap-equiv pair is the same
  -- Eq-transport shape in miniature: `LinearEquiv.ofEq` over a
  -- propositional submodule equality, unfolded by `simp`.
  `TauCeti.Contour.Cycle.isLocallyConstant_windingNumber,
  `TauCeti.GridDiagram.fullyBlockedCyclesSwapMarkingsEquiv_apply,
  `TauCeti.GridDiagram.fullyBlockedCyclesSwapMarkingsEquiv_symm_apply
]

/-- Every focus constant is a legitimate TauCeti theorem, so the kernel
    is expected to accept all of them; the suite stays red until the
    fuel-exhaustion family above is fixed (same convention as
    `CheckEnv.expectedPass`). -/
def expectedPass (_name : Lean.Name) : Bool := true

/-- Same narrowing hook as `CheckEnv.filterFocusConsts`: restrict the
    batch to names containing `IX_KERNEL_FOCUS_CONST`. -/
private def filterFocusConsts (names : Array Lean.Name) : IO (Array Lean.Name) := do
  match (← IO.getEnv "IX_KERNEL_FOCUS_CONST") with
  | none => pure names
  | some filter =>
    let filtered := names.filter fun name => name.toString.contains filter
    IO.println s!"[check-tauceti] IX_KERNEL_FOCUS_CONST={filter} matched {filtered.size}/{names.size}"
    pure filtered

def testRustCheckTauCetiConsts (names : Array Lean.Name := focusConsts) : TestSeq :=
  .individualIO s!"kernel check {names.size} TauCeti focus consts" none (do
    unless (← ixePath.pathExists) do
      return (false, 0, names.size, some s!"{ixePath} missing — build it \
        with `ix compile Benchmarks/Compile/TauCeti.lean` (see module docstring)")
    let names ← filterFocusConsts names
    let expectPass : Array Bool := names.map expectedPass
    let start ← IO.monoMsNow
    -- Focus batches are intentionally tiny — keep verbose output so each
    -- targeted constant prints its elapsed time and depth inline. Exact
    -- seeds skip the env name preflight; a name missing from a stale
    -- `tauceti.ixe` comes back as an ordinary per-name kernel error
    -- (`missing Named entry`).
    let results ← rsCheckIxonFFI ixePath.toString names expectPass false ""
    let elapsed := (← IO.monoMsNow) - start

    let mut passed := 0
    let mut failures : Array (Lean.Name × String) := #[]
    -- Rust preserves input order, so `results[i]` pairs with `names[i]`.
    for i in [:names.size] do
      let shouldPass := expectedPass names[i]!
      match results[i]! with
      | none =>
        if shouldPass then
          passed := passed + 1
        else
          failures := failures.push (names[i]!, "unexpected pass")
      | some err =>
        let msg := match err with
          | .kernelException m => s!"kernel: {m}"
          | .compileError    m => s!"compile: {m}"
        if shouldPass then
          failures := failures.push (names[i]!, msg)
        else
          passed := passed + 1

    IO.println s!"[check-tauceti] {passed}/{names.size} passed in {elapsed}ms"
    if !failures.isEmpty then
      IO.println s!"[check-tauceti] {failures.size} failure(s):"
      for (name, msg) in failures do
        IO.println s!"  ✗ {name}: {msg}"

    let total := passed + failures.size
    if failures.isEmpty then
      return (true, passed, total, none)
    else
      return (false, passed, total,
        some s!"TauCeti focus check failed with {failures.size} failure(s)")
  ) .done

def suite : List TestSeq := [testRustCheckTauCetiConsts]

end Tests.Ix.Kernel.CheckTauCeti
