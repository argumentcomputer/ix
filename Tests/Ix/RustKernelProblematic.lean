/-
  Rust vs Lean Kernel comparison tests for problematic constants.
  Runs the same constants through both kernels with detailed stats
  to identify performance divergences.
-/
import Ix.Kernel
import Ix.Kernel.Convert
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec
open Tests.Ix.Kernel.Helpers (parseIxName)

namespace Tests.Ix.RustKernelProblematic

/-- Constants that are problematic for the Rust kernel. -/
def problematicNames : Array String := #[
  "_private.Std.Time.Format.Basic.«0».Std.Time.parseWith",
  "Batteries.BinaryHeap.heapifyDown._unsafe_rec",
  "UInt8.toUInt64_toUSize",
]

/-- Print detailed stats. -/
def printStats (st : Ix.Kernel.Stats) : IO Unit := do
  IO.println s!"    hb={st.heartbeats} infer={st.inferCalls} eval={st.evalCalls} deq={st.isDefEqCalls}"
  IO.println s!"    quick: true={st.quickTrue} false={st.quickFalse}  equiv={st.equivHits}  ptr_succ={st.ptrSuccessHits}  ptr_fail={st.ptrFailureHits}  proof_irrel={st.proofIrrelHits}"
  IO.println s!"    whnf: hit={st.whnfCacheHits} miss={st.whnfCacheMisses}  equiv={st.whnfEquivHits}  core_hit={st.whnfCoreCacheHits}  core_miss={st.whnfCoreCacheMisses}"
  IO.println s!"    delta: steps={st.deltaSteps} lazy_iters={st.lazyDeltaIters}  same_head: check={st.sameHeadChecks}  hit={st.sameHeadHits}"
  IO.println s!"    step10={st.step10Fires} step11={st.step11Fires}  native={st.nativeReduces}"
  IO.println s!"    thunks: count={st.thunkCount} forces={st.thunkForces} hits={st.thunkHits} cache={st.cacheHits}"

/-- Run problematic constants through both Lean and Rust kernels with stats. -/
def testProblematic : TestSeq :=
  .individualIO "rust-kernel-problematic comparison" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    IO.println s!"[rust-kernel-problematic] rsCompileEnv: {ixonEnv.consts.size} consts in {compileMs.formatMs}"

    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[rust-kernel-problematic] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      IO.println s!"[rust-kernel-problematic] convertEnv: {kenv.size} consts in {convertMs.formatMs}"

      -- Phase 1: Rust kernel (fast — gives us baseline stats)
      IO.println s!"\n=== Rust Kernel ==="
      let rustStart ← IO.monoMsNow
      let results ← Ix.Kernel.rsCheckConsts leanEnv problematicNames
      let rustMs := (← IO.monoMsNow) - rustStart
      for (name, result) in results do
        match result with
        | none => IO.println s!"  ✓ {name} ({rustMs.formatMs})"
        | some err => IO.println s!"  ✗ {name} ({rustMs.formatMs}): {repr err}"

      -- Phase 2: Lean kernel (low heartbeat limit to catch divergence early)
      IO.println s!"\n=== Lean Kernel ==="
      for name in problematicNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do IO.println s!"  ✗ {name}: not found in named map"; continue
        let addr := cNamed.addr
        IO.println s!"  checking {name} ..."
        (← IO.getStdout).flush
        let leanStart ← IO.monoMsNow
        let (errOpt, st) := Ix.Kernel.typecheckConstWithStatsAlways kenv prims addr quotInit
          (trace := false) (maxHeartbeats := 100_000)
        let ms := (← IO.monoMsNow) - leanStart
        match errOpt with
        | none => IO.println s!"  ✓ {name} ({ms.formatMs})"
        | some e => IO.println s!"  ✗ {name} ({ms.formatMs}): {e}"
        printStats st

      return (true, none)
  ) .done

def suite : List TestSeq := [testProblematic]

end Tests.Ix.RustKernelProblematic
