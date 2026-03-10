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
]

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

      -- Phase 1: Lean kernel
      IO.println s!"\n=== Lean Kernel ==="
      for name in problematicNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do IO.println s!"  ✗ {name}: not found in named map"; continue
        let addr := cNamed.addr
        IO.println s!"  checking {name} ..."
        (← IO.getStdout).flush
        let leanStart ← IO.monoMsNow
        match Ix.Kernel.typecheckConstWithStats kenv prims addr quotInit (trace := true) with
        | .ok st =>
          let ms := (← IO.monoMsNow) - leanStart
          IO.println s!"  ✓ {name} ({ms.formatMs})"
          IO.println s!"    hb={st.heartbeats} infer={st.inferCalls} eval={st.evalCalls} deq={st.isDefEqCalls}"
          IO.println s!"    thunks={st.thunkCount} forces={st.thunkForces} hits={st.thunkHits} cache={st.cacheHits}"
          IO.println s!"    deltaSteps={st.deltaSteps} nativeReduces={st.nativeReduces} whnfMisses={st.whnfCacheMisses} proofIrrel={st.proofIrrelHits}"
        | .error e =>
          let ms := (← IO.monoMsNow) - leanStart
          IO.println s!"  ✗ {name} ({ms.formatMs}): {e}"

      -- Phase 2: Rust kernel
      IO.println s!"\n=== Rust Kernel ==="
      let rustStart ← IO.monoMsNow
      let results ← Ix.Kernel.rsCheckConsts leanEnv problematicNames
      let rustMs := (← IO.monoMsNow) - rustStart
      for (name, result) in results do
        match result with
        | none => IO.println s!"  ✓ {name} ({rustMs.formatMs})"
        | some err => IO.println s!"  ✗ {name} ({rustMs.formatMs}): {repr err}"

      return (true, none)
  ) .done

def suite : List TestSeq := [testProblematic]

end Tests.Ix.RustKernelProblematic
