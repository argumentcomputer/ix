/-
  Lean kernel const-checking tests: typecheck specific constants
  through the Lean NbE kernel.
-/
import Ix.Kernel
import Ix.Kernel.Convert
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Helpers
import Tests.Ix.Kernel.Consts
import LSpec

open LSpec
open Tests.Ix.Kernel.Helpers (parseIxName)

namespace Tests.Ix.Kernel.ConstCheck

/-- Typecheck regression constants through the Lean kernel. -/
def testConsts : TestSeq :=
  .individualIO "kernel const checks" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    IO.println s!"[kernel-const] rsCompileEnv: {ixonEnv.consts.size} consts in {compileMs.formatMs}"

    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel-const] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      IO.println s!"[kernel-const] convertEnv: {kenv.size} consts in {convertMs.formatMs}"

      let constNames := Consts.regressionConsts
      let mut passed := 0
      let mut failures : Array String := #[]
      for name in constNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do failures := failures.push s!"{name}: not found"; continue
        let mid : Ix.Kernel.MetaId .meta := (ixName, cNamed.addr)
        IO.println s!"  checking {name} ..."
        (← IO.getStdout).flush
        let start ← IO.monoMsNow
        -- let trace := name.containsSubstr "heapifyDown"
        -- if trace then
        --   if let some ci := kenv.find? mid then
        --     IO.println s!"  [debug] {name} type:\n{ci.type.pp}"
        --     if let some val := ci.value? then
        --       IO.println s!"  [debug] {name} value:\n{val.pp}"
        let (err?, stats) := Ix.Kernel.typecheckConstWithStatsAlways kenv prims mid quotInit (trace := false)
        let ms := (← IO.monoMsNow) - start
        match err? with
        | none =>
          IO.println s!"  ✓ {name} ({ms.formatMs})"
          passed := passed + 1
        | some e =>
          IO.println s!"  ✗ {name} ({ms.formatMs}): {e}"
          failures := failures.push s!"{name}: {e}"
        if ms >= 10 then
          IO.println s!"  [lean-stats] {name}: hb={stats.heartbeats} infer={stats.inferCalls} eval={stats.evalCalls} deq={stats.isDefEqCalls} thunks={stats.thunkCount} forces={stats.forceCalls} hits={stats.thunkHits}"
          IO.println s!"  [lean-stats]   quick: true={stats.quickTrue} false={stats.quickFalse}  equiv={stats.equivHits}  ptr_succ={stats.ptrSuccessHits}  ptr_fail={stats.ptrFailureHits}  proofIrrel={stats.proofIrrelHits}"
          IO.println s!"  [lean-stats]   whnf: hit={stats.whnfCacheHits} miss={stats.whnfCacheMisses}  equiv={stats.whnfEquivHits}  core_hit={stats.whnfCoreCacheHits}  core_miss={stats.whnfCoreCacheMisses}"
          IO.println s!"  [lean-stats]   delta: steps={stats.deltaSteps}  lazy_iters={stats.lazyDeltaIters}  same_head: check={stats.sameHeadChecks}  hit={stats.sameHeadHits}"
          IO.println s!"  [lean-stats]   step10={stats.step10Fires}  step11={stats.step11Fires}  native={stats.nativeReduces}"
      IO.println s!"[kernel-const] {passed}/{constNames.size} passed"
      if failures.isEmpty then
        return (true, none)
      else
        return (false, some s!"{failures.size} failure(s)")
  ) .done

/-- Problematic constants: slow or hanging constants isolated for profiling. -/
def testConstsProblematic : TestSeq :=
  .individualIO "kernel problematic const checks" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    IO.println s!"[kernel-problematic] rsCompileEnv: {ixonEnv.consts.size} consts in {compileMs.formatMs}"

    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel-problematic] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      IO.println s!"[kernel-problematic] convertEnv: {kenv.size} consts in {convertMs.formatMs}"

      let constNames := Consts.problematicConsts
      let mut passed := 0
      let mut failures : Array String := #[]
      for name in constNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do failures := failures.push s!"{name}: not found"; continue
        let mid : Ix.Kernel.MetaId .meta := (ixName, cNamed.addr)
        IO.println s!"  checking {name} ..."
        (← IO.getStdout).flush
        let start ← IO.monoMsNow
        match Ix.Kernel.typecheckConst kenv prims mid quotInit (trace := true) (maxHeartbeats := 2_000_000) with
        | .ok () =>
          let ms := (← IO.monoMsNow) - start
          IO.println s!"  ✓ {name} ({ms.formatMs})"
          passed := passed + 1
        | .error e =>
          let ms := (← IO.monoMsNow) - start
          IO.println s!"  ✗ {name} ({ms.formatMs}): {e}"
          failures := failures.push s!"{name}: {e}"
      IO.println s!"[kernel-problematic] {passed}/{constNames.size} passed"
      if failures.isEmpty then
        return (true, none)
      else
        return (false, some s!"{failures.size} failure(s)")
  ) .done

def constSuite : List TestSeq := [testConsts]
def problematicSuite : List TestSeq := [testConstsProblematic]

end Tests.Ix.Kernel.ConstCheck
