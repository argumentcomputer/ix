/-
  Scheduling independence of the parallel aux-aware compile driver
  (`Ix.CompileM.compileEnvParallelAuxWith`).

  The driver starts blocks ahead of their wave against a speculative
  state and accepts or recomputes their outcomes when the authoritative
  state reaches their wave, so its output must not depend on worker
  count, completion order or dispatch priority. This runner compiles the
  aux-gen fixture closure (the corpus `aux-gen-diff` checks against Rust)
  under the plain wave schedule and under speculative schedules with
  different worker counts, seeded priorities and seeded start delays
  (which force other completion orders), plus the verify mode that
  recomputes every speculative outcome and fails if validation accepted
  one that differs from its wave outcome. Every run must serialize to the
  same bytes and record the same per-block failures. A `rustRef` map with
  deliberately wrong addresses must abort every run with the same
  mismatch.

  Invoked via `lake test -- --ignored compile-schedule`.
-/
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.ValidateAux

namespace Tests.Ix.CompileSchedule

open Ix.CompileM

/-- Per-block failures in a canonical order. -/
private def ungroundedList (cenv : CompileEnv) : Array (String × String) :=
  (cenv.ungrounded.toArray.map fun (n, e) => (n.pretty, e)).qsort
    fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def run (env : Lean.Environment) : IO UInt32 := do
  let filtered := validateAuxClosure env
  let raw ← rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let condensed := raw.condensed.toCondensedBlocks
  IO.println s!"[compile-schedule] {filtered.length} constants, \
{condensed.blocks.size} blocks"
  let configs : List (String × AuxSchedConfig) := [
    ("waves, 32 workers", { speculate := false }),
    ("speculative, 32 workers", {}),
    ("speculative, 1 worker", { numWorkers := 1 }),
    ("speculative, 4 workers", { numWorkers := 4 }),
    ("speculative, verify, 8 workers", { numWorkers := 8, verify := true }),
    ("seed 1, delays up to 3ms, 8 workers",
      { numWorkers := 8, seed := 1, jitterMs := 3 }),
    ("seed 2, delays up to 7ms, 3 workers",
      { numWorkers := 3, seed := 2, jitterMs := 7 }),
    ("seed 3, immediate republication, 16 workers",
      { numWorkers := 16, seed := 3, publishMs := 0 })]
  let mut failures := 0
  let mut reference : Option (ByteArray × Array (String × String)) := none
  let mut refEnv : Option Ixon.Env := none
  for (label, cfg) in configs do
    let t0 ← IO.monoMsNow
    match ← compileEnvParallelAuxWith rawEnv condensed cfg with
    | .error e =>
      IO.println s!"[compile-schedule] {label}: ERROR {e}"
      failures := failures + 1
    | .ok (ixonEnv, _, cenv) =>
      match Ixon.serEnv ixonEnv with
      | .error e =>
        IO.println s!"[compile-schedule] {label}: serEnv failed: {e}"
        failures := failures + 1
      | .ok bytes =>
        let ms := (← IO.monoMsNow) - t0
        let ungrounded := ungroundedList cenv
        match reference with
        | none =>
          reference := some (bytes, ungrounded)
          refEnv := some ixonEnv
          IO.println s!"[compile-schedule] {label}: {bytes.size} bytes, \
{ungrounded.size} failures, {ms}ms (reference)"
        | some (refBytes, refUngrounded) =>
          if bytes == refBytes && ungrounded == refUngrounded then
            IO.println s!"[compile-schedule] {label}: identical, {ms}ms"
          else
            IO.println s!"[compile-schedule] {label}: DIFFERS (bytes \
{bytes.size} vs {refBytes.size}, failures {ungrounded.size} vs \
{refUngrounded.size})"
            failures := failures + 1
  -- Deterministic error reporting: wrong reference addresses for every
  -- 7th registered name must give the same first mismatch every time.
  if let some ixonEnv := refEnv then
    let names := (ixonEnv.named.toArray.map (·.1)).qsort (·.pretty < ·.pretty)
    let mut rustRef : Std.HashMap Ix.Name Address := {}
    for h : k in [:names.size] do
      let name := names[k]
      let addr := (ixonEnv.named.get? name).map (·.addr) |>.getD default
      rustRef := rustRef.insert name
        (if k % 7 == 3 then Address.blake3 name.pretty.toUTF8 else addr)
    let errConfigs : List (String × AuxSchedConfig) := [
      ("waves", { speculate := false }),
      ("speculative", {}),
      ("seed 4, delays up to 5ms, 6 workers",
        { numWorkers := 6, seed := 4, jitterMs := 5 })]
    let mut firstErr : Option String := none
    for (label, cfg) in errConfigs do
      match ← compileEnvParallelAuxWith rawEnv condensed cfg (rustRef := some rustRef) with
      | .ok _ =>
        IO.println s!"[compile-schedule] rustRef {label}: no mismatch reported"
        failures := failures + 1
      | .error e =>
        match firstErr with
        | none =>
          firstErr := some e
          IO.println s!"[compile-schedule] rustRef {label}: {e.take 160}"
        | some e₀ =>
          if e == e₀ then
            IO.println s!"[compile-schedule] rustRef {label}: same error"
          else
            IO.println s!"[compile-schedule] rustRef {label}: DIFFERENT error \
{e.take 160}"
            failures := failures + 1
  IO.println s!"[compile-schedule] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.CompileSchedule
