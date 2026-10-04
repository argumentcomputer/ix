/-
  compile-schedule-identity: the Lean compiler's output does not depend on
  the schedule (Phase A §3.5 and §5.5; design document §6.2; the A7 gate).

  Over the twins closure (`Tests.Ix.Compile.Twins`, every family) and the
  aux fixture corpus (`validateAuxClosure`: `Tests.Ix.Compile.Mutual`,
  `Canonicity`, `LevelSpellings`, the IxVM and `Test.Ix.Fixtures`
  families), compile, once with the Pass 3 switch off and once with it on
  (`IX_PASS3=images`, passed explicitly to every driver so the environment
  variable does not matter), with

  - the sequential driver `Ix.CompileM.compileEnvAux` (the fold that §6.2
    makes the definition: least canonical key first, A7 D9), on the
    canonical environment and condensation of `rsCompilePhasesOf`;
  - the wave driver `compileEnvParallelAux` on the same input at 1, 2, 4,
    16 and 32 workers;
  - the whole `ix compile-lean` pipeline (`compileLeanInput`, its own canon
    and condensation, so other block representatives) at 1, 4 and 16
    workers;

  and require every serialized environment of one mode to be
  byte-identical. A difference is reported with the constant and its two
  addresses; it is a finding for A7, not something this suite repairs.
  There is no speculative driver in the Lean compiler (the optimisation
  branch's was not taken, owner 2026-10-03), so it has no leg here.

  Under every schedule the block failures must be exactly the expected
  refusals of the closure (`NonCanonical.expectedRefusals`), each with its
  message: a refusal that appears or disappears under one schedule fails
  the suite, and so does any difference in the (name, message) list
  between the schedules of one mode.

  Run with: `lake test -- --ignored compile-schedule-identity`.
-/
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux

open Lean

namespace Tests.Ix.Compile.ScheduleIdentity

/-- The per-name differences of two environments: (name, address in `a`,
    address in `b`), names missing on one side included. -/
def namedDiffs (a b : Ixon.Env) : Array (String × String × String) := Id.run do
  let mut out := #[]
  for (n, x) in a.named do
    match b.named.get? n with
    | some y => if x.addr != y.addr then out := out.push (toString n, toString x.addr, toString y.addr)
    | none => out := out.push (toString n, toString x.addr, "-")
  for (n, y) in b.named do
    if !a.named.contains n then out := out.push (toString n, "-", toString y.addr)
  return out

/-- Wave driver worker counts. -/
def waveWorkers : List Nat := [1, 2, 4, 16, 32]

/-- `ix compile-lean` worker counts. -/
def pipelineWorkers : List Nat := [1, 4, 16]

/-- One mode (Pass 3 off or on): every schedule, compared. Returns the
    number of failures. -/
def runMode (env : Environment) (closure : List (Name × ConstantInfo))
    (phases : Ix.CompileM.CompilePhases) (nameByHash : Std.HashMap Address Ix.Name)
    (pass3 : Bool) : IO Nat := do
  let mode := if pass3 then "IX_PASS3=images" else "switch off"
  -- (label, bytes, environment, block failures as (name, message))
  let mut runs : Array (String × ByteArray × Ixon.Env × List (String × String)) := #[]
  let failuresOf (cenv : Ix.CompileM.CompileEnv) : List (String × String) :=
    cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e)
  -- sequential
  match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed (nameByHash := nameByHash)
      (pass3 := pass3) with
  | .error e => throw (IO.userError s!"[schedule] {mode}: sequential driver: {e}")
  | .ok (ixon, _, cenv) =>
    let bytes ← IO.ofExcept (Ixon.serEnv ixon)
    IO.println s!"[schedule] {mode}: sequential: {bytes.size} bytes, {cenv.ungrounded.size} block failures"
    runs := runs.push ("sequential", bytes, ixon, failuresOf cenv)
  -- wave driver
  for k in waveWorkers do
    match ← Ix.CompileM.compileEnvParallelAux phases.rawEnv phases.condensed (numWorkers := k)
        (nameByHash := nameByHash) (pass3? := some pass3) with
    | .error e => throw (IO.userError s!"[schedule] {mode}: wave driver, {k} workers: {e}")
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      IO.println s!"[schedule] {mode}: wave --jobs {k}: {bytes.size} bytes, \
{cenv.ungrounded.size} block failures"
      runs := runs.push (s!"wave --jobs {k}", bytes, ixon, failuresOf cenv)
  -- the whole `ix compile-lean` pipeline
  for k in pipelineWorkers do
    let out ← Tests.Ix.Compile.Twins.leanCompile env closure k (pass3? := some pass3)
    IO.println s!"[schedule] {mode}: compile-lean --workers {k}: {out.bytes.size} bytes, \
{out.cenv.ungrounded.size} block failures"
    runs := runs.push (s!"compile-lean --workers {k}", out.bytes, out.env, failuresOf out.cenv)
  let some (refLabel, refBytes, refEnv, refFails) := runs[0]? | return 1
  let mut failures := 0
  -- Refusals: under every schedule the block failures are exactly the
  -- expected refusals (`NonCanonical.expectedRefusals`) of the constants in
  -- the closure, each with its message (`Twins.refusalCheck`: an unexpected
  -- failure, a refusal with another message, and an expected refusal that
  -- does not happen all fail), and the full (name, message) list is the same
  -- in every schedule.
  let scope : Std.HashSet Name := closure.foldl (init := {}) fun s (n, _) => s.insert n
  let sortFails (xs : List (String × String)) : Array (String × String) :=
    xs.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  for (label, _, _, fails) in runs do
    let bad ← Tests.Ix.Compile.Twins.refusalCheck s!"schedule: {mode}: {label}" scope fails
    if bad == 0 then
      IO.println s!"[schedule] {mode}: {label}: refusals = expectedRefusals ({fails.length})"
    else
      failures := failures + 1
      IO.println s!"[schedule] {mode}: {label}: refusals ≠ expectedRefusals ({bad} violations)"
    if sortFails fails != sortFails refFails then
      failures := failures + 1
      IO.println s!"[schedule] {mode}: {label}: block failures (names or messages) differ \
from {refLabel}"
  for (label, bytes, ixon, _) in runs[1:] do
    if bytes == refBytes then
      IO.println s!"[schedule] {mode}: {label} = {refLabel}"
    else
      failures := failures + 1
      let ds := namedDiffs refEnv ixon
      IO.println s!"[schedule] {mode}: {label} ≠ {refLabel}: {bytes.size} vs {refBytes.size} \
bytes, {ds.size} names differ"
      for (n, x, y) in ds[:20] do
        IO.println s!"[schedule]   {n}: {refLabel} {x}, {label} {y}"
  return failures

def run : IO UInt32 := do
  let env ← get_env!
  let (_, twins) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  let fixtures := validateAuxClosure env
  let names : Std.HashSet Name := twins.foldl (init := {}) fun s (n, _) => s.insert n
  let closure := twins ++ fixtures.filter (!names.contains ·.1)
  IO.println s!"[schedule] {closure.length} constants (twins {twins.length}, fixture corpus \
{fixtures.length})"
  IO.println "[schedule] no speculative driver exists in the Lean compiler: no leg"
  -- the canonical environment and condensation, as `ix compile` computes them
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  let mut failures := 0
  for pass3 in [false, true] do
    failures := failures + (← runMode env closure phases nameByHash pass3)
  IO.println s!"[schedule] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ScheduleIdentity
