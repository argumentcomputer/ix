/-
  compile-schedule-identity: the Lean compiler's output does not depend on
  the schedule (Phase A §3.5 and §5.5; design document §6.2; the A7 gate).

  Over the twins closure (`Tests.Ix.Compile.Twins`, every family) and the
  aux fixture corpus (`validateAuxClosure`: `Tests.Ix.Compile.Mutual`,
  `Canonicity`, `LevelSpellings`, the IxVM and `Test.Ix.Fixtures`
  families), compile with

  - the sequential driver `Ix.CompileM.compileEnvAux` (the fold that §6.2
    makes the definition), on the canonical environment and condensation of
    `rsCompilePhasesOf`;
  - the wave driver `compileEnvParallelAux` on the same input at 1, 4 and
    16 workers;
  - the whole `ix compile-lean` pipeline (`compileLeanInput`, its own canon
    and condensation) at 1, 4 and 16 workers;

  and require every serialized environment to be byte-identical. A
  difference is reported with the constant and its two addresses; it is a
  finding for A7, not something this suite repairs.

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

def run : IO UInt32 := do
  let env ← get_env!
  let (_, twins) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  let fixtures := validateAuxClosure env
  let names : Std.HashSet Name := twins.foldl (init := {}) fun s (n, _) => s.insert n
  let closure := twins ++ fixtures.filter (!names.contains ·.1)
  IO.println s!"[schedule] {closure.length} constants (twins {twins.length}, fixture corpus \
{fixtures.length})"
  -- the canonical environment and condensation, as `ix compile` computes them
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  let mut runs : Array (String × ByteArray × Ixon.Env) := #[]
  -- sequential
  match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed (nameByHash := nameByHash) with
  | .error e => throw (IO.userError s!"[schedule] sequential driver: {e}")
  | .ok (ixon, _, cenv) =>
    let bytes ← IO.ofExcept (Ixon.serEnv ixon)
    IO.println s!"[schedule] sequential: {bytes.size} bytes, {cenv.ungrounded.size} block failures"
    runs := runs.push ("sequential", bytes, ixon)
  -- wave driver
  for k in [1, 4, 16] do
    match ← Ix.CompileM.compileEnvParallelAux phases.rawEnv phases.condensed (numWorkers := k)
        (nameByHash := nameByHash) with
    | .error e => throw (IO.userError s!"[schedule] wave driver, {k} workers: {e}")
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      IO.println s!"[schedule] wave --jobs {k}: {bytes.size} bytes, {cenv.ungrounded.size} block failures"
      runs := runs.push (s!"wave --jobs {k}", bytes, ixon)
  -- the whole `ix compile-lean` pipeline
  for k in [1, 4, 16] do
    let out ← Tests.Ix.Compile.Twins.leanCompile env closure k
    IO.println s!"[schedule] compile-lean --workers {k}: {out.bytes.size} bytes, \
{out.cenv.ungrounded.size} block failures"
    runs := runs.push (s!"compile-lean --workers {k}", out.bytes, out.env)
  let some (refLabel, refBytes, refEnv) := runs[0]? | return 1
  let mut failures := 0
  for (label, bytes, ixon) in runs[1:] do
    if bytes == refBytes then
      IO.println s!"[schedule] {label} = {refLabel}"
    else
      failures := failures + 1
      let ds := namedDiffs refEnv ixon
      IO.println s!"[schedule] {label} ≠ {refLabel}: {bytes.size} vs {refBytes.size} bytes, \
{ds.size} names differ"
      for (n, x, y) in ds[:20] do
        IO.println s!"[schedule]   {n}: {refLabel} {x}, {label} {y}"
  IO.println s!"[schedule] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ScheduleIdentity
