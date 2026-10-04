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

  With the switch off, block failures must be exactly the closure's
  `NonCanonical.expectedRefusals`, each with its message. With images on,
  those former surgery refusals are supported: require zero block failures
  and every source name in the output. The twelve former refusals were
  checked by all three kernels, including explicit certified record
  coverage, before introducing this mode-specific expectation. Any
  difference in (name, message) failures between schedules still fails.

  Run with: `lake test -- --ignored compile-schedule-identity`.
-/
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.Pass3

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

/-- Print a line with the monotonic clock in seconds and flush, so a long
    or stuck leg is visible in the log while it runs. -/
def say (s : String) : IO Unit := do
  IO.println s!"{s} (t={(← IO.monoMsNow) / 1000}s)"
  (← IO.getStdout).flush

/-- Wave driver worker counts. -/
def waveWorkers : List Nat := [1, 2, 4, 16, 32]

/-- `ix compile-lean` worker counts. -/
def pipelineWorkers : List Nat := [1, 4, 16]

/-- Optional diagnostic artifact capture. The ordinary gate is unchanged. -/
def saveRun (pass3 : Bool) (label : String) (bytes : ByteArray)
    (failures : List (String × String)) : IO Unit := do
  for line in (← Ix.PhaseTimers.report) do IO.eprintln line
  if let some dir ← IO.getEnv "SCHED_OUTPUT_DIR" then
    IO.FS.createDirAll dir
    let path := s!"{dir}/{if pass3 then "on" else "off"}-{label}.ixe"
    IO.FS.writeBinFile path bytes
    let sorted := failures.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
    let lines := sorted.toList.map fun (name, cause) =>
      (Json.mkObj [("name", toJson name), ("cause", toJson cause)]).compress
    IO.FS.writeFile s!"{path}.failures.jsonl" (String.intercalate "\n" lines ++ "\n")
    say s!"[schedule] saved {path}: {Address.blake3 bytes}"
    for (name, cause) in sorted[:5] do
      say s!"[schedule] {label}: captured refusal {name}: {cause}"

/-- One mode (Pass 3 off or on): every schedule, compared. Returns the
    number of failures. -/
def runMode (env : Environment) (closure : List (Name × ConstantInfo))
    (phases : Ix.CompileM.CompilePhases) (nameByHash : Std.HashMap Address Ix.Name)
    (pass3 : Bool) : IO Nat := do
  let mode := if pass3 then "IX_PASS3=images" else "switch off"
  let diagnostic := (← IO.getEnv "SCHED_DIAGNOSTIC") == some "1"
  let singleWave := (← IO.getEnv "SCHED_SINGLE_WAVE") == some "32"
  if singleWave then say "[schedule] DIAGNOSTIC: wave 32 only; no schedule-identity claim; not a full gate"
  if diagnostic then say "[schedule] DIAGNOSTIC: sequential and wave 1 only; not a full gate"
  say s!"[schedule] {mode}: begin"
  -- (label, bytes, environment, block failures as (name, message))
  let mut runs : Array (String × ByteArray × Ixon.Env × List (String × String)) := #[]
  let failuresOf (cenv : Ix.CompileM.CompileEnv) : List (String × String) :=
    cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e)
  -- sequential
  if !singleWave then
    match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed (nameByHash := nameByHash)
        (pass3 := pass3) with
    | .error e => throw (IO.userError s!"[schedule] {mode}: sequential driver: {e}")
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      saveRun pass3 "sequential" bytes (failuresOf cenv)
      say s!"[schedule] {mode}: sequential: {bytes.size} bytes, {cenv.ungrounded.size} block failures"
      runs := runs.push ("sequential", bytes, ixon, failuresOf cenv)
  -- wave driver
  for k in (if singleWave then [32] else if diagnostic then [1] else waveWorkers) do
    match ← Ix.CompileM.compileEnvParallelAux phases.rawEnv phases.condensed (numWorkers := k)
        (nameByHash := nameByHash) (pass3? := some pass3) with
    | .error e => throw (IO.userError s!"[schedule] {mode}: wave driver, {k} workers: {e}")
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      saveRun pass3 s!"wave-{k}" bytes (failuresOf cenv)
      say s!"[schedule] {mode}: wave --jobs {k}: {bytes.size} bytes, \
{cenv.ungrounded.size} block failures"
      runs := runs.push (s!"wave --jobs {k}", bytes, ixon, failuresOf cenv)
  -- the whole `ix compile-lean` pipeline
  for k in (if singleWave || diagnostic then [] else pipelineWorkers) do
    let out ← Tests.Ix.Compile.Twins.leanCompile env closure k (pass3? := some pass3)
    saveRun pass3 s!"pipeline-{k}" out.bytes (failuresOf out.cenv)
    say s!"[schedule] {mode}: compile-lean --workers {k}: {out.bytes.size} bytes, \
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
  for (label, _, ixon, fails) in runs do
    let bad ← if pass3 then do
        for (name, message) in fails do
          say s!"[schedule] {label}: unexpected switch-on refusal {name}: {message}"
        let missing := closure.filter fun (name, _) => !ixon.named.contains (Ix.Name.fromLeanName name)
        for (name, _) in missing do
          say s!"[schedule] {label}: switch-on output omitted source name {name}"
        pure (fails.length + missing.length)
      else Tests.Ix.Compile.Twins.refusalCheck s!"schedule: {mode}: {label}" scope fails
    if bad == 0 then
      say s!"[schedule] {mode}: {label}: refusals = expectedRefusals ({fails.length})"
    else
      failures := failures + 1
      say s!"[schedule] {mode}: {label}: refusals ≠ expectedRefusals ({bad} violations)"
    if sortFails fails != sortFails refFails then
      failures := failures + 1
      say s!"[schedule] {mode}: {label}: block failures (names or messages) differ \
from {refLabel}"
  for (label, bytes, ixon, _) in runs[1:] do
    if bytes == refBytes then
      say s!"[schedule] {mode}: {label} = {refLabel}"
    else
      failures := failures + 1
      let ds := namedDiffs refEnv ixon
      say s!"[schedule] {mode}: {label} ≠ {refLabel}: {bytes.size} vs {refBytes.size} \
bytes, {ds.size} names differ"
      for (n, x, y) in ds[:20] do
        say s!"[schedule]   {n}: {refLabel} {x}, {label} {y}"
      say s!"[schedule] tables: constants {refEnv.consts.size}/{ixon.consts.size}, \
names {refEnv.names.size}/{ixon.names.size}, blobs {refEnv.blobs.size}/{ixon.blobs.size}"
      let mut metaDiffs := 0
      for (n, x) in refEnv.named do
        if let some y := ixon.named.get? n then
          if x != y then
            metaDiffs := metaDiffs + 1
            say s!"[schedule] Named differs {n}: addr={x.addr != y.addr} \
meta={x.constMeta != y.constMeta} original={x.original != y.original} hints={x.hints != y.hints}"
      say s!"[schedule] Named differences: {metaDiffs}"
  return failures

/-- Diagnose the on-mode domain of the off-mode refusal fixtures against a
saved artifact. Require explicit owning-record acceptance and real work by
both executable kernels before changing a refusal expectation. -/
def checkRefusalArtifact (path : System.FilePath) : IO UInt32 := do
  let names := Tests.Ix.Compile.NonCanonical.expectedRefusals.toArray.map (·.constant.toString)
  let dir := System.FilePath.mk ((← IO.getEnv "SCHED_CHECK_OUTPUT").getD "out/schedule-refusal-check")
  IO.FS.createDirAll dir
  let failures ← Tests.Ix.Compile.Pass3.kernelFailures dir path names (anon := true)
  for (kernel, name, message) in failures do
    say s!"[schedule-check] {kernel}: {name}: {message}"
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile path))
  let records := parts.namedRows.foldl (init := ({} : Std.HashMap String Address)) fun m row =>
    m.insert row.name.pretty (Tests.Ix.Compile.AuxCert.recordOf parts.env row.addr)
  let report ← IO.ofExcept (Tests.Ix.Compile.KernelReport.parse (← IO.FS.readFile (dir / "cert.jsonl")))
  let mut rejected := failures.size
  for name in names do
    let some address := records.get? name | throw (IO.userError s!"missing compiled fixture {name}")
    let some verdict := report.get? (toString address) | throw (IO.userError s!"missing verdict {name}@{address}")
    say s!"[schedule-check] {name}@{address}: {verdict.outcome}: {verdict.reason}"
    if verdict.outcome != "accept" then rejected := rejected + 1
  say s!"[schedule-check] {names.size} fixtures, {rejected} failed acceptance checks"
  return if rejected == 0 then 0 else 1

def run : IO UInt32 := do
  if let some path ← IO.getEnv "SCHED_CHECK_IXE" then
    return ← checkRefusalArtifact path
  let env ← get_env!
  let (_, twins) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  let fixtures := validateAuxClosure env
  let names : Std.HashSet Name := twins.foldl (init := {}) fun s (n, _) => s.insert n
  let mut closure := twins ++ fixtures.filter (!names.contains ·.1)
  if let some selected ← IO.getEnv "SCHED_PREFIXES" then
    let prefixes := selected.splitOn ","
    let seeds := env.constants.toList.filterMap fun (n, _) =>
      if prefixes.any (fun p => !p.isEmpty && (n.toString.splitOn p).length > 1)
      then some n else none
    if seeds.isEmpty then throw (IO.userError "SCHED_PREFIXES matched no declarations")
    closure := Tests.Ix.Compile.Twins.closeWithRecursors env (Ix.EnvScope.collectDeps env seeds)
    say s!"[schedule] DIAGNOSTIC selected prefixes {selected}: {seeds.length} seeds; not a full gate"
  say s!"[schedule] {closure.length} constants (twins {twins.length}, fixture corpus \
{fixtures.length})"
  say "[schedule] no speculative driver exists in the Lean compiler: no leg"
  -- the canonical environment and condensation, as `ix compile` computes them
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  -- D9: compare the cache entry for each actual block before/after
  -- reindexing, including missing entries and the complete reference set.
  let indexed := Ix.CompileM.canonicalBlockRefs phases.condensed
  let mut rekeyed := 0
  let mut formerlyMissed := 0
  for (lo, all) in phases.condensed.blocks do
    let key := Ix.CompileM.blockKey lo all
    if key != lo then rekeyed := rekeyed + 1
    if (phases.condensed.blockRefs.get? key).isNone then formerlyMissed := formerlyMissed + 1
    let same := match phases.condensed.blockRefs.get? lo, indexed.get? key with
      | none, none => true
      | some a, some b => a.size == b.size && a.toList.all b.contains
      | _, _ => false
    unless same do throw (IO.userError s!"D9: reference cache changed for {lo.pretty}")
  say s!"[schedule] reference cache: {phases.condensed.blocks.size} blocks equivalent, \
{rekeyed} keys changed, {formerlyMissed} former misses"
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  let mut failures := 0
  -- `SCHED_MODES=off` or `on` runs one mode only (diagnostics).
  let modes := match ← IO.getEnv "SCHED_MODES" with
    | some "off" => [false]
    | some "on" => [true]
    | _ => [false, true]
  for pass3 in modes do
    failures := failures + (← runMode env closure phases nameByHash pass3)
  say s!"[schedule] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ScheduleIdentity
