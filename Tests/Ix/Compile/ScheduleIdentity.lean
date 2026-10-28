/-
  compile-schedule-identity: the Lean compiler's output does not depend on
  the schedule (TT-12; the executable regression of "parallel = sequential").

  Over the twins closure (`Tests.Ix.Compile.Twins`, every family) and the
  fixture corpus (`validateAuxClosure`: `Tests.Ix.Compile.Mutual`,
  `Canonicity`, `LevelSpellings`, the IxVM and `Test.Ix.Fixtures`
  families), compile with

  - the driver, the pure wave fold `Ix.CompileM.compileEnvFold`, on the
    canonical environment and condensation of `rsCompilePhasesOf` (as
    `ix compile` computes them), at its default width and at widths 1 and
    32 (tasks per wave; the value must not depend on it);
  - the reference schedule (`Tests.Ix.Compile.ScheduleReference.sequential`,
    a sequential driver: live state, one block at a
    time) on the same input,
    with the least and with the greatest ready key first;
  - the whole `ix compile-lean` pipeline (`compileLeanInput`, with its own
    canon and condensation, so other block representatives) at 1, 4 and 16
    workers;

  and require every serialized environment and decline report to be identical. A
  difference is reported with the constant and its two addresses.

  Refusals: the twin presentations that the compilers refuse on purpose
  (`Tests.Ix.Compile.NonCanonical.expectedRefusals`) are refused under every
  schedule, with their messages, and nothing else is; every other source name
  is in the output; and the (name, message) failures are the same under every
  schedule.

  The twins' fixtures are not imported into `IxTests` (see
  `Tests.Ix.Compile.Twins`): the suite loads this module's imports and the
  twins' fixture root at run time.

  The legs run concurrently (each is an independent compile of the same
  read-only input; `SCHED_JOBS=<n>` runs at most n at a time), and are
  reported and compared in the order above once all have finished.

  Tiers: the default (`SCHED_LEGS=full`) is the integration gate, all eight
  legs. `SCHED_LEGS=quick` is the per-iteration tier: `fold` (the
  reference), `reference, least key first` and `compile-lean --workers 16`,
  with every check below; it is never the integration gate.
  `SCHED_OUTPUT_DIR=<dir>` writes each leg's bytes and failures, for
  diagnosis.

  Ported from the old branch (`a9cf3607`) without its Pass 3 mode and
  phase timers: the compiler here has one mode.

  Run with: `lake exe IxTests --ignored compile-schedule-identity`.
-/
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ScheduleReference
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.IxVM
import Tests.Ix.Fixtures

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

/-- `ix compile-lean` worker counts. -/
def pipelineWorkers : List Nat := [1, 4, 16]

/-- Optional diagnostic artifact capture (`SCHED_OUTPUT_DIR`). -/
def saveRun (label : String) (bytes : ByteArray) (failures : List (String × String)) :
    IO Unit := do
  if let some dir ← IO.getEnv "SCHED_OUTPUT_DIR" then
    IO.FS.createDirAll dir
    let path := s!"{dir}/{label}.ixe"
    IO.FS.writeBinFile path bytes
    let sorted := failures.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
    let lines := sorted.toList.map fun (name, cause) =>
      (Json.mkObj [("name", toJson name), ("cause", toJson cause)]).compress
    IO.FS.writeFile s!"{path}.failures.jsonl" (String.intercalate "\n" lines ++ "\n")
    say s!"[schedule] saved {path}: {Address.blake3 bytes}"

/-- One leg's result: (label, bytes, environment, block failures as (name, message)). -/
abbrev Declines := Array (String × String)

/-- The Lean compiler compiles Lean's declarations as given and records no
    declines, on every leg. -/
def declinesOf (_cenv : Ix.CompileM.CompileEnv) : Declines := #[]

abbrev LegResult := String × ByteArray × Ixon.Env × List (String × String) × Declines

/-- A leg: its label in the log, its file label for `saveRun`, and the compile. -/
structure Leg where
  label : String
  saveLabel : String
  act : IO (ByteArray × Ixon.Env × List (String × String) × Declines)

/-- The leg tier: `SCHED_LEGS=quick` (three legs) or `full` (the default, the
    integration tier). -/
def quickTier : IO Bool := do
  match ← IO.getEnv "SCHED_LEGS" with
  | none | some "full" => pure false
  | some "quick" => pure true
  | some other => throw (IO.userError s!"SCHED_LEGS={other}: expected full or quick")

/-- The legs, in the order the log reports them; the first is the reference. -/
def legsOf (env : Environment) (closure : List (Name × ConstantInfo))
    (phases : Ix.CompileM.CompilePhases) :
    IO (Array Leg) := do
  let quick ← quickTier
  let failuresOf (cenv : Ix.CompileM.CompileEnv) : List (String × String) :=
    cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e)
  let outcome (label : String)
      (result : Except String (Ixon.Env × Nat × Ix.CompileM.CompileEnv)) :
      IO (ByteArray × Ixon.Env × List (String × String) × Declines) := do
    match result with
    | .error e => throw (IO.userError s!"[schedule] {label}: {e}")
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      pure (bytes, ixon, failuresOf cenv, declinesOf cenv)
  let mut legs : Array Leg := #[]
  -- the driver, at its default width (the reference) and at widths 1 and 32
  for width in (if quick then [none] else [none, some 1, some 32]) do
    let label := match width with | none => "fold" | some w => s!"fold, width {w}"
    let saveLabel := match width with | none => "fold" | some w => s!"fold-{w}"
    legs := legs.push { label, saveLabel, act := do
      -- `IO.lazyPure`: the pure driver is evaluated inside the action, so the
      -- legs run concurrently
      outcome label (← IO.lazyPure fun _ => match width with
        | none => Ix.CompileM.compileEnvFold phases.rawEnv phases.condensed
        | some w => Ix.CompileM.compileEnvFold phases.rawEnv phases.condensed
            (width := w)) }
  -- the reference schedule, least and greatest ready key first
  for least in (if quick then [true] else [true, false]) do
    let label := s!"reference, {if least then "least" else "greatest"} key first"
    let saveLabel := s!"reference-{if least then "least" else "greatest"}"
    legs := legs.push { label, saveLabel, act := do
      outcome label (← IO.lazyPure fun _ =>
        ScheduleReference.sequential phases.rawEnv phases.condensed
          (least := least)) }
  -- the whole `ix compile-lean` pipeline
  for k in (if quick then [16] else pipelineWorkers) do
    legs := legs.push { label := s!"compile-lean --workers {k}", saveLabel := s!"pipeline-{k}",
                        act := do
      let out ← ClosureHarness.compileClosure env closure k
      pure (out.bytes, out.env, failuresOf out.cenv, declinesOf out.cenv) }
  return legs

/-- Run the legs, at most `SCHED_JOBS` at a time (default: all at once; each
    leg is an independent compile of the same read-only input), and return
    their results in leg order. -/
def runLegs (legs : Array Leg) : IO (Array LegResult) := do
  let jobs := ((← IO.getEnv "SCHED_JOBS").bind String.toNat?).getD 0
  let jobs := if jobs == 0 then legs.size else jobs
  let mut done : Array (ByteArray × Ixon.Env × List (String × String) × Declines) := #[]
  let mut pending : Array (Task (Except IO.Error (ByteArray × Ixon.Env × List (String × String) × Declines))) := #[]
  for leg in legs do
    if pending.size ≥ jobs then
      done := done.push (← IO.ofExcept (← IO.wait pending[0]!))
      pending := pending.extract 1 pending.size
    pending := pending.push (← IO.asTask (prio := .dedicated) leg.act)
  for t in pending do done := done.push (← IO.ofExcept (← IO.wait t))
  return (legs.zip done).map fun (leg, (bytes, ixon, fails, declines)) => (leg.label, bytes, ixon, fails, declines)

/-- Every schedule's result, compared. Returns the number of failures. -/
def compareLegs (closure : List (Name × ConstantInfo)) (legs : Array Leg)
    (runs : Array LegResult) : IO Nat := do
  if ← quickTier then
    say "[schedule] SCHED_LEGS=quick: the per-iteration tier (3 legs); not the integration gate"
  let scope : Std.HashSet Name := closure.foldl (init := {}) fun s (n, _) => s.insert n
  for (leg, (_, bytes, _, fails, declines)) in legs.zip runs do
    saveRun leg.saveLabel bytes fails
    say s!"[schedule] {leg.label}: {bytes.size} bytes, {fails.length} block failures, {declines.size} declines"
  let some (refLabel, refBytes, refEnv, refFails, refDeclines) := runs[0]? | return 1
  let mut failures := 0
  -- Refusals: under every schedule exactly the expected refusals, with their
  -- messages; every other source name is in the output; and the full
  -- (name, message) list of failures is the same in every schedule.
  let sortFails (xs : List (String × String)) : Array (String × String) :=
    xs.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  for (label, _, ixon, fails, declines) in runs do
    let bad ← Tests.Ix.Compile.Twins.refusalCheck s!"schedule: {label}" scope fails
    let missing := closure.filter fun (name, _) =>
      !Tests.Ix.Compile.Twins.refusedSet.contains name
        && !ixon.named.contains (_root_.Ix.Name.fromLeanName name)
    for (name, _) in missing do
      say s!"[schedule] {label}: output omitted source name {name}"
    if bad + missing.length == 0 then
      say s!"[schedule] {label}: exactly the expected refusals, every other source name present"
    else
      failures := failures + 1
      say s!"[schedule] {label}: {bad + missing.length} violation(s)"
    if sortFails fails != sortFails refFails then
      failures := failures + 1
      say s!"[schedule] {label}: block failures (names or messages) differ from {refLabel}"
    if declines != refDeclines then
      failures := failures + 1
      say s!"[schedule] {label}: decline reports differ from {refLabel}"
  for (label, bytes, ixon, _, _) in runs[1:] do
    if bytes == refBytes then
      say s!"[schedule] {label} = {refLabel}"
    else
      failures := failures + 1
      let ds := namedDiffs refEnv ixon
      say s!"[schedule] {label} ≠ {refLabel}: {bytes.size} vs {refBytes.size} bytes, \
{ds.size} names differ"
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

def run : IO UInt32 := do
  -- this module's imports (the fixture corpus) and the twins' fixtures
  let env ← getCompileEnv ((this_file!).push Tests.Ix.Compile.Twins.fixturesModule)
  let (_, twins) :=
    Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  let fixtures := validateAuxClosure env
  let names : Std.HashSet Name := twins.foldl (init := {}) fun s (n, _) => s.insert n
  let closure := twins ++ fixtures.filter (!names.contains ·.1)
  say s!"[schedule] {closure.length} constants (twins {twins.length}, fixture corpus \
{fixtures.length})"
  -- the canonical environment and condensation, as `ix compile` computes them
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  -- Every leg is an independent compile of the same input: run them
  -- concurrently (`SCHED_JOBS` bounds it), then compare in leg order.
  let legs ← legsOf env closure phases
  let results ← runLegs legs
  let failures ← compareLegs closure legs results
  say s!"[schedule] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ScheduleIdentity
