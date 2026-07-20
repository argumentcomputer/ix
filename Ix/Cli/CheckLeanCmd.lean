/-
  `ix check-lean <path.ixe>`: typecheck a serialized `.ixe` environment
  through the pure-Lean `Ix.Tc` kernel — the reference-kernel counterpart
  of `ix check-rs`, with matching mode default, live progress, and exit
  codes. Correctness-first: expect the Rust kernel to be much faster.

  Modes:
  - Default (meta): the full env is parsed (`Ixon.deEnv`), meta-ingressed
    in parallel into one merged `KEnv .meta`, and every Named entry's
    block is checked. Labels are Lean names.
  - `--anon`: anon sections only (`Ixon.deEnvAnon`); metadata never
    reaches the kernel; labels are `#<hex>` addresses. Verdicts are
    mode-independent (checking never reads metadata) — meta buys readable
    progress/errors, anon a smaller memory footprint.

  Both modes eagerly ingress the WHOLE env before checking: checking is
  subject-only but still reads dependencies' declared types, so every
  constant must be present. `--max` therefore bounds the check phase
  only, never ingress. Checking then runs work-stealing parallel workers
  over the shared env (see `Ix.Tc.ParCheck`).

  Progress mirrors `check-rs`: a periodic aggregate line (done/total,
  rate, eta, oldest in-flight) on stderr, persistent lines only for
  failures and slow constants, tunable via IX_KERNEL_CHECK_PROGRESS_MS /
  IX_PROGRESS_MS, IX_KERNEL_CHECK_SLOW_MS, IX_KERNEL_CHECK_ACTIVE_SLOW_MS
  (0 disables). `--fail-out` streams failures in the check-rs FailureLog
  shape (bare name lines + `#` comments), so a meta-mode file feeds
  straight into `ix check-rs --consts-file` for differential bisects.

  Exit codes match check-rs: 0 all pass; 3 kernel rejection; 2 usage;
  1 infra (read/parse/ingress) error.
-/
module
public import Cli
public import Ix.Common
public import Ix.Tc
public import Ix.Benchmark.Results

public section

namespace Ix.Cli.CheckLeanCmd

open Ix.Tc

/-- First set env var wins; else the default. Zero is a valid setting. -/
def envNat (names : List String) (dflt : Nat) : IO Nat := do
  for n in names do
    if let some v ← IO.getEnv n then
      if let some parsed := v.trimAscii.toString.toNat? then
        return parsed
  return dflt

/-- Default worker count: `LEAN_NUM_THREADS`, else the machine's core
    count via `nproc` (Lean has no core-count API), else 8. -/
def defaultWorkers : IO Nat := do
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS").bind
      (·.trimAscii.toString.toNat?) then
    return max 1 n
  match ← (IO.Process.output { cmd := "nproc" }).toBaseIO with
  | .ok out =>
    if out.exitCode == 0 then
      return (out.stdout.trimAscii.toString.toNat?).map (max 1) |>.getD 8
    return 8
  | .error _ => return 8

/-- Meta path: full parse → parallel meta ingress → check work → parallel
    check. Returns `(report, workItems)` or an infra error. -/
def runMetaCheck (bytes : ByteArray) (cfg : ParCheckCfg) (verify : Bool)
    (max? : Option Nat) (failOut? : Option IO.FS.Handle) :
    IO (Except String (ParCheckReport × Nat)) := do
  let t0 ← IO.monoMsNow
  match Ixon.deEnv bytes with
  | .error e => return .error s!"deserialize failed: {e}"
  | .ok ixonEnv =>
    let t1 ← IO.monoMsNow
    IO.eprintln s!"[check-lean] deserialize: {t1 - t0}ms \
                   ({ixonEnv.consts.size} consts, {ixonEnv.named.size} named)"
    match ingressMetaEnvParallel ixonEnv (verify := verify) with
    | .error e => return .error s!"meta ingress failed: {e}"
    | .ok kenv =>
      let t2 ← IO.monoMsNow
      IO.eprintln s!"[check-lean] ingress:     {t2 - t1}ms \
                     ({kenv.consts.size} kernel consts, {kenv.blocks.size} blocks)"
      let workAll := buildCheckWork kenv
      let work := match max? with
        | some n => workAll.extract 0 (min n workAll.size)
        | none => workAll
      let totalTargets := work.foldl (fun n it => n + it.targets.size) 0
      IO.eprintln s!"[check-lean] checking {work.size} work item(s) for \
                     {totalTargets} constants with {cfg.workers} worker(s)..."
      let prims := Primitives.fromEnv kenv
      let report ← checkEnvParallel kenv prims work
        (labelOf := fun id => toString id)
        (failLabelOf := fun id => toString id.name)
        cfg failOut?
      return .ok (report, work.size)

/-- Anon path: anon parse → parallel anon ingress → check work → parallel
    check. Same driver, `#<hex>` labels. -/
def runAnonCheck (bytes : ByteArray) (cfg : ParCheckCfg) (verify : Bool)
    (max? : Option Nat) (failOut? : Option IO.FS.Handle) :
    IO (Except String (ParCheckReport × Nat)) := do
  let t0 ← IO.monoMsNow
  match Ixon.deEnvAnon bytes with
  | .error e => return .error s!"deserialize failed: {e}"
  | .ok ixonEnv =>
    let t1 ← IO.monoMsNow
    IO.eprintln s!"[check-lean] deserialize: {t1 - t0}ms \
                   ({ixonEnv.consts.size} consts, {ixonEnv.anonHints.size} hints)"
    match buildAnonWork ixonEnv with
    | .error e => return .error s!"work discovery failed: {e}"
    | .ok ingressWork =>
      match ingressAnonEnvParallel ixonEnv ingressWork (verify := verify) with
      | .error e => return .error s!"anon ingress failed: {e}"
      | .ok kenv =>
        let t2 ← IO.monoMsNow
        IO.eprintln s!"[check-lean] ingress:     {t2 - t1}ms \
                       ({kenv.consts.size} kernel consts, {kenv.blocks.size} blocks)"
        let workAll := buildCheckWork kenv
        let work := match max? with
          | some n => workAll.extract 0 (min n workAll.size)
          | none => workAll
        let totalTargets := work.foldl (fun n it => n + it.targets.size) 0
        IO.eprintln s!"[check-lean] checking {work.size} work item(s) for \
                       {totalTargets} constants with {cfg.workers} worker(s)..."
        let report ← checkEnvParallel kenv Primitives.ofAnonAddrs work
          (labelOf := fun id => toString id)
          (failLabelOf := fun id => s!"#{id.addr}")
          cfg failOut?
        return .ok (report, work.size)

/-- Best-effort `#hex → name` relabeling for anon failure rows (meta
    sections parsed only on demand, only when something failed). -/
def relabelAnonFailures (bytes : ByteArray)
    (failures : Array (String × String)) : Array (String × String) :=
  match Ixon.deEnv bytes with
  | .error _ => failures
  | .ok fullEnv =>
    let addrToName : Std.HashMap String String :=
      fullEnv.addrToName.fold
        (fun acc addr name => acc.insert (toString addr) (toString name)) {}
    failures.map fun (label, msg) =>
      match addrToName[(label.drop 1).toString]? with
      | some n => (s!"{label} ({n})", msg)
      | none => (label, msg)

def runCheckLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return Ix.Benchmark.Results.exitUsage
  let envPath := pathArg.as! String
  let anon := p.hasFlag "anon"
  let verbose := p.hasFlag "verbose"
  let verify := !(p.hasFlag "no-verify")
  let clearEvery := ((p.flag? "clear-every").map (·.as! Nat)).getD 50
  let max? := (p.flag? "max").map (·.as! Nat)
  let failOutPath := ((p.flag? "fail-out").map (·.as! String)).getD ""
  let workers ← match (p.flag? "workers").map (·.as! Nat) with
    | some n => pure (max 1 n)
    | none => defaultWorkers
  let cfg : ParCheckCfg := {
    workers, clearEvery, verbose
    progressMs := ← envNat ["IX_KERNEL_CHECK_PROGRESS_MS", "IX_PROGRESS_MS"] 2000
    slowMs := ← envNat ["IX_KERNEL_CHECK_SLOW_MS"] 7000
    stuckMs := ← envNat ["IX_KERNEL_CHECK_ACTIVE_SLOW_MS"] 30000 }

  IO.println s!"Running Ix.Tc kernel check \
                ({if anon then "anon" else "meta"} mode) on {envPath}"
  let t0 ← IO.monoMsNow
  let bytes ← IO.FS.readBinFile envPath
  let t1 ← IO.monoMsNow
  IO.eprintln s!"[check-lean] read env:    {t1 - t0}ms ({bytes.size} bytes)"

  let failOut? ← if failOutPath.isEmpty then pure none else do
    let h ← IO.FS.Handle.mk failOutPath .write
    h.putStrLn "# ix check-lean failures"
    h.putStrLn s!"# env: {envPath}"
    pure (some h)

  let result ← if anon then runAnonCheck bytes cfg verify max? failOut?
    else runMetaCheck bytes cfg verify max? failOut?
  match result with
  | .error e =>
    IO.eprintln s!"[check-lean] {e}"
    return 1
  | .ok (report, workN) =>
    if let some h := failOut? then
      h.putStrLn ""
      h.putStrLn s!"# total failures: {report.failures.size}"
      h.flush
    let failures := if anon && !report.failures.isEmpty then
        relabelAnonFailures bytes report.failures
      else report.failures
    IO.println s!"[check-lean] checked {report.targetsCovered} constants \
                  ({workN} work items) in {report.elapsedMs}ms"
    IO.println s!"[check-lean] {report.passed}/{report.targetsCovered} passed"
    if !failures.isEmpty then
      IO.println s!"[check-lean] {failures.size} failure(s):"
      let shown := min 30 failures.size
      for (label, msg) in failures.toSubarray 0 shown do
        IO.println s!"  ✗ {label}: {msg}"
      if failures.size > shown then
        IO.println s!"  … ({failures.size - shown} more failures suppressed)"
    if !failOutPath.isEmpty then
      IO.println s!"[check-lean] streamed {report.failures.size} failure(s) \
                    to {failOutPath}"
    IO.println s!"##check-lean## {report.elapsedMs} {report.passed} \
                  {failures.size} {report.targetsCovered}"
    return if failures.isEmpty then 0 else Ix.Benchmark.Results.exitRejected

end Ix.Cli.CheckLeanCmd

open Ix.Cli.CheckLeanCmd in
def checkLeanCmd : Cli.Cmd := `[Cli|
  "check-lean" VIA runCheckLeanCmd;
  "Typecheck a `.ixe` through the pure-Lean Ix.Tc kernel (meta mode by default; parallel)"

  FLAGS:
    anon;                   "Run in anon mode (metadata never reaches the kernel; `#hex` labels)"
    workers       : Nat;    "Parallel check workers (default: LEAN_NUM_THREADS, else core count)"
    "fail-out"    : String; "Stream failing constants to this path (check-rs consts-file format)"
    max           : Nat;    "Check only the first N work items (ingress still covers the whole env)"
    "clear-every" : Nat;    "Clear each worker's reduction caches every N work items (0 disables; default 50)"
    "no-verify";            "Skip blake3 integrity verification at constant materialization"
    verbose;                "Serial mode: one line per constant (forces --workers 1)"

  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
