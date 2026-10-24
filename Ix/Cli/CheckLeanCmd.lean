module

public import Cli
public import Ix.Common
public import Ix.Cli.CheckLeanTargets
public import Ix.KernelCheck.Run
public import Ix.KernelCheck.Stream
public import Ix.Runtime.Thread
public import Ix.Benchmark.Results

public section

/-! The IxC host record checker behind check-lean. Both modes authenticate
input bytes. Selected declarations run with their complete supporting closure;
actual emitted-key coverage is required. This harness reports accept/typed/
reject/decline/blocked, not an aggregate certified byte-admission theorem. -/

namespace Ix.Cli.CheckLeanCmd

open Ix.Kernel Ix.Kernel.Reader Benchmarks.Kernel.CheckIxeStep
open Benchmarks.Kernel.CheckIxeMeta
open Ix.Cli.CheckLeanTargets

inductive DriverError where
  | usage (message : String)
  | infrastructure (message : String)
  | refused (label message : String)

def DriverError.message : DriverError → String
  | .usage s | .infrastructure s => s | .refused n s => s!"{n}: {s}"
def DriverError.exitCode : DriverError → UInt32
  | .usage _ => 2 | .infrastructure _ => 1 | .refused .. => 3

def targetError : CheckLeanTargets.Error → DriverError
  | .selector s => .usage s
  | .input n e => .refused n s!"{(readOutcome e).1}: {(readOutcome e).2}"
  | .coverage n s => .refused n s!"decline: {s}"

structure CheckCfg where
  workers : Nat := 1
  verbose : Bool := false
  silent : Bool := false
  progressMs : Nat := 2000
  slowMs : Nat := 7000
  stackBytes : Nat := 256 * 1024 * 1024
  tag : String := "[check-lean]"

structure PreparedInput where
  parts : Ixon.LazyEnvParts
  setup : Setup
  pre : Prelude .anon
  hints : Hints
  inventory : Array Candidate
  anon : Bool
  prepareMs : Nat := 0

/-- Authenticate first; retain raw windows and reader skeletons. No metadata
or original-data field is rebuilt through an incomplete Env literal. -/
def prepareInput (bytes : ByteArray) (anon : Bool := false) : IO (Except DriverError PreparedInput) := do
  let start ← IO.monoMsNow
  let result : Except DriverError PreparedInput ← IO.lazyPure fun _ => do
    let parts ← (Ixon.deEnvVerifiedLazy bytes).mapError DriverError.infrastructure
    let table ← defaultTable.mapError DriverError.infrastructure
    let pre ← (preludeFor table : Except String (Prelude .anon)).mapError DriverError.infrastructure
    let mut store : RecordStore := {}
    let mut literals := #[]
    for (a, lc) in parts.env.consts do
      let c ← lc.get.mapError DriverError.infrastructure
      let (nat, str) := literalKinds c
      if nat || str then literals := literals.push (a, Benchmarks.Kernel.CheckIxeStream.literalStandIn nat str)
      store := store.insert a (Benchmarks.Kernel.CheckIxeStream.skeleton c)
    let hints := Hints.ofStore store parts.env.anonHints
    let setup := Benchmarks.Kernel.CheckIxeStep.setup store (parts.env.blobs[·]?) table pre hints.lookup
      (literals := some literals)
    let inventory ← if anon then (anonymousCandidates store).mapError targetError else
      pure (namedCandidates store (parts.namedRows.map fun (r : Ixon.NamedRow) => (toString r.name, r.addr)))
    pure { parts, setup, pre, hints, inventory, anon : PreparedInput }
  let elapsed := (← IO.monoMsNow) - start
  return result.map fun p => { p with prepareMs := elapsed }

def PreparedInput.record (p : PreparedInput) (a : Address) : Except ReadError Ixon.Constant :=
  match p.parts.env.consts[a]? with
  | some lc => lc.get.mapError (.malformed ·)
  | none => match p.setup.store[a]? with
    | some c => .ok c | none => .error (.malformed "record is missing")

structure CheckReport where
  targets : Array TargetResult
  execution : Execution
  omitted : Array String
  records : Nat
  inputMs : Nat
  prepareMs : Nat
  elapsedMs : Nat
  subjectMicros : Nat
  supportMicros : Nat
  readMicros : Nat

def success (outcome : String) : Bool := outcome == "accept" || outcome == "typed"
def CheckReport.targetsCovered (r : CheckReport) : Nat := r.targets.size
def CheckReport.passed (r : CheckReport) : Nat := (r.targets.filter (success ∘ (·.outcome))).size
def CheckReport.typed (r : CheckReport) : Nat := (r.targets.filter (·.outcome == "typed")).size
def CheckReport.failures (r : CheckReport) : Array (String × String) :=
  (r.targets.filter (!success ·.outcome)).map fun t => (t.target.label, s!"{t.outcome}: {t.reason}")

/-- No persistent marking: each call owns fresh serial checker/reader state.
The exact cached tier declarations and onRead values supply key observations. -/
def runMode (p : PreparedInput) (cfg : CheckCfg) (plan : Plan) (cx : Ctx md) (ev : Evidences md)
    (erase : Key md → Key .anon) (decorate : Read md → Read md) (decorateTier : Tier.TierDecl md → Tier.TierDecl md)
    (spell : Key md → String) (prepareStart : Nat) (failOut? : Option IO.FS.Handle) :
    IO (Except DriverError CheckReport) := do
  let mut tiers : Std.HashMap Address (Except ReadError (Tier.TierDecl md)) := {}
  let mut observed : Produced := {}
  for a in plan.addresses do
    if (p.setup.store[a]?).any (fun c => Ix.Kernel.Admission.isTierInfo c.info) then
      let d := (p.record a >>= fun c => (readTierAt cx a c).getD (.error (.malformed "missing tier declaration"))).map decorateTier
      tiers := tiers.insert a d
      if let .ok decl := d then observed := noteTier erase observed a decl
  let seen ← IO.mkRef observed
  let actual ← IO.mkRef (tiers.fold (init := {}) fun (set : Std.HashSet Address) a _ => set.insert a)
  let src : LoopSource (State md) md := {
    view := p.setup.view, init := pure {}, commit := fun st _ rd => st.commit rd,
    read := fun st a => (p.record a >>= readRecord cx st a).map decorate,
    tier := some fun _ a => tiers[a]? }
  let byProducer := plan.targets.foldl (fun (m : Std.HashMap Address (List Target)) t =>
    m.insert t.producer (t :: m.getD t.producer [])) {}
  let prepareMs := (← IO.monoMsNow) - prepareStart
  let start ← IO.monoMsNow
  let completed ← IO.mkRef (0, 0)
  let stop ← IO.mkRef false
  let reporter ← IO.asTask (prio := .dedicated) do
    if cfg.silent || cfg.progressMs == 0 then return
    let mut last := start
    while !(← stop.get) do
      IO.sleep (min 100 cfg.progressMs).toUInt32
      let now ← IO.monoMsNow
      if now - last ≥ cfg.progressMs && !(← stop.get) then
        let (subjects, records) ← completed.get
        IO.eprintln s!"{cfg.tag} {subjects}/{plan.targets.size} subjects, {records} record rows, elapsed {(now - start) / 1000}s"
        last := now
  try
    let run ← runRecords src ev (fun _ => #[]) plan.addresses { workers := some cfg.workers, tier := true }
      (spell := spell)
      (onRead := fun a r _ => do
        actual.modify (·.insert a)
        if let .ok rd := r then seen.modify (noteRead erase · a rd))
      (emit := fun row => do
        let selected := (byProducer.getD row.address []).reverse
        completed.modify fun (n, r) => (n + selected.length, r + 1)
        if selected.isEmpty && cfg.verbose && !cfg.silent && !success row.outcome then
          IO.eprintln s!"{cfg.tag} support #{row.address}: {row.outcome} {row.reason}"
        for t in selected do
          let covered := (← seen.get).getD row.address {} |>.contains t.key
          let outcome := if success row.outcome && !covered then "decline" else row.outcome
          let reason := if success row.outcome && !covered then "selected key was not emitted" else row.reason
          if !cfg.silent && (cfg.verbose || !success outcome || (cfg.slowMs > 0 && row.micros / 1000 ≥ cfg.slowMs)) then
            IO.eprintln s!"{cfg.tag} {t.label}: {outcome} {reason} ({row.micros / 1000}ms)"
          if let some h := failOut? then
            if !success outcome then
              h.putStrLn s!"\n# {outcome}: {(reason.replace "\n" " | ").replace "\r" ""}"
              h.putStrLn t.fileLabel
              h.flush)
    let targets ← match results plan run.rows (← seen.get) with
      | .ok xs => pure xs | .error e => return .error (targetError e)
    let actual ← actual.get
    let subject := run.rows.foldl (fun n r => if actual.contains r.address && byProducer.contains r.address then n + r.micros else n) 0
    let total := run.rows.foldl (fun n r => if actual.contains r.address then n + r.micros else n) 0
    let reads := run.rows.foldl (fun n r => if actual.contains r.address then n + r.readMicros else n) 0
    let elapsedMs := (← IO.monoMsNow) - start
    return .ok {
      targets, execution := run.execution, omitted := plan.omitted, records := actual.size
      inputMs := p.prepareMs, prepareMs, elapsedMs, subjectMicros := subject
      supportMicros := total - subject, readMicros := reads }
  finally
    stop.set true
    let _ ← IO.wait reporter
    pure ()

/-- Preparation is shareable; every run owns ordinary reclaimable checker
state. Tier support explicitly chooses one effective worker. -/
def runPrepared (p : PreparedInput) (cfg : CheckCfg) (selection : Selection)
    (maxGroups : Option Nat := none) (failOut? : Option IO.FS.Handle := none) : IO (Except DriverError CheckReport) := do
  if cfg.workers == 0 then return .error (.usage "--workers must be greater than zero")
  try
    let start ← IO.monoMsNow
    let plan ← match select p.setup (p.pre.records.map fun (a, c) => owner a c) p.inventory selection maxGroups with
      | .ok v => pure v | .error e => return .error (targetError e)
    if !cfg.silent then IO.eprintln s!"{cfg.tag} {plan.targets.size} selected subjects, {plan.producers.size} producers, {plan.addresses.size} support/prelude records; workers requested {cfg.workers}, effective 1 (serial typing tier); {plan.omitted.size} omitted by cap"
    let job : IO (Except DriverError CheckReport) ← if p.anon then
      pure (runMode p cfg plan p.setup.cx p.setup.evidence id id id toString start failOut?)
    else do
      let mut included := plan.addresses.foldl (fun (s : Std.HashSet Address) a => s.insert a) {}
      for a in plan.addresses do
        for r in recursorRecords p.setup.cx.index a do included := included.insert r
      let mut env := p.parts.env
      for row in p.parts.namedRows do
        if (p.setup.store[row.addr]?).any (fun c => included.contains (owner row.addr c)) then
          let named ← IO.ofExcept (row.materialize p.parts.backing p.parts.nameRev)
          env := { env with named := env.named.insert row.name named }
      let pre : Prelude .meta ← IO.ofExcept (preludeFor p.setup.table)
      let (cx, ev) := metaContext p.setup (env.blobs[·]?) p.setup.table pre p.hints.lookup
      let display := displayTable env cx
      let nc : Ix.KernelDisplay.NameCx := ⟨env.names, Ix.KernelDisplay.metaTable env cx⟩
      pure (runMode p cfg plan cx ev (fun k => Key.map (md := .meta) (md' := .anon) id k)
        (fun rd => (Ix.KernelDisplay.nameRead nc (withDisplay display rd)).1)
        (fun d => (nameTier nc d {}).1) (spellWith display) start failOut?)
    if cfg.stackBytes != 0 then Ix.Tc.setLeanThreadStackSize (USize.ofNat cfg.stackBytes)
    IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) job))
  catch e => return .error (.infrastructure e.toString)

def runMetaCheck (bytes : ByteArray) (cfg : CheckCfg) (selection : Selection)
    (maxGroups : Option Nat := none) (failOut? : Option IO.FS.Handle := none) : IO (Except DriverError CheckReport) := do
  match ← prepareInput bytes with
  | .error e => return .error e | .ok p => runPrepared p cfg selection maxGroups failOut?
def runAnonCheck (bytes : ByteArray) (cfg : CheckCfg) (selection : Selection)
    (maxGroups : Option Nat := none) (failOut? : Option IO.FS.Handle := none) : IO (Except DriverError CheckReport) := do
  match ← prepareInput bytes true with
  | .error e => return .error e | .ok p => runPrepared p cfg selection maxGroups failOut?

/-- First supplied setting wins; malformed values are usage errors. -/
def envNat (names : List String) (dflt : Nat) : IO (Except DriverError Nat) := do
  for name in names do
    if let some v ← IO.getEnv name then
      return match v.trimAscii.toString.toNat? with
        | some n => .ok n | none => .error (.usage s!"{name} requires a natural number")
  return .ok dflt

def defaultWorkers : IO Nat := do
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS").bind (·.trimAscii.toString.toNat?) then return max 1 n
  match ← (IO.Process.output { cmd := "nproc" }).toBaseIO with
  | .ok out => if out.exitCode != 0 then return 8 else return (out.stdout.trimAscii.toString.toNat?).map (max 1) |>.getD 8
  | .error _ => return 8

def checkConfig (p : Cli.Parsed) : IO (Except DriverError CheckCfg) := do
  if p.hasFlag "no-verify" then return .error (.usage "--no-verify is unsupported by IxC; byte authentication is required")
  if ((p.flag? "clear-every").map (·.as! Nat)).getD 0 != 0 then return .error (.usage "--clear-every must be 0; Ix.Tc cache controls do not apply to IxC")
  for name in ["IX_TC_STEP_TRACE", "IX_TC_STATS", "IX_TC_NO_ACCEL", "IX_KERNEL_CHECK_ACTIVE_SLOW_MS"] do
    if let some v ← IO.getEnv name then
      if v.trimAscii.toString.toNat? != some 0 then return .error (.usage s!"{name} is unsupported by IxC; unset it or use 0")
  if (← IO.getEnv "IX_TC_DEBUG_CONST").any (!·.trimAscii.isEmpty) then return .error (.usage "IX_TC_DEBUG_CONST is unsupported by IxC")
  if (← IO.getEnv "IX_MAX_REC_FUEL").isSome then return .error (.usage "IX_MAX_REC_FUEL cannot override IxC's checker limits")
  let workers ← match (p.flag? "workers").map (·.as! Nat) with | some n => pure n | none => defaultWorkers
  if workers == 0 then return .error (.usage "--workers must be greater than zero")
  let progress ← envNat ["IX_KERNEL_CHECK_PROGRESS_MS", "IX_PROGRESS_MS"] 2000
  let slow ← envNat ["IX_KERNEL_CHECK_SLOW_MS"] 7000
  return do pure { workers, verbose := p.hasFlag "verbose", progressMs := ← progress, slowMs := ← slow }

def runCheckLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.positionalArg? "path" | p.printError "error: must specify <path>"; return 2
  let cfg ← match ← checkConfig p with
    | .ok c => pure c | .error e => IO.eprintln e.message; return e.exitCode
  try
    let only ← ConstsFile.gather p
    let selection := if (p.flag? "consts").isSome || (p.flag? "consts-file").isSome then Selection.only only else .all
    let cap := (p.flag? "max").map (·.as! Nat)
    let bytes ← IO.FS.readBinFile (path.as! String)
    let out ← match p.flag? "fail-out" with
      | none => pure none
      | some f => do
        let h ← IO.FS.Handle.mk (f.as! String) .write
        h.putStrLn s!"# ix check-lean failures\n# env: {path.as! String}"
        pure (some h)
    IO.println s!"Running IxC record check ({if p.hasFlag "anon" then "anon" else "meta"} mode)"
    let result ← if p.hasFlag "anon" then runAnonCheck bytes cfg selection cap out else runMetaCheck bytes cfg selection cap out
    match result with
    | .error e =>
      IO.eprintln s!"[check-lean] {e.message}"
      if let some h := out then
        h.putStrLn s!"# {e.message.replace "\n" " | "}"
        if let .refused label _ := e then h.putStrLn (if label.startsWith "#" then (label.drop 1).toString else label)
        h.flush
      return e.exitCode
    | .ok report =>
      if let some h := out then h.putStrLn s!"\n# total failures: {report.failures.size}"; h.flush
      IO.println s!"[check-lean] {report.passed}/{report.targetsCovered} subjects passed ({report.typed} typed only), {report.records} checked/read records"
      IO.println s!"[check-lean] authenticated input {report.inputMs}ms; run preparation {report.prepareMs}ms; selected checker {report.subjectMicros / 1000}ms; support checker {report.supportMicros / 1000}ms; reading {report.readMicros / 1000}ms; run {report.elapsedMs}ms"
      IO.println s!"##check-lean## {report.elapsedMs} {report.passed} {report.failures.size} {report.targetsCovered}"
      return if report.failures.isEmpty then 0 else Ix.Benchmark.Results.exitRejected
  catch e => IO.eprintln s!"[check-lean] {e}"; return 1

end Ix.Cli.CheckLeanCmd

open Ix.Cli.CheckLeanCmd in
def checkLeanCmd : Cli.Cmd := `[Cli|
  "check-lean" VIA runCheckLeanCmd;
  "Check authenticated .ixe declarations with IxC (meta by default; serial typing tier)"
  FLAGS:
    anon; "Anonymous keys and #hex display labels"
    workers : Nat; "Requested workers (>0); the tier-capable path reports effective 1"
    "fail-out" : String; "Write failing selected labels in consts-file format"
    consts : String; "Comma-separated selected names or anonymous addresses"
    "consts-file" : String; "Selected labels, one per line; # introduces comments"
    max : Nat; "Select the first N producer groups; all dependencies/prelude remain"
    "clear-every" : Nat; "Compatibility option: only 0 is supported by IxC"
    "no-verify"; "Unsupported: IxC requires byte authentication"
    verbose; "Print one outcome per selected subject"
  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
