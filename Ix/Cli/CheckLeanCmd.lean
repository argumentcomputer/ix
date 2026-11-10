module

public import Cli
public import Ix.Common
public import Ix.Cli.CheckLeanTargets
public import Ix.KernelCheck.Run
public import Ix.KernelCheck.Stream
public import Ix.HostAdmission
public import Ix.RoleBinding.Compile
public import Ix.RoleBinding.UserAxioms
public import Ix.Store
public import Ix.Runtime.Thread
public import Ix.Benchmark.Results

public section

/-! The IxCK host record checker behind check-lean. Both modes authenticate
input bytes. A whole-artifact run of a bound artifact also runs the certified
logical or tiered entry (`Ix.HostAdmission.certify`) and reports its host
statement. Selected/capped runs report only their selected declarations;
actual emitted-key coverage is required in both modes. A run that asks for the
whole artifact of an artifact with no role binding cannot run the whole-artifact
entry: it says so and exits with `exitPartial`, even when every declaration
passed.

Checking is strict: a safe axiom other than Lean's standard three declines.
`--allow-user-axioms` admits such axioms (`Key.isCustomAxiomEligible`) in the
declaration checks, and a whole run runs the kernel's entry that admits them
once, which lists the user axioms among the declarations. With none listed,
that run is the certified entry's (T1) and the host statement is issued. With
some, the run lists them, issues no host statement and exits with
`exitConditional`; so does a selected run whose declaration checks read one. -/

namespace Ix.Cli.CheckLeanCmd

open Ix.Kernel Ix.Kernel.Reader Benchmarks.Kernel.CheckIxeStep
open Benchmarks.Kernel.CheckIxeMeta
open Ix.Cli.CheckLeanTargets

inductive DriverError where
  | usage (message : String)
  | infrastructure (message : String)
  | refused (label message : String)
  /-- Aggregate refusal: there is no declaration selector for a fail file. -/
  | artifact (message : String)

def DriverError.message : DriverError → String
  | .usage s | .infrastructure s | .artifact s => s | .refused n s => s!"{n}: {s}"
def DriverError.exitCode : DriverError → UInt32
  | .usage _ => 2 | .infrastructure _ => 1 | .refused .. | .artifact _ => 3

def targetError : CheckLeanTargets.Error → DriverError
  | .selector s => .usage s
  | .input n e => .refused n s!"{(readOutcome e).1}: {(readOutcome e).2}"
  | .coverage n s => .refused n s!"decline: {s}"

/-- Whether a selection asks for every declaration. -/
def _root_.Ix.Cli.CheckLeanTargets.Selection.isWhole : Selection → Bool
  | .all => true
  | .only _ => false

structure CheckCfg where
  workers : Nat := 1
  verbose : Bool := false
  silent : Bool := false
  allowDeclined : Bool := false
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
  bound : Bool := false
  hasTier : Bool := false
  /-- `--allow-user-axioms`: the declaration checks admit user axioms, and a
  whole run takes the entry that admits them (`checkWhole`). Set only by
  `prepareInput`, after the binding has passed the kernel's role-table check
  (`UserAxioms.requireAxiomRoles`). -/
  allowUserAxioms : Bool := false
  prepareMs : Nat := 0

/-- Explicit coverage limits for the complete artifact entry, shared by both
display modes. These are the host's whole-library byte/expansion bounds. -/
def artifactLimits : Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- Authenticate first; retain raw windows and reader skeletons. No metadata
field is rebuilt through an incomplete Env literal. A bound artifact's binding
is admitted with its records (`Artifact.prepareRecords`). In meta mode its
published names must agree with the binding (`RoleBinding.Compile.roleBindingError`,
which the compiler's `finalize` also runs). With `allowUserAxioms` the binding
must pass the kernel's role-table check for user axioms
(`Admission.admitAxiomPolicy .allowUser`, through `UserAxioms.requireAxiomRoles`:
`sorryAx`, `propext` and `Classical.choice` bound) before any declaration is
checked, since the record-by-record checks never reach admission; an artifact
with no binding is refused. -/
def prepareInput (bytes : ByteArray) (anon : Bool := false) (allowUserAxioms : Bool := false) :
    IO (Except DriverError PreparedInput) := do
  let start ← IO.monoMsNow
  let result : Except DriverError PreparedInput ← IO.lazyPure fun _ => do
    let parts ← (Ixon.deEnvVerifiedLazy bytes).mapError DriverError.infrastructure
    let boundInput ← if parts.env.roleBinding.isSome then
        (Ix.RoleBinding.Artifact.prepareRecords parts.env artifactLimits).map some
          |>.mapError (DriverError.artifact ∘ toString)
      else pure none
    if allowUserAxioms then
      (Ix.RoleBinding.UserAxioms.requireAxiomRoles parts.env.roleBinding).mapError
        fun e => DriverError.artifact s!"artifact: decline: --allow-user-axioms: {e}"
    if !anon && boundInput.isSome && !parts.namedRows.isEmpty then
      let named ← parts.materializeAllNamed.mapError DriverError.infrastructure
      if let some e := Ix.RoleBinding.Compile.roleBindingError named then
        throw (.artifact s!"artifact: role binding: {e}")
    let (table, pre) ← match boundInput with
      | some input => pure (input.prepared.table, input.prepared.pre)
      | none => do
        let table ← defaultTable.mapError DriverError.infrastructure
        let pre ← (preludeFor table : Except String (Prelude .anon)).mapError DriverError.infrastructure
        pure (table, pre)
    -- Evidence is read through this store, so a bound theorem and its owner
    -- must retain their real bodies instead of the diagnostic skeleton.
    let mut proofRecords : Std.HashSet Address := {}
    if boundInput.isSome then
      for (_, entries) in table.evidence do
        for entry in entries do
          if let .proof address := entry then
            proofRecords := proofRecords.insert address
            if let some lazy := parts.env.consts[address]? then
              let record ← lazy.get.mapError DriverError.infrastructure
              proofRecords := proofRecords.insert (owner address record)
    let mut store : RecordStore := {}
    let mut literals := #[]
    for (a, lc) in parts.env.consts do
      let c ← lc.get.mapError DriverError.infrastructure
      let (nat, str) := literalKinds c
      if nat || str then literals := literals.push (a, Benchmarks.Kernel.CheckIxeStream.literalStandIn nat str)
      store := store.insert a (if proofRecords.contains a then c else Benchmarks.Kernel.CheckIxeStream.skeleton c)
    let hints := Hints.ofStore store parts.env.anonHints
    let setup := Benchmarks.Kernel.CheckIxeStep.setup store (parts.env.blobs[·]?) table pre hints.lookup
      (literals := some literals)
    let inventory ← if anon then (anonymousCandidates store).mapError targetError else
      pure (namedCandidates store (parts.namedRows.map fun (r : Ixon.NamedRow) => (toString r.name, r.addr)))
    pure { parts, setup, pre, hints, inventory, anon, bound := boundInput.isSome
           hasTier := (boundInput.map (·.hasTier)).getD false, allowUserAxioms : PreparedInput }
  let elapsed := (← IO.monoMsNow) - start
  return result.map fun p => { p with prepareMs := elapsed }

def PreparedInput.record (p : PreparedInput) (a : Address) : Except ReadError Ixon.Constant :=
  match p.parts.env.consts[a]? with
  | some lc => lc.get.mapError (.malformed ·)
  | none => match p.setup.store[a]? with
    | some c => .ok c | none => .error (.malformed "record is missing")

/-- The whole-artifact entry that ran and what it accepted. `conditional` is
the verdict of the entry `--allow-user-axioms` runs (`Artifact.checkConditional`,
or `checkTieredConditional` with its tier census in `typed`) when the kernel
lists user axioms among the declarations: no theorem covers it and it issues no
host statement, and it holds only under `axioms`, those the kernel listed. -/
inductive ArtifactAdmission where
  | logical (records : Nat)
  | tiered (records typed : Nat)
  | conditional (records : Nat) (typed : Option Nat) (axioms : Array Address)
  deriving BEq, Repr

structure CheckReport where
  targets : Array TargetResult
  rows : Array Row := #[]
  execution : Execution
  omitted : Array String
  records : Nat
  inputMs : Nat
  prepareMs : Nat
  elapsedMs : Nat
  subjectMicros : Nat
  supportMicros : Nat
  readMicros : Nat
  bound : Bool := false
  /-- A whole run of a bound artifact: the binding's roles, `(admitted,
  refused)`, a role refused when this run refused its record. -/
  roles : Option (Nat × Nat) := none
  /-- The user axioms whose records the declaration checks read and accepted
  (`--allow-user-axioms`, `admittedUserAxioms`). -/
  userAxioms : Array Address := #[]
  artifactAdmission : Option ArtifactAdmission := none
  hostStatement : Option Ix.HostAdmission.Statement := none
  artifactMs : Nat := 0

/-- Whether a run of `selection`, capped at `maxGroups`, runs the
whole-artifact entry: a bound artifact, every declaration, no cap. An
unresolved thin artifact declines; there is no external-store fallback. -/
def wholeEntry (p : PreparedInput) (selection : Selection) (maxGroups : Option Nat) :
    Except DriverError Bool := do
  unless p.bound && selection.isWhole && maxGroups.isNone do return false
  unless p.parts.env.assumptions.isEmpty do
    throw (.artifact "artifact: decline: thin artifact assumptions require explicit resolution")
  return true

/-- The verdict of a certified whole-artifact run. -/
def ArtifactAdmission.ofRun {artifact : Ixon.Env} {limits : Admission.Limits} :
    Ix.HostAdmission.Run artifact limits → ArtifactAdmission
  | .logical receipt => .logical receipt.prepared.records.length
  | .tiered receipt => .tiered receipt.prepared.records.length receipt.tier.length

/-- A certified run's verdict and its host statement, derived from the run as
`HostAdmission.certify` derives it (`HostAdmission.statementOf`). -/
def certifiedVerdict (artifact : Ixon.Env) (run : Ix.HostAdmission.Run artifact artifactLimits) :
    Except DriverError (Option (ArtifactAdmission × Option Ix.HostAdmission.Statement)) := do
  let statement ← (Ix.HostAdmission.statementOf artifact artifactLimits run).mapError
    (DriverError.artifact ∘ toString)
  return some (ArtifactAdmission.ofRun run, some statement)

/-- Route from authenticated record headers before either entry runs. A
failure never selects another checker. Selected/capped runs make no complete
artifact claim. Without `allowUserAxioms` the certified entry runs
(`HostAdmission.certify`). With it, the entry that admits user axioms runs once
(`Artifact.checkConditional`, `checkTieredConditional`: the kernel's
`Admission.checkBytesUnder .allowUser` and its tiered form), and the kernel's
list of the user axioms among the declarations it ran over chooses the verdict:
with none, its receipt is the certified entry's (T1,
`ReceiptConditional.toReceipt`, `TierReceiptConditional.toTierReceipt`) and the
host statement is derived from it as `certify` derives it; with some, the
verdict is conditional on them and there is no statement. -/
def checkWhole (p : PreparedInput) (selection : Selection) (maxGroups : Option Nat) :
    Except DriverError (Option (ArtifactAdmission × Option Ix.HostAdmission.Statement)) := do
  unless (← wholeEntry p selection maxGroups) do return none
  let artifact := p.parts.env
  unless p.allowUserAxioms do
    let ⟨statement, checked⟩ ← (Ix.HostAdmission.certify artifact artifactLimits).mapError
      (DriverError.artifact ∘ toString)
    return some (ArtifactAdmission.ofRun checked.run, some statement)
  if p.hasTier then
    let receipt ← (Ix.RoleBinding.Artifact.checkTieredConditional artifact artifactLimits).mapError
      (DriverError.artifact ∘ toString)
    match noAxioms : receipt.axioms with
    | [] => certifiedVerdict artifact (.tiered (receipt.toTierReceipt noAxioms))
    | _ :: _ =>
      return some (.conditional receipt.prepared.records.length (some receipt.tier.length)
        (Ix.RoleBinding.UserAxioms.addresses receipt.axioms), none)
  else
    let receipt ← (Ix.RoleBinding.Artifact.checkConditional artifact artifactLimits).mapError
      (DriverError.artifact ∘ toString)
    match noAxioms : receipt.axioms with
    | [] => certifiedVerdict artifact (.logical (receipt.toReceipt noAxioms))
    | _ :: _ =>
      return some (.conditional receipt.prepared.records.length none
        (Ix.RoleBinding.UserAxioms.addresses receipt.axioms), none)

def success (outcome : String) : Bool := outcome == "accept" || outcome == "typed"
def CheckReport.targetsCovered (r : CheckReport) : Nat := r.targets.size
def CheckReport.passed (r : CheckReport) : Nat := (r.targets.filter (success ∘ (·.outcome))).size
def CheckReport.typed (r : CheckReport) : Nat := (r.targets.filter (·.outcome == "typed")).size
def CheckReport.failures (r : CheckReport) : Array (String × String) :=
  (r.targets.filter (!success ·.outcome)).map fun t => (t.target.label, s!"{t.outcome}: {t.reason}")
/-- Whether any checked target or record in the closure was rejected by the
kernel or reader (`outcome == "reject"`), as opposed to declined as outside
`IxCK`'s fragment (`"decline"`) or blocked solely by a declined dependency. -/
def CheckReport.hasReject (r : CheckReport) : Bool :=
  r.targets.any (·.outcome == "reject") || r.rows.any (·.outcome == "reject")

/-- The user axioms a run's verdict is conditional on: the conditional
whole-artifact entry's, otherwise those its declaration checks read and accepted. -/
def CheckReport.conditionalOn (r : CheckReport) : Array Address :=
  match r.artifactAdmission with
  | some (.conditional _ _ axioms) => axioms
  | _ => r.userAxioms

/-- The binding's roles after a whole run's declaration checks: `(admitted,
refused)`, where a role is refused when this run refused its record. -/
def roleCounts (p : PreparedInput) (rows : Array Row) : Nat × Nat :=
  let failed : Std.HashSet Address :=
    rows.foldl (fun s r => if success r.outcome then s else s.insert r.address) {}
  let refused := p.setup.table.bound.filter fun (_, a) =>
    (p.setup.store[a]?).any fun c => failed.contains (owner a c)
  (p.setup.table.bound.size - refused.size, refused.size)

/-- **The exit status of a partial check**: every declaration checked passed, but the
whole-artifact admission the run asked for did not run, because the artifact carries
no role binding. Distinct from success (0), a usage error (2) and a refusal (3). -/
def exitPartial : UInt32 := 4

/-- **The exit status of a conditional run**: every declaration checked passed
with user axioms admitted (`--allow-user-axioms`), so the verdict holds only
under the axioms the run lists: a whole artifact accepted by the uncertified
conditional entry, or a selected run whose declaration checks read a user
axiom. Distinct from success (0), an infrastructure failure (1), a usage
error (2), a refusal (3) and a partial check (`exitPartial`). -/
def exitConditional : UInt32 := 5

/-- What a completed run did not check, if anything: a selected or capped run covers
only its selection; a run that asked for the whole artifact (`wholeRequested`) of an
artifact with no role binding covers only the per-declaration checks; `--allow-declined`
checks records only and makes no whole-artifact admission claim. -/
def coverageNotice (report : CheckReport) (wholeRequested : Bool)
    (allowDeclined : Bool := false) : Option String :=
  match report.artifactAdmission with
  | some _ => none
  | none =>
    if allowDeclined then
      some "[check-lean] record check (--allow-declined); no whole-artifact receipt"
    else if report.bound then
      if wholeRequested then
        some "[check-lean] whole-artifact admission did not run because declaration checks failed"
      else some "[check-lean] selected checking only; no whole-artifact receipt"
    else if wholeRequested then
      some s!"[check-lean] partial check: the artifact carries no role binding, so the \
whole-artifact admission did not run; only the per-declaration checks ran \
({report.targetsCovered} subjects)"
    else
      some "[check-lean] selected checking only; the artifact carries no role binding, so no \
whole-artifact admission could run"

/-- The exit status of a completed run: a refusal (`exitRejected`) when a
checked declaration failed (or, under `allowDeclined`, when any target or
record was `"reject"`ed); otherwise a usage error when a host statement was
asked for (`hostRequested`) and the run issued none; otherwise `exitPartial`
when the whole artifact was asked for (without `allowDeclined`) and its
admission did not run; otherwise `exitConditional` when the verdict is
conditional on user axioms; else 0. -/
def runExit (report : CheckReport) (wholeRequested : Bool) (hostRequested : Bool := false)
    (allowDeclined : Bool := false) : UInt32 :=
  let failed := if allowDeclined then report.hasReject else !report.failures.isEmpty
  if failed then Ix.Benchmark.Results.exitRejected
  else if hostRequested && report.hostStatement.isNone then Ix.Benchmark.Results.exitUsage
  else if !allowDeclined && wholeRequested && report.artifactAdmission.isNone then exitPartial
  else if !report.conditionalOn.isEmpty then exitConditional
  else 0

/-- The results-row status of a completed run (`Ix.Benchmark.Results`): its
exit status (`runExit`, no host statement asked for) by name. `rejected` (3),
`partial` (`exitPartial`), `conditional` (`exitConditional`), else `ok`. -/
def runStatus (report : CheckReport) (wholeRequested : Bool)
    (allowDeclined : Bool := false) : String :=
  let code := runExit report wholeRequested (allowDeclined := allowDeclined)
  if code == Ix.Benchmark.Results.exitRejected then "rejected"
  else if code == exitPartial then "partial"
  else if code == exitConditional then "conditional"
  else "ok"

/-- The user axioms a run's declaration checks admitted: of those they
read (`read`), the ones whose records they accepted (`rows`), by address. A
record read and then blocked, declined or rejected admits nothing; this is how
`kernel-check-ixe` lists them. -/
def admittedUserAxioms (read : Std.HashSet Address) (rows : Array Row) : Array Address :=
  let accepted := rows.foldl (init := ({} : Std.HashSet Address)) fun s r =>
    if r.outcome == "accept" then s.insert r.address else s
  (read.toArray.filter accepted.contains).qsort (compare · · == .lt)

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
  let userAxioms ← IO.mkRef ({} : Std.HashSet Address)
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
    let run ← runRecords src ev (fun _ => #[]) plan.addresses
      { workers := some cfg.workers, tier := true, allowUserAxioms := p.allowUserAxioms }
      (spell := spell)
      (onRead := fun a r _ => do
        actual.modify (·.insert a)
        if let .ok rd := r then
          seen.modify (noteRead erase · a rd)
          if p.allowUserAxioms then
            for d in rd.decls do
              if let some cv := d.userAxiom? then
                if let .id address := erase cv.name then userAxioms.modify (·.insert address))
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
      targets, rows := run.rows, execution := run.execution, omitted := plan.omitted, records := actual.size
      inputMs := p.prepareMs, prepareMs, elapsedMs, subjectMicros := subject
      supportMicros := total - subject, readMicros := reads
      userAxioms := admittedUserAxioms (← userAxioms.get) run.rows }
  finally
    stop.set true
    let _ ← IO.wait reporter
    pure ()

/-- Preparation is shareable; every run owns ordinary reclaimable checker
state. Tier support explicitly chooses one effective worker. The declaration
checks run first; the whole-artifact entry (`checkWhole`) runs only when they
all pass. -/
def runPrepared (p : PreparedInput) (cfg : CheckCfg) (selection : Selection)
    (maxGroups : Option Nat := none) (failOut? : Option IO.FS.Handle := none) : IO (Except DriverError CheckReport) := do
  if cfg.workers == 0 then return .error (.usage "--workers must be greater than zero")
  try
    let start ← IO.monoMsNow
    let plan ← match select p.setup (p.pre.records.map fun (a, c) => owner a c) p.inventory selection maxGroups with
      | .ok v => pure v | .error e => return .error (targetError e)
    -- an unresolved thin whole run declines before any declaration is checked
    let whole ← match wholeEntry p selection maxGroups with
      | .ok w => pure w | .error e => return .error e
    if !cfg.silent then IO.eprintln s!"{cfg.tag} {plan.targets.size} selected subjects, {plan.producers.size} producers, {plan.addresses.size} support/prelude records; workers requested {cfg.workers}, effective 1 (serial typing tier); {plan.omitted.size} omitted by cap"
    let declarations : IO (Except DriverError CheckReport) ← if p.anon then
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
      let pre : Prelude .meta ← IO.ofExcept <| if p.bound then do
          let pre ← readPrelude p.setup.table p.pre.records #[] p.pre.blobs
          checkPreludeShape pre
          checkFallbackRecursors pre
          pure pre
        else preludeFor p.setup.table
      let (cx, ev) := metaContext p.setup (env.blobs[·]?) p.setup.table pre p.hints.lookup
      let display := displayTable env cx
      let nc : Ix.KernelDisplay.NameCx := ⟨env.names, Ix.KernelDisplay.metaTable env cx⟩
      pure (runMode p cfg plan cx ev (fun k => Key.map (md := .meta) (md' := .anon) id k)
        (fun rd => (Ix.KernelDisplay.nameRead nc (withDisplay display rd)).1)
        (fun d => (nameTier nc d {}).1) (spellWith display) start failOut?)
    let run : IO (Except DriverError CheckReport) := do
      match ← declarations with
      | .error e => return .error e
      | .ok report =>
        let report := { report with
          bound := p.bound, roles := if whole then some (roleCounts p report.rows) else none }
        if !whole || cfg.allowDeclined || !report.failures.isEmpty then return .ok report
        let started ← IO.monoMsNow
        let admitted ← IO.lazyPure fun _ => checkWhole p selection maxGroups
        let elapsed := (← IO.monoMsNow) - started
        match admitted with
        | .error e => return .error e
        | .ok admission =>
          return .ok { report with
            artifactAdmission := admission.map (·.1), hostStatement := admission.bind (·.2)
            artifactMs := elapsed }
    if cfg.stackBytes != 0 then Ix.Runtime.setLeanThreadStackSize (USize.ofNat cfg.stackBytes)
    IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) run))
  catch e => return .error (.infrastructure e.toString)

def runMetaCheck (bytes : ByteArray) (cfg : CheckCfg) (selection : Selection)
    (maxGroups : Option Nat := none) (failOut? : Option IO.FS.Handle := none) : IO (Except DriverError CheckReport) := do
  match ← prepareInput bytes with
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
  let workers ← match (p.flag? "workers").map (·.as! Nat) with | some n => pure n | none => defaultWorkers
  if workers == 0 then return .error (.usage "--workers must be greater than zero")
  let progress ← envNat ["IX_KERNEL_CHECK_PROGRESS_MS", "IX_PROGRESS_MS"] 2000
  let slow ← envNat ["IX_KERNEL_CHECK_SLOW_MS"] 7000
  return do pure {
    workers, verbose := p.hasFlag "verbose", allowDeclined := p.hasFlag "allow-declined"
    progressMs := ← progress, slowMs := ← slow }

private def csvField (s : String) : String :=
  if s.any (fun c => c == ',' || c == '"')
  then "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

/-- One CSV row per record, its first row when runs repeat it (the per-name
runs share support records). -/
private def writePerConstCsv (p : PreparedInput) (rows : Array Row) (outCsv : String) : IO Unit := do
  let mut named : Std.HashMap String String := {}
  for r in p.parts.namedRows do
    let key := toString r.addr
    if !named.contains key then
      named := named.insert key (toString r.name)
  let mut viaPrj : Std.HashMap String String := {}
  for (caddr, c) in p.setup.store do
    let blk? := match c.info with
      | .iPrj prj => some prj.block
      | .cPrj prj => some prj.block
      | .rPrj prj => some prj.block
      | .dPrj prj => some prj.block
      | _ => none
    let some blk := blk? | continue
    let key := toString blk
    if !viaPrj.contains key then
      if let some n := named[toString caddr]? then
        viaPrj := viaPrj.insert key n
  let mut out := "name,addr,consts,nanos,heartbeats,subst,whnf,def_eq,nat_arith,intern,cost\n"
  let mut written : Std.HashSet Address := {}
  for row in rows do
    if written.contains row.address then continue
    written := written.insert row.address
    let addr := toString row.address
    let name := match named[addr]? with
      | some n => n
      | none => match viaPrj[addr]? with
        | some n => n
        | none => s!"@{addr.take 16}"
    let nanos := (row.micros + row.readMicros) * 1000
    out := out ++ s!"{csvField name},{addr},1,{nanos},0,0,0,0,0,0,0\n"
  IO.FS.writeFile outCsv out

/-- A benchmark results row (`Ix.Benchmark.Results`) for one run. `constants`
is the number of records the run checked or read, whole-artifact or per name;
`throughput` is that count per second of `check-time`. `status` is the run's
exit status by name (`runStatus`): `rejected`, `partial`, `conditional` or `ok`. -/
private def writeJsonReportRow (jsonPath key : String) (report : CheckReport)
    (wholeRequested : Bool) (allowDeclined : Bool := false) : IO Unit := do
  let secs := report.elapsedMs.toFloat / 1000.0
  let tput := if report.elapsedMs > 0
    then report.records.toFloat * 1000.0 / report.elapsedMs.toFloat else 0.0
  let peakRss := (← statusKb "VmHWM:") * 1024
  let status := runStatus report wholeRequested allowDeclined
  Ix.Benchmark.Results.writeRow jsonPath key status
    [ ("constants", Lean.toJson report.records)
    , ("check-time", Ix.Benchmark.Results.jsonRound 3 secs)
    , ("throughput", Ix.Benchmark.Results.jsonRound 2 tput)
    , ("peak-rss", Lean.toJson peakRss) ]

/-- The command line, read once. -/
structure Options where
  path : String
  cfg : CheckCfg
  anon : Bool
  allowUserAxioms : Bool
  /-- Whether `--consts` or `--consts-file` was given (possibly empty). -/
  hasConsts : Bool
  only : Array String
  cap : Option Nat
  json? : Option String
  jsonName? : Option String
  perConst? : Option String
  failOut? : Option String
  hostOut? : Option String
  hostStore : Bool

def Options.selection (o : Options) : Selection := if o.hasConsts then .only o.only else .all
def Options.wholeRequested (o : Options) : Bool := o.selection.isWhole && o.cap.isNone
def Options.hostRequested (o : Options) : Bool := o.hostOut?.isSome || o.hostStore
/-- `--json` with a selection: one full-closure run and row per selected name,
into this results file. -/
def Options.perName? (o : Options) : Option String := if o.hasConsts then o.json? else none

def parseOptions (p : Cli.Parsed) (path : String) : IO (Except DriverError Options) := do
  let cfg ← match ← checkConfig p with | .ok c => pure c | .error e => return .error e
  let string (flag : String) := (p.flag? flag).map (·.as! String)
  let o : Options := {
    path, cfg, anon := p.hasFlag "anon", allowUserAxioms := p.hasFlag "allow-user-axioms"
    hasConsts := (p.flag? "consts").isSome || (p.flag? "consts-file").isSome
    only := (← ConstsFile.gather p), cap := (p.flag? "max").map (·.as! Nat)
    json? := string "json", jsonName? := string "json-name", perConst? := string "per-const"
    failOut? := string "fail-out", hostOut? := string "host-out", hostStore := p.hasFlag "host-store" }
  if o.hostRequested && (o.hasConsts || o.cap.isSome || o.cfg.allowDeclined) then
    return .error (.usage "[check-lean] host statement output requires a complete bound artifact check")
  if o.perName?.isSome && o.failOut?.isSome then
    return .error (.usage "[check-lean] --json per-name rows and --fail-out cannot be combined")
  if o.perName?.isSome && o.only.isEmpty then
    return .error (.usage "[check-lean] explicit selector is empty")
  return .ok o

/-- Print a refusal and record it in the fail-out file; its exit status. -/
def refuse (out : Option IO.FS.Handle) (e : DriverError) : IO UInt32 := do
  IO.eprintln s!"[check-lean] {e.message}"
  if let some h := out then
    h.putStrLn s!"# {e.message.replace "\n" " | "}"
    if let .refused label _ := e then h.putStrLn (if label.startsWith "#" then (label.drop 1).toString else label)
    h.flush
  return e.exitCode

/-- The lines that list the user axioms a verdict is conditional on: each
axiom's address, with its names in meta mode. -/
def conditionalLines (p : PreparedInput) (scope : String) (axioms : Array Address) : Array String := Id.run do
  let mut names : Std.HashMap Address (Array String) := {}
  unless p.anon do
    for r in p.parts.namedRows do
      names := names.insert r.addr ((names.getD r.addr #[]).push (toString r.name))
  let mut lines := #[s!"[check-lean] {scope}: CONDITIONAL on {axioms.size} user axioms:"]
  for a in axioms do
    lines := lines.push <| match names[a]? with
      | some ns => s!"[check-lean]   {a} {" | ".intercalate ns.toList}"
      | none => s!"[check-lean]   {a}"
  return lines

/-- One full-closure run per selected name, each written as its own results
row as soon as it finishes: keyed by the name, after `<json-name>/` when
`--json-name` is given. A name that resolves to no declaration, or whose run
refuses its input, is reported and the remaining names still run. The result
merges the runs, with the unresolved names and the refused ones. -/
def runPerName (o : Options) (p : PreparedInput) (json : String) :
    IO (Except DriverError (CheckReport × Array String × Array String)) := do
  -- anonymous runs also resolve Lean names, through the named inventory
  let index := candidateIndex p.inventory
  let namedIndex := if p.anon then
      candidateIndex (namedCandidates p.setup.store
        (p.parts.namedRows.map fun (r : Ixon.NamedRow) => (toString r.name, r.addr)))
    else index
  let key (name : String) := match o.jsonName? with | some stem => s!"{stem}/{name}" | none => name
  let mut merged : CheckReport := {
    targets := #[], execution := .serialTier (some o.cfg.workers), omitted := #[], records := 0
    inputMs := p.prepareMs, prepareMs := 0, elapsedMs := 0, subjectMicros := 0, supportMicros := 0
    readMicros := 0, bound := p.bound }
  let mut userAxioms : Std.HashSet Address := {}
  let mut unresolved : Array String := #[]
  let mut refused : Array String := #[]
  for name in o.only do
    let found : Except CheckLeanTargets.Error Candidate := match findIndexed index name with
      | .ok c => .ok c
      | .error e => if p.anon then findIndexed namedIndex name else .error e
    match found with
    | .error e =>
      IO.eprintln s!"[check-lean] {name}: unresolved: {(targetError e).message}"
      unresolved := unresolved.push name
    | .ok c =>
      let single := { p with inventory := #[{ c with label := name, fileLabel := name }] }
      match ← runPrepared single o.cfg (.only #[name]) o.cap none with
      | .error (.refused label message) =>
        IO.eprintln s!"[check-lean] {label}: {message}"
        Ix.Benchmark.Results.writeRow json (key name) "rejected" []
        refused := refused.push name
      | .error e => return .error e
      | .ok report =>
        writeJsonReportRow json (key name) report false o.cfg.allowDeclined
        userAxioms := report.userAxioms.foldl (·.insert ·) userAxioms
        merged := { merged with
          targets := merged.targets ++ report.targets, rows := merged.rows ++ report.rows
          execution := report.execution, records := merged.records + report.records
          prepareMs := merged.prepareMs + report.prepareMs, elapsedMs := merged.elapsedMs + report.elapsedMs
          subjectMicros := merged.subjectMicros + report.subjectMicros
          supportMicros := merged.supportMicros + report.supportMicros
          readMicros := merged.readMicros + report.readMicros }
  return .ok ({ merged with userAxioms := userAxioms.toArray.qsort (compare · · == .lt) }, unresolved, refused)

/-- Report a completed run: the fail-out total, the per-record CSV, the role
and whole-artifact verdict lines (or the coverage notice), the host statement,
the summary and machine row, and the whole-run results row. -/
def emitReport (o : Options) (p : PreparedInput) (report : CheckReport) (out : Option IO.FS.Handle) : IO Unit := do
  if let some h := out then h.putStrLn s!"\n# total failures: {report.failures.size}"; h.flush
  if let some csv := o.perConst? then writePerConstCsv p report.rows csv
  if let some (admitted, refused) := report.roles then
    IO.println s!"[check-lean] bound roles: {admitted} admitted, {refused} refused"
  match report.artifactAdmission with
  | some (.logical records) =>
    IO.println s!"[check-lean] whole artifact: logical entry accepted all {records} records ({report.artifactMs}ms)"
  | some (.tiered records typed) =>
    IO.println s!"[check-lean] whole artifact: logical entry and typing tier accepted all {records} records; {typed} tier constants typed only ({report.artifactMs}ms)"
  | some (.conditional records typed axioms) =>
    for line in conditionalLines p "whole artifact" axioms do IO.println line
    let entry := match typed with
      | some n => s!"conditional logical entry and typing tier ({n} tier constants typed only)"
      | none => "conditional logical entry"
    IO.println s!"[check-lean] {entry}: {records} records checked with these axioms admitted; \
uncertified, no host statement ({report.artifactMs}ms)"
  | none =>
    if report.failures.isEmpty && !report.userAxioms.isEmpty then
      for line in conditionalLines p "selected checking" report.userAxioms do IO.println line
    if let some notice := coverageNotice report o.wholeRequested o.cfg.allowDeclined then IO.println notice
  if let some statement := report.hostStatement then
    let hostBytes ← IO.ofExcept statement.bytes
    let address := Address.admissionHash hostBytes
    IO.println s!"[check-lean] host admission statement: {address}"
    if report.failures.isEmpty then
      if let some output := o.hostOut? then
        IO.FS.writeBinFile output hostBytes
      if o.hostStore then
        let stored ← StoreIO.toIO (Store.write hostBytes)
        unless stored == address do throw (IO.userError "stored host statement address differs")
  else if o.hostRequested && report.failures.isEmpty then
    let axioms := report.conditionalOn
    IO.eprintln <| if axioms.isEmpty then
        "[check-lean] host statement output requires a complete bound artifact check"
      else s!"[check-lean] host statement output requires an unconditional whole-artifact \
admission: this run is CONDITIONAL on {axioms.size} user axioms and issues no host statement"
  IO.println s!"[check-lean] {report.passed}/{report.targetsCovered} subjects passed ({report.typed} typed only), {report.records} checked/read records"
  IO.println s!"[check-lean] authenticated input {report.inputMs}ms; run preparation {report.prepareMs}ms; selected checker {report.subjectMicros / 1000}ms; support checker {report.supportMicros / 1000}ms; reading {report.readMicros / 1000}ms; run {report.elapsedMs}ms"
  IO.println s!"##check-lean## {report.elapsedMs} {report.passed} {report.failures.size} {report.targetsCovered}"
  if let some json := o.json? then
    writeJsonReportRow json (o.jsonName?.getD "env") report o.wholeRequested o.cfg.allowDeclined

def runCheckLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.positionalArg? "path" | p.printError "error: must specify <path>"; return 2
  try
    let o ← match ← parseOptions p (path.as! String) with
      | .ok o => pure o | .error e => IO.eprintln e.message; return e.exitCode
    let out ← o.failOut?.mapM fun f => do
      let h ← IO.FS.Handle.mk f .write
      h.putStrLn s!"# ix check-lean failures\n# env: {o.path}"
      pure h
    let bytes ← IO.FS.readBinFile o.path
    IO.println s!"Running IxCK record check ({if o.anon then "anon" else "meta"} mode\
{if o.allowUserAxioms then "; user axioms allowed" else ""}\
{if o.cfg.allowDeclined then "; declined allowed" else ""})"
    let prepared ← match ← prepareInput bytes o.anon o.allowUserAxioms with
      | .ok prep => pure prep
      | .error e => return (← refuse out e)
    if let some json := o.perName? then
      let startAll ← IO.monoMsNow
      let (report, unresolved, refused) ← match ← runPerName o prepared json with
        | .ok r => pure r
        | .error e => return (← refuse out e)
      if let some csv := o.perConst? then writePerConstCsv prepared report.rows csv
      if report.failures.isEmpty && refused.isEmpty && !report.userAxioms.isEmpty then
        for line in conditionalLines prepared "selected checking" report.userAxioms do IO.println line
      let failed := report.failures.size + refused.size
      IO.println s!"[check-lean] {report.passed}/{o.only.size} subjects passed ({report.typed} typed only), \
{failed} failed, {unresolved.size} unresolved"
      IO.println s!"##check-lean## {(← IO.monoMsNow) - startAll} {report.passed} {failed + unresolved.size} {o.only.size}"
      return if !unresolved.isEmpty then Ix.Benchmark.Results.exitUsage
        else if !refused.isEmpty then Ix.Benchmark.Results.exitRejected
        else runExit report false (allowDeclined := o.cfg.allowDeclined)
    match ← runPrepared prepared o.cfg o.selection o.cap out with
    | .error e => return (← refuse out e)
    | .ok report =>
      emitReport o prepared report out
      return runExit report o.wholeRequested o.hostRequested o.cfg.allowDeclined
  catch e => IO.eprintln s!"[check-lean] {e}"; return 1

end Ix.Cli.CheckLeanCmd

open Ix.Cli.CheckLeanCmd in
def checkLeanCmd : Cli.Cmd := `[Cli|
  "check-lean" VIA runCheckLeanCmd;
  "Check authenticated .ixe declarations with IxCK (bound whole inputs use actual artifact admission; meta display by default). Strict: a safe axiom other than propext, Classical.choice and Quot.sound declines unless --allow-user-axioms. Exit 0: everything asked for passed; 3: a declaration failed or the artifact was refused; 4: every declaration passed but the whole artifact, asked for, carries no role binding, so its admission did not run; 5: CONDITIONAL, everything passed only with the listed user axioms admitted (--allow-user-axioms); 2: usage, including a selector naming no declaration and a host statement the run could not issue; 1: infrastructure"
  FLAGS:
    anon; "Anonymous keys and #hex display labels"
    workers : Nat; "Requested workers (>0); the tier-capable path reports effective 1"
    "allow-user-axioms"; "Admit safe axioms beyond the standard three; the role binding must bind sorryAx, propext and Classical.choice. A whole run whose declarations hold any runs the uncertified conditional entry, lists the axioms, issues no host statement and exits 5; so does a selected run that reads one"
    "allow-declined"; "Record-check mode: tolerate declarations outside IxCK's fragment (decline) and their dependents (blocked), failing with exit 3 only on a kernel or reader reject; skips whole-artifact admission and issues no host statement"
    "fail-out" : String; "Write failing selected labels in consts-file format"
    "host-out" : String; "Write the checked whole-artifact host admission statement (certified, unconditional runs only)"
    "host-store"; "Persist the checked host admission statement in the content-addressed store"
    consts : String; "Comma-separated selected names or anonymous addresses"
    "consts-file" : String; "Selected labels, one per line; # introduces comments"
    max : Nat; "Select the first N producer groups; all dependencies/prelude remain"
    "per-const" : String; "Write a per-record attribution CSV (name, addr, consts, nanos, counters, cost) to this path; with --json and a selection, over every per-name run, one row per record"
    json : String; "Write benchmark results rows to this path: the whole-run row keyed by --json-name, or with --consts/--consts-file one full-closure row per selected name; constants is the records checked or read"
    "json-name" : String; "Key of the whole-run --json row (default: env); with a selection, the prefix <json-name>/ of every per-name row key"
    verbose; "Print one outcome per selected subject"
  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
