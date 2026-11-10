module

public import Ix.Cli.FormalAiur
public import Ix.IxVM.ClaimHarness
public import Ix.Aiur.Statistics
public import Ix.AiurInvocation
public import Ix.IxVM.PwCheck

/-!
# Running claims through the IxVM program

The IxVM suites submit claims to the formal IxVM program and pin each verdict.
A case is a claim witness built by `IxVM.ClaimHarness`, as `ix check` builds
one, with the verdict it must get and, for a rejection, text the error must
contain. The cases run in the production host, `ixvm-proof test`, against the
trusted claim artifact: the same program, entry point (`IxVM::verify_claim`)
and witness preparation as `ix check` and `ix prove`.

Three helpers name what the suites run against, so that a change in how the
program is produced (elaborated from Lean, serialized as Ixon) changes them
only:

- `programArtifact` is the IxVM claim artifact: `$IX_AIUR_ARTIFACT`, or the
  checkout's cached export (`ix prepare`), exported on first use;
- `programHost` is the Rust host: `$IX_AIUR_HOST`, or the checkout's
  `ixvm-proof`, built on first use;
- `programSources` is the program's source text, which the guards over its
  literals and IO reads scan.

`$IX_TEST_OUTPUT_DIR`, when set, keeps the case files, so that a failing case
can be rerun alone with `ixvm-proof test <artifact> <file>`. Cases with FFT
pins also request a `.stats.json` sidecar from the host with `--stats-out`.
Lean computes and checks the costs from those raw measurements.

## Circuit verdict

Ordinary execution skips the assertions the program exports with
`runtimeCheck := false` (`constrain_eq!`: the `u32`/`u64` gadgets' range and
recomposition checks, `KernelNatPrim`'s `split_u32`), which only the circuit
enforces. In circuit-verdict mode the host checks every assertion, so a case's
verdict is the circuit's on the case's witness. The circuit verdict is the
suites' verdict: the harness runs every case file in circuit-verdict mode
unless `$IX_AIUR_CIRCUIT_VERDICT=0` selects plain execution or a suite pins a
mode with `circuit`. The host acknowledges the mode in its output; a case file
whose host did not is a failure, so that a stale host cannot pass a suite in
the wrong mode.
-/

public section

namespace Tests.Ix.IxVM

open IxVM.ClaimHarness

/-- The IxVM claim artifact the suites execute: `$IX_AIUR_ARTIFACT`, or the
checkout's cached export. -/
def programArtifact : IO String := Ix.Cli.FormalAiur.artifact default

/-- The Rust host that executes the cases (`ixvm-proof test`). -/
def programHost : IO String := Ix.Cli.FormalAiur.host

/-- The Aiur source text of a program's modules as `(file, text)`, in file-name
order: the body of the `aiur⟦ … ⟧` block of each `.lean` file in `dir`, by
default the IxVM program's modules, without `--` comment lines. Named DSL
modules retain all function quotations; legacy module quotations (used by
MultiStark) retain their whole block. Missing declarations fail the guard. -/
def programSources (dir : System.FilePath := "IxVM/IxVM/Source") :
    IO (Array (System.FilePath × String)) := do
  let dir := (← Ix.Cli.FormalAiur.repoRoot) / dir
  let files := ((← dir.readDir).map (·.path)).filter (·.extension == some "lean")
  let mut out := #[]
  for file in files.qsort (·.toString < ·.toString) do
    let text ← IO.FS.readFile file
    let lines := text.splitOn "\n"
    let named := lines.dropWhile fun l => !l.trimAscii.toString.startsWith "aiur_module "
    let lines ← if !named.isEmpty then pure named else do
      let (head :: _ :: _) := text.splitOn "\n⟧"
        | throw (IO.userError s!"{file} has no Aiur declarations")
      let parts := head.splitOn "aiur⟦"
      unless parts.length ≥ 2 do throw (IO.userError s!"{file} has no Aiur declarations")
      pure ((parts.getLastD "").splitOn "\n")
    out := out.push (file, "\n".intercalate (lines.filter
      fun l => !l.trimAscii.toString.startsWith "--"))
  if out.isEmpty then throw (IO.userError s!"{dir} holds no module files")
  return out

/-- A claim submitted to the IxVM program, with its expected verdict. -/
structure Case where
  label : String
  /-- Whether the program must accept the claim. -/
  accept : Bool
  /-- For a rejection: text the execution error must contain, such as the
  failing assertion's message. Without it, any failure of the program counts,
  except a witness that lacks data the program asks for (`missing hint`). -/
  rejectsWith : Option String := none
  /-- For an acceptance: a function of the program the execution must call,
  such as the native rule a case targets. -/
  exercises : Option String := none
  /-- Exact rounded FFT-work surrogate of the accepted execution. -/
  expectedFftCost : Option Nat := none
  witness : ClaimWitness

/-- The case for `claim` over `env`, with the assumption trees its roots name. -/
def Case.ofClaim (label : String) (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {}) (accept : Bool := true)
    (rejectsWith : Option String := none) : Except String Case := do
  let witness ← buildClaimWitness env claim trees
  return { label, accept, rejectsWith, witness }

/-- `c` with the binder data (D2, `IxVM.PwHints`) its claim's conversion
reads, when its witness carries none: a suite that builds its IO by hand gets
them as `IxVM.ClaimHarness`'s builders give them. -/
def Case.withPwHints (c : Case) : Except String Case := do
  if _root_.IxVM.PwHints.hasHints c.witness.inputIOBuffer then return c
  let some claim := _root_.IxVM.PwHints.claimOf c.witness.inputIOBuffer c.witness.input | return c
  let io ← _root_.IxVM.PwHints.withHints claim c.witness.inputIOBuffer
  return { c with witness := { c.witness with inputIOBuffer := io } }

/-! ## The case file

`ixvm-proof test` reads a case file in Ixon (`Ix.AiurInvocation`): a header,
the cases one at a time, each a label, the verdict, `rejects_with`,
`exercises` and the invocation (`Ix.Cli.FormalAiur.invocation`), and a
trailer. Witnesses carry megabytes of constant bytes, so a case is encoded
when it is written and then dropped. -/

/-- One case as it follows the header of a case file. -/
def Case.encode (c : Case) : ByteArray :=
  let invocation := Ix.Cli.FormalAiur.invocation c.witness.input c.witness.inputIOBuffer
  Ix.AiurInvocation.Case.encode
    { label := c.label, accept := c.accept, rejectsWith := c.rejectsWith,
      exercises := c.exercises, invocation := invocation }

/-- The stream elements of a case, the measure of its size. -/
def Case.size (c : Case) : Nat :=
  c.witness.inputIOBuffer.map.fold (init := c.witness.input.size) fun n _ info => n + info.len

/-! ## Running

A suite adds its cases to a `Runner` one at a time. A witness holds megabytes
of constant bytes, so each case is written to the current case file as it is
added and then dropped. A file of about `limit` stream elements, or of
`maxCases` cases, is closed and runs in a host process at once, up to `jobs`
at a time, while the suite builds the next cases. -/

/-- The case file being written: its path, handle, cases and stream elements. -/
structure OpenFile where
  path : System.FilePath
  handle : IO.FS.Handle
  cases : Nat
  size : Nat
  fftPins : Array (String × Nat) := #[]

structure Runner where
  suite : String
  dir : System.FilePath
  artifact : String
  host : String
  /-- Circuit-verdict mode: the host checks every assertion. -/
  circuit : Bool := false
  jobs : Nat
  limit : Nat
  maxCases : Nat
  current : IO.Ref (Option OpenFile)
  tasks : IO.Ref (Array (System.FilePath × Array (String × Nat) × Task (Except IO.Error IO.Process.Output)))
  labels : IO.Ref (Std.HashSet String)
  broken : IO.Ref Nat

/-- The host's switch for circuit-verdict mode. -/
def circuitVerdictVar : String := "IX_AIUR_CIRCUIT_VERDICT"

/-- The number of assertions the host says it enabled for circuit-verdict
mode, from its acknowledgement line. -/
def circuitAcknowledgement (stdout : String) : Option Nat :=
  (stdout.splitOn "\n").findSome? fun line =>
    match line.trimAscii.toString.splitOn " " with
    | "circuit" :: "verdict:" :: n :: _ => n.toNat?
    | _ => none

/-- Close the current file and run it. -/
private def Runner.flush (r : Runner) : IO Unit := do
  let some file ← r.current.get | return
  r.current.set none
  file.handle.write Ix.AiurInvocation.casesTrailer
  file.handle.flush
  let mut args := #["test", r.artifact, file.path.toString]
  unless file.fftPins.isEmpty do
    args := args ++ #["--stats-out", (file.path.withExtension "stats.json").toString]
  let tasks ← r.tasks.get
  if tasks.size ≥ r.jobs then
    let _ ← IO.wait tasks[tasks.size - r.jobs]!.2.2
  let env := #[(circuitVerdictVar, if r.circuit then some "1" else none)]
  let task ← IO.asTask (prio := .dedicated)
    (IO.Process.output { cmd := r.host, args, env })
  r.tasks.modify (·.push (file.path, file.fftPins, task))

/-- A case that could not be built: reported, and fails the suite. -/
def Runner.fail (r : Runner) (message : String) : IO Unit := do
  r.broken.modify (· + 1)
  IO.eprintln s!"[{r.suite}] {message}"

/-- The host-side check of a case's binder data (`$IX_PW_CHECK`): every key
the conversion asks for answered, every datum the kernel's
(`IxVM.PwHints.check`), and the annotator, rerun on the witness without its
data, deterministic. Prints one `PW` line; returns the failure, if any. -/
def pwCheckCase (suite : String) (c : Case) : IO (Option String) := do
  let io := c.witness.inputIOBuffer
  unless _root_.IxVM.PwHints.hasHints io do return none
  let t0 ← IO.monoMsNow
  let again := _root_.IxVM.PwHints.annotate (_root_.IxVM.PwHints.stripHints io)
  let rerun ← match again with
    | .ok (io', stats) => do
      let same := match _root_.IxVM.PwHints.tableOf io', _root_.IxVM.PwHints.tableOf io with
        | .ok a, .ok b => a.size == b.size && a.toList.all fun (k, v) => b[k]? == some v
        | _, _ => false
      pure (some (stats, same))
    | .error _ => pure none
  let t1 ← IO.monoMsNow
  match _root_.IxVM.PwHints.check io, rerun with
  | .ok rep, some (stats, same) =>
    let (values, blocks, extra) := _root_.IxVM.PwHints.streamCounts io
    IO.println s!"PW {c.label}: {rep.render} values={values} blocks={blocks} \
      variants>0={extra} binders={stats.binders} shares={stats.shares} \
      free-shares={stats.freeShares} params={stats.params} \
      fallbacks={stats.fallbacks} refused={stats.refused} annotate_ms={t1 - t0} \
      check_ms={(← IO.monoMsNow) - t1}"
    if rep.ok && same then return none
    for s in rep.samples do IO.eprintln s!"[{suite}] PW {c.label}: {s}"
    return some s!"PW {c.label}: binder data incomplete, not the kernel's, or not deterministic"
  | .error e, _ => return some s!"PW {c.label}: {e}"
  | _, none => return some s!"PW {c.label}: the annotator failed on a rerun"

/-- `pwCheckCase` in a runner: a failure fails the suite. -/
def Runner.pwCheck (r : Runner) (c : Case) : IO Unit := do
  if let some e ← pwCheckCase r.suite c then r.fail e

/-- Write `c` to the current case file. -/
def Runner.add (r : Runner) (c : Case) : IO Unit := do
  let built ← match c.withPwHints with
    | .ok c' => pure (some c')
    | .error e => do
      r.fail s!"the binder data of {c.label} could not be built: {e}"
      pure none
  let some c := built | return
  if let some mode ← IO.getEnv "IX_PW_CHECK" then
    r.pwCheck c
    if mode == "only" then return
  if c.expectedFftCost.isSome && !c.accept then
    return ← r.fail s!"FFT pin on rejection case {c.label}"
  if (← r.labels.get).contains c.label then
    return ← r.fail s!"two cases are labelled {c.label}"
  r.labels.modify (·.insert c.label)
  let file ← match ← r.current.get with
    | some file => pure file
    | none => do
      let path := r.dir / s!"{r.suite}-{(← r.tasks.get).size}.ixt"
      let handle ← IO.FS.Handle.mk path .write
      handle.write Ix.AiurInvocation.casesHeader
      pure { path, handle, cases := 0, size := 0 }
  file.handle.write c.encode
  let fftPins := match c.expectedFftCost with
    | some cost => file.fftPins.push (c.label, cost)
    | none => file.fftPins
  let file := { file with cases := file.cases + 1, size := file.size + c.size, fftPins }
  r.current.set (some file)
  if file.size ≥ r.limit || file.cases ≥ r.maxCases then r.flush

/-- Build `c` and write it, or report why it could not be built. -/
def Runner.build (r : Runner) (c : Except String Case) : IO Unit :=
  match c with
  | .ok c => r.add c
  | .error e => r.fail s!"a case could not be built: {e}"

/-- Run the cases `body` adds through the IxVM program (`ixvm-proof test`).
Every case runs; the result is `0` when every case was built and every verdict
and FFT cost are the expected ones. The host reports verdicts and execution
times; Lean computes and checks costs from the raw statistics. -/
def withRunner (suite : String) (body : Runner → IO Unit) (jobs : Nat := 8)
    (limit : Nat := 4_000_000) (maxCases : Nat := 200) (circuit : Option Bool := none) :
    IO UInt32 := do
  let artifact ← programArtifact
  let host ← programHost
  -- The circuit verdict unless the environment asks for plain execution.
  let circuit ← match circuit with
    | some c => pure c
    | none => do pure ((← IO.getEnv circuitVerdictVar) != some "0")
  let go (dir : System.FilePath) : IO UInt32 := do
    IO.FS.createDirAll dir
    let started ← IO.monoMsNow
    let current ← IO.mkRef none
    let tasks ← IO.mkRef #[]
    let labels ← IO.mkRef {}
    let broken ← IO.mkRef 0
    let r : Runner := {
      suite := suite, dir := dir, artifact := artifact, host := host, circuit := circuit,
      jobs := jobs, limit := limit, maxCases := maxCases, current := current, tasks := tasks,
      labels := labels, broken := broken }
    try body r catch e => r.fail s!"building the cases failed: {e}"
    r.flush
    let mut failed := 0
    for (path, pins, task) in ← r.tasks.get do
      let out ← IO.ofExcept (← IO.wait task)
      IO.print out.stdout
      unless out.exitCode == 0 do
        failed := failed + 1
        IO.eprintln s!"[{suite}] {path}: {out.stderr.trimAscii}"
      if circuit then
        match circuitAcknowledgement out.stdout with
        | some 0 =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: the host enabled no deferred assertion"
        | some _ => pure ()
        | none =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: the host did not acknowledge circuit-verdict mode"
      unless pins.isEmpty do
        try
          let raw ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (path.withExtension "stats.json")))
          for (label, expected) in pins do
            let measurements ← IO.ofExcept (raw.getObjVal? label >>= Aiur.ExecutionMeasurements.fromJson)
            let actual := (Aiur.computeStats measurements).roundedFftCost
            IO.println s!"FFT {label}: {actual} (expected {expected})"
            unless actual == expected do
              failed := failed + 1
              IO.eprintln s!"FAILED {label}: FFT cost {actual}, expected {expected}"
        catch e =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: invalid or missing FFT statistics: {e}"
    let broken ← r.broken.get
    let mode := if circuit then "circuit verdict" else "execution verdict"
    IO.println s!"[{suite}] {(← r.labels.get).size} claims in {(← r.tasks.get).size} files \
      ({mode}), {(← IO.monoMsNow) - started} ms; {broken} cases not built, \
      {failed} verdict, statistics or FFT-pin failures"
    return if failed == 0 && broken == 0 then 0 else 1
  match ← IO.getEnv "IX_TEST_OUTPUT_DIR" with
  | some dir => go (System.FilePath.mk dir / "ixvm")
  | none => IO.FS.withTempDir go

/-- A case, built when it is written. -/
abbrev Builder := Unit → Except String Case

/-- Run `cases`, building each as it is written. -/
def runCases (suite : String) (cases : Array Builder) (jobs : Nat := 8)
    (circuit : Option Bool := none) : IO UInt32 :=
  withRunner suite (jobs := jobs) (circuit := circuit) fun r => do
    IO.println s!"[{suite}] {cases.size} claims through the IxVM program"
    for build in cases do r.build (build ())

end Tests.Ix.IxVM

end
