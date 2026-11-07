module

public import Ix.Cli.FormalAiur
public import Ix.IxVM.ClaimHarness

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
can be rerun alone with `ixvm-proof test <artifact> <file>`.
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
default the IxVM program's modules, without its `--` comment lines. The block
starts after the last `aiur⟦` before the `⟧` that closes it at the start of a
line (the module docstring mentions `aiur⟦ … ⟧` first). A module file without
a block fails, so a change in the sources' layout cannot hide them from the
guards. -/
def programSources (dir : System.FilePath := "IxVM/IxVM/Modules") :
    IO (Array (System.FilePath × String)) := do
  let dir := (← Ix.Cli.FormalAiur.repoRoot) / dir
  let files := ((← dir.readDir).map (·.path)).filter (·.extension == some "lean")
  let mut out := #[]
  for file in files.qsort (·.toString < ·.toString) do
    let text ← IO.FS.readFile file
    let (head :: _ :: _) := text.splitOn "\n⟧"
      | throw (IO.userError s!"{file} has no aiur⟦ … ⟧ block")
    let parts := head.splitOn "aiur⟦"
    unless parts.length ≥ 2 do throw (IO.userError s!"{file} has no aiur⟦ … ⟧ block")
    let lines := ((parts.getLastD "").splitOn "\n").filter
      fun l => !l.trimAscii.toString.startsWith "--"
    out := out.push (file, "\n".intercalate lines)
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
  witness : ClaimWitness

/-- The case for `claim` over `env`, with the assumption trees its roots name. -/
def Case.ofClaim (label : String) (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {}) (accept : Bool := true)
    (rejectsWith : Option String := none) : Except String Case := do
  let witness ← buildClaimWitness env claim trees
  return { label, accept, rejectsWith, witness }

/-! ## The case file

`ixvm-proof test` reads a JSON array of `{label, accept, rejects_with,
invocation}`, where `invocation` is `Ix.Cli.FormalAiur.invocation`'s object.
Witnesses carry megabytes of constant bytes, so the streams are written as
text directly rather than through a `Json` node per byte. -/

/-- Append the decimal digits of `n`. -/
@[inline] private def pushNat (out : ByteArray) (n : Nat) : ByteArray :=
  let digit (d : Nat) : UInt8 := 48 + d.toUInt8
  if n < 10 then out.push (digit n)
  else if n < 100 then (out.push (digit (n / 10))).push (digit (n % 10))
  else if n < 1000 then
    ((out.push (digit (n / 100))).push (digit (n / 10 % 10))).push (digit (n % 10))
  else out ++ (toString n).toUTF8

private def pushStr (out : ByteArray) (s : String) : ByteArray := out ++ s.toUTF8

/-- Append `[a, b, …]`, the values of `xs` from `start` for `len` elements. -/
private def pushArray (out : ByteArray) (xs : Array Aiur.G) (start len : Nat) : ByteArray :=
  Id.run do
    let mut out := out.push '['.toUInt8
    for i in [start:start + len] do
      if i != start then out := out.push ','.toUInt8
      out := pushNat out (xs[i]?.map (·.n) |>.getD 0)
    return out.push ']'.toUInt8

/-- One case as `ixvm-proof test` reads it. -/
def Case.encode (c : Case) (out : ByteArray := .empty) : ByteArray := Id.run do
  let w := c.witness
  let mut out := pushStr out s!"\{\"label\":{(Lean.toJson c.label).compress},\
    \"accept\":{c.accept}"
  if let some reason := c.rejectsWith then
    out := pushStr out s!",\"rejects_with\":{(Lean.toJson reason).compress}"
  if let some name := c.exercises then
    out := pushStr out s!",\"exercises\":{(Lean.toJson name).compress}"
  out := pushStr out ",\"invocation\":{\"entry\":\"IxVM::verify_claim\",\"args\":"
  out := pushArray out w.input 0 w.input.size
  out := pushStr out ",\"streams\":["
  let mut first := true
  for ((channel, key), info) in w.inputIOBuffer.map.toArray do
    unless first do out := out.push ','.toUInt8
    first := false
    out := pushStr out "{\"channel\":"
    out := pushNat out channel.n
    out := pushStr out ",\"key\":"
    out := pushArray out key 0 key.size
    out := pushStr out ",\"values\":"
    out := pushArray out (w.inputIOBuffer.data.getD channel #[]) info.idx info.len
    out := out.push '}'.toUInt8
  return pushStr out "]}}"

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

structure Runner where
  suite : String
  dir : System.FilePath
  artifact : String
  host : String
  jobs : Nat
  limit : Nat
  maxCases : Nat
  current : IO.Ref (Option OpenFile)
  tasks : IO.Ref (Array (System.FilePath × Task (Except IO.Error IO.Process.Output)))
  labels : IO.Ref (Std.HashSet String)
  broken : IO.Ref Nat

/-- Close the current file and run it. -/
private def Runner.flush (r : Runner) : IO Unit := do
  let some file ← r.current.get | return
  r.current.set none
  file.handle.write "]".toUTF8
  file.handle.flush
  let tasks ← r.tasks.get
  if tasks.size ≥ r.jobs then
    let _ ← IO.wait tasks[tasks.size - r.jobs]!.2
  let task ← IO.asTask (prio := .dedicated)
    (IO.Process.output { cmd := r.host, args := #["test", r.artifact, file.path.toString] })
  r.tasks.modify (·.push (file.path, task))

/-- A case that could not be built: reported, and fails the suite. -/
def Runner.fail (r : Runner) (message : String) : IO Unit := do
  r.broken.modify (· + 1)
  IO.eprintln s!"[{r.suite}] {message}"

/-- Write `c` to the current case file. -/
def Runner.add (r : Runner) (c : Case) : IO Unit := do
  if (← r.labels.get).contains c.label then
    return ← r.fail s!"two cases are labelled {c.label}"
  r.labels.modify (·.insert c.label)
  let file ← match ← r.current.get with
    | some file => pure file
    | none => do
      let path := r.dir / s!"{r.suite}-{(← r.tasks.get).size}.json"
      let handle ← IO.FS.Handle.mk path .write
      handle.write "[".toUTF8
      pure { path, handle, cases := 0, size := 0 }
  if file.cases > 0 then file.handle.write ",".toUTF8
  file.handle.write c.encode
  let file := { file with cases := file.cases + 1, size := file.size + c.size }
  r.current.set (some file)
  if file.size ≥ r.limit || file.cases ≥ r.maxCases then r.flush

/-- Build `c` and write it, or report why it could not be built. -/
def Runner.build (r : Runner) (c : Except String Case) : IO Unit :=
  match c with
  | .ok c => r.add c
  | .error e => r.fail s!"a case could not be built: {e}"

/-- Run the cases `body` adds through the IxVM program (`ixvm-proof test`).
Every case runs; the result is `0` when every case was built and every verdict
is the expected one. The host prints one line per case: its verdict, the error
that rejected it, and its execution time. -/
def withRunner (suite : String) (body : Runner → IO Unit) (jobs : Nat := 8)
    (limit : Nat := 4_000_000) (maxCases : Nat := 200) : IO UInt32 := do
  let artifact ← programArtifact
  let host ← programHost
  let go (dir : System.FilePath) : IO UInt32 := do
    IO.FS.createDirAll dir
    let started ← IO.monoMsNow
    let current ← IO.mkRef none
    let tasks ← IO.mkRef #[]
    let labels ← IO.mkRef {}
    let broken ← IO.mkRef 0
    let r : Runner := {
      suite := suite, dir := dir, artifact := artifact, host := host, jobs := jobs,
      limit := limit, maxCases := maxCases, current := current, tasks := tasks,
      labels := labels, broken := broken }
    try body r catch e => r.fail s!"building the cases failed: {e}"
    r.flush
    let mut failed := 0
    for (path, task) in ← r.tasks.get do
      let out ← IO.ofExcept (← IO.wait task)
      IO.print out.stdout
      unless out.exitCode == 0 do
        failed := failed + 1
        IO.eprintln s!"[{suite}] {path}: {out.stderr.trimAscii}"
    let broken ← r.broken.get
    IO.println s!"[{suite}] {(← r.labels.get).size} claims in {(← r.tasks.get).size} files, \
      {(← IO.monoMsNow) - started} ms; {broken} cases not built, \
      {failed} files with unexpected verdicts"
    return if failed == 0 && broken == 0 then 0 else 1
  match ← IO.getEnv "IX_TEST_OUTPUT_DIR" with
  | some dir => go (System.FilePath.mk dir / "ixvm")
  | none => IO.FS.withTempDir go

/-- A case, built when it is written. -/
abbrev Builder := Unit → Except String Case

/-- Run `cases`, building each as it is written. -/
def runCases (suite : String) (cases : Array Builder) (jobs : Nat := 8) : IO UInt32 :=
  withRunner suite (jobs := jobs) fun r => do
    IO.println s!"[{suite}] {cases.size} claims through the IxVM program"
    for build in cases do r.build (build ())

end Tests.Ix.IxVM

end
