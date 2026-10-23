/-
  The compiler suites' unit harness (R11-08), kernels: the checkers on a
  compiled output, a test-only environment of computation-rule statements,
  and the machinery of a kernel-failure record.

  Legs: `cert`, the certified checker (`kernel-check-ixe`, through
  `ClosureHarness.certify`; acceptance is a row verdict, declines in
  documented classes are not failures), and `rs`, the Rust kernel
  (`ix check-rs`, meta mode: seeded checks are subject-only; anonymous mode
  on request), and `lean`, IxC through `ix check-lean`. Its exact selected
  labels, outcomes and reasons are checked independently of producer/support
  record counts; accept and typed remain distinct successful outcomes.

  A record (`Expect` rows) covers the failures of one unit and leg whose
  message contains `msg`: exactly the names listed, or exactly `count` of
  them. `check` runs both ways: a failure no row covers fails, and so does a
  row whose names do not all fail or whose count is not met (stale). A row of
  a meta-mode-only cause (`metaOnly`) covers a failure only where the
  certified checker accepts the same constant. A `varies` row (the meta
  kernel's verdicts on collapsed aliases change between runs on one output)
  covers any failure of its class that the anonymous kernel (run on the same
  output for this) accepts, and needs at least one, unless it also carries
  `mayBeEmpty` (the cause, as text, why a run may see none; only on a
  `varies` row). Each leg must check every requested name. `emit` writes
  candidate rows from dumps, for review.
-/
import Ix.Compile.Pass
import Tests.Ix.Compile.Harness.Units
import Tests.Ix.Compile.KernelReport
import Tests.Ix.Compile.LeanReport

open Lean

namespace Tests.Ix.Compile.Harness

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- Spawned binaries must not see the toolchain's `LD_LIBRARY_PATH`. -/
private def runProc (cmd : System.FilePath) (args : Array String) : IO IO.Process.Output := do
  let exe ← IO.FS.realPath cmd
  IO.Process.output { cmd := exe.toString, args, env := #[("LD_LIBRARY_PATH", none)] }

/-! ## The checkers -/

/-- The failures of one kernel run, `(leg, name, message)`, and the number of
constants each leg reports it checked. -/
structure KernelRun where
  failed : Array (String × String × String)
  checked : List (String × Nat)
  /-- Selected labels, independent of an anonymous Rust dependency closure. -/
  selected : List (String × Nat) := []
  /-- The declarations checked: the requested names, block labels expanded. -/
  targets : Array String := #[]
  /-- Exact selected IxC outcomes, including successful typed-only subjects. -/
  leanOutcomes : Array LeanReport.Row := #[]

/-- The three legs must independently cover the requested declarations.
These are selected-label counts, not the number of producer/support records. -/
def kernelCoverageProblems (checked : List (String × Nat)) (requested : Nat) : Array String := Id.run do
  let mut problems := #[]
  if requested == 0 then problems := problems.push "kernels requested zero declarations"
  for leg in ["cert", "rs", "lean"] do
    unless checked.filter (·.1 == leg) == [(leg, requested)] do
      problems := problems.push s!"{leg}: missing, duplicate or incomplete selected-label coverage"
  for (leg, _) in checked do
    unless ["cert", "rs", "lean"].contains leg do
      problems := problems.push s!"unknown kernel leg: {leg}"
  return problems

/-- Rust reports selected seeds separately from anonymous closure work. -/
def rsSelectedLabels (stdout : String) (anon : Bool) : Except String Nat := do
  let seedPrefix := if anon then "[check] " else "[check] checking "
  let [line] := (stdout.splitOn "\n").filter fun line =>
    line.startsWith seedPrefix && hasSub line " seed constant(s)"
    | throw "check-rs: missing or duplicate selected-seed summary"
  let rest := (line.drop seedPrefix.length).toString
  let [count, suffix] := rest.splitOn " seed constant(s)"
    | throw "check-rs: malformed selected-seed summary"
  unless (if anon then suffix.startsWith ": " else suffix.isEmpty) do
    throw "check-rs: malformed selected-seed suffix"
  let some count := count.toNat? | throw "check-rs: non-numeric selected-seed count"
  return count

/-- Attach actual strict IxC CLI evidence without changing either older leg. -/
def KernelRun.withLeanReport (run : KernelRun) (stdout stderr failOut : String) (exitCode : UInt32) :
    Except String KernelRun := do
  let rows ← LeanReport.parse run.targets stdout stderr failOut exitCode
  let refused := rows.filterMap fun r =>
    if LeanReport.success r.outcome then none else some ("lean", r.label, r.reason)
  return { run with
    failed := run.failed ++ refused
    checked := run.checked ++ [("lean", rows.size)]
    selected := run.selected ++ [("lean", rows.size)]
    leanOutcomes := rows }

def KernelRun.leanSummary (run : KernelRun) : String :=
  let counts := ["accept", "typed", "reject", "decline", "blocked"].map fun outcome =>
    s!"{outcome} {(run.leanOutcomes.filter (·.outcome == outcome)).size}"
  s!"IxC {run.leanOutcomes.size}/{run.targets.size} exact labels ({", ".intercalate counts})"

/-- A synthetic `Muts` label denotes a container, not a kernel declaration.
Expand it to all recorded members, verifying each member's projection and
owning block; keep every ordinary requested selector. -/
def expandKernelTargets (parts : Ixon.LazyEnvParts) (requested : Array String) :
    Except String (Array String) := do
  let rows := parts.namedRows.foldl (fun m row => m.insert row.name.pretty row)
    ({} : Std.HashMap String Ixon.NamedRow)
  let mut declarations : Array String := #[]
  let mut members : Array String := #[]
  for label in requested do
    let some row := rows.get? label | throw s!"kernel selector is absent: {label}"
    let some constant := parts.env.getConst? row.addr
      | throw s!"kernel selector has no anonymous payload: {label}"
    match constant.info with
    | .muts entries =>
      let named ← row.materialize parts.backing parts.nameRev
      let .muts classes _ := named.constMeta.info
        | throw s!"block selector has no member metadata: {label}"
      unless !classes.isEmpty && classes.size == entries.size do
        throw s!"block selector has inconsistent member count: {label}"
      for (cls, index) in classes.zipIdx do
        if cls.isEmpty then throw s!"block selector has an empty class: {label}"
        for hash in cls do
          let some name := parts.env.names.get? hash
            | throw s!"block selector has an unknown member name: {label}"
          let some memberIndex := parts.rowIdx.get? name
            | throw s!"block selector has an unregistered member: {label}: {name.pretty}"
          let some member := parts.namedRows[memberIndex]?
            | throw s!"block selector has an invalid member row: {label}"
          let some payload := parts.env.getConst? member.addr
            | throw s!"block selector member has no payload: {label}: {name.pretty}"
          let belongs := match payload.info with
            | .iPrj p => p.block == row.addr && p.idx.toNat == index
            | .dPrj p => p.block == row.addr && p.idx.toNat == index
            | .rPrj p => p.block == row.addr && p.idx.toNat == index
            | _ => false
          unless belongs do
            throw s!"block selector member belongs elsewhere: {label}: {name.pretty}"
          members := members.push name.pretty
    | _ => declarations := declarations.push label
  for member in members do
    unless declarations.contains member do declarations := declarations.push member
  return declarations

/-- `(leg, name, message)` of every failure of the three kernels on `names` of
the output `bytes`, and each leg's checked count. The output is written to
`<dir>/out.ixe`. Declines of the certified checker in documented classes are
not failures. Process and report failures throw instead of entering the
per-name accounting. `anon`: the Rust kernel in anonymous mode (subject-only
with `skipDeps`), its address labels mapped back to the names. -/
def kernelRun (dir : System.FilePath) (bytes : ByteArray) (names : Array String)
    (anon : Bool := false) (skipDeps : Bool := false) : IO KernelRun := do
  if names.isEmpty then throw (IO.userError "kernel check requested no names")
  let mut failed : Array (String × String × String) := #[]
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes)
  let names ← IO.ofExcept (expandKernelTargets parts names)
  if names.isEmpty then throw (IO.userError "kernel selectors contain no declarations")
  let namesFile := dir / "names.txt"
  IO.FS.writeFile namesFile ("\n".intercalate names.toList ++ "\n")
  let byName : Std.HashMap String String := parts.namedRows.foldl (fun m row =>
    m.insert row.name.pretty (toString (Tests.Ix.Compile.AuxCert.recordOf parts.env row.addr))) {}
  let rawAddresses : Std.HashMap String String := parts.namedRows.foldl
    (fun m row => m.insert row.name.pretty (toString row.addr)) {}
  let mut expected : Array (String × String) := #[]
  let mut anonNames : Std.HashMap String (Array String) := {}
  for n in names do
    let some address := byName[n]?
      | throw (IO.userError s!"kernel check requested a name absent from the output: {n}")
    expected := expected.push (n, address)
    let some rawAddress := rawAddresses[n]?
      | throw (IO.userError s!"missing anonymous address for {n}")
    anonNames := anonNames.insert rawAddress ((anonNames.getD rawAddress #[]).push n)
  -- the certified checker (whole file; it writes `<dir>/out.ixe`)
  let report ← Tests.Ix.Compile.ClosureHarness.certify dir "out" bytes (jobs := 8)
  IO.ofExcept (KernelReport.checkCoverage report expected)
  for (n, address) in expected do
    let some verdict := report[address]?
      | throw (IO.userError s!"missing certified verdict for {n}@{address}")
    if verdict.outcome == "accept" then continue
    if verdict.outcome == "decline" && Tests.Ix.Compile.AuxCert.documentedDecline verdict.reason then
      continue
    failed := failed.push ("cert", n, s!"{verdict.outcome}: {verdict.reason}")
  -- the Rust kernel on the names; every failure comes from the fail-out file
  -- (stdout shows the first 30)
  let path := dir / "out.ixe"
  let rsFailOut := dir / "rs.fail"
  if ← rsFailOut.pathExists then IO.FS.removeFile rsFailOut
  let rs ← runProc ixExe ((#["check-rs", path.toString, "--consts-file", namesFile.toString,
    "--fail-out", rsFailOut.toString] ++ (if anon then #["--anon"] else #[])
    ++ (if anon && skipDeps then #["--skip-deps"] else #[])))
  IO.FS.writeFile (dir / "rs.stdout") rs.stdout
  IO.FS.writeFile (dir / "rs.stderr") rs.stderr
  if rs.exitCode == 0 && hasSub (rs.stdout ++ rs.stderr) "[check] 0/0 passed" then
    throw (IO.userError "check-rs checked zero targets")
  let rsNames := fun (label : String) => match KernelReport.anonymousAddress? label with
    | some address => anonNames.getD address #[label]
    | none => #[label]
  let rsRows ← if ← rsFailOut.pathExists then
      pure (KernelReport.failOutRows (← IO.FS.readFile rsFailOut))
    else pure #[]
  for (label, m) in rsRows do
    for n in rsNames label do failed := failed.push ("rs", n, m)
  let rsN := KernelReport.rsChecked (rs.stdout ++ rs.stderr)
  if rs.exitCode != 0 && rsRows.isEmpty then
    failed := failed.push ("rs", "*",
      s!"check-rs exit {rs.exitCode}: {((rs.stdout ++ rs.stderr).takeEnd 300).toString}")
  let rsSelected ← IO.ofExcept (rsSelectedLabels rs.stdout anon)
  unless (rsN.getD 0) > 0 do throw (IO.userError "check-rs checked zero records or omitted its summary")
  let partialRun : KernelRun := {
    failed, targets := names, checked := [("cert", expected.size), ("rs", rsN.getD 0)]
    selected := [("cert", expected.size), ("rs", rsSelected)] }
  let leanFailOut := dir / "lean.fail"
  if ← leanFailOut.pathExists then IO.FS.removeFile leanFailOut
  let lean ← runProc ixExe #["check-lean", path.toString, "--consts-file", namesFile.toString,
    "--fail-out", leanFailOut.toString, "--workers", "1", "--verbose"]
  IO.FS.writeFile (dir / "lean.stdout") lean.stdout
  IO.FS.writeFile (dir / "lean.stderr") lean.stderr
  IO.FS.writeFile (dir / "lean.exit") s!"{lean.exitCode}\n"
  let failText ← if ← leanFailOut.pathExists then IO.FS.readFile leanFailOut else pure ""
  let result ← IO.ofExcept (partialRun.withLeanReport lean.stdout lean.stderr failText lean.exitCode)
  IO.FS.writeFile (dir / "lean-outcomes.json")
    ((Json.arr (result.leanOutcomes.map LeanReport.Row.toJson)).pretty ++ "\n")
  let coverage := kernelCoverageProblems result.selected names.size
  unless coverage.isEmpty do throw (IO.userError ("; ".intercalate coverage.toList))
  return result

/-- `(leg, name, message)` of every failure (`kernelRun` without the counts). -/
def kernelFailures (dir : System.FilePath) (bytes : ByteArray) (names : Array String)
    (anon : Bool := false) : IO (Array (String × String × String)) :=
  (·.failed) <$> kernelRun dir bytes names anon

/-- `PASS3_FAILURES=<file>`: append every kernel failure of a unit, one
tab-separated row `unit run leg name message` (the message whole, its
newlines and tabs replaced), and one row `#checked unit run leg count` per
leg. `run` is `suite`, or a recheck's mode (`meta`, `anon`). -/
def dumpRuns (unit : String) (runs : List (String × KernelRun)) : IO Unit := do
  let some f := ← IO.getEnv "PASS3_FAILURES" | return
  let h ← IO.FS.Handle.mk f .append
  let clean := fun (s : String) => (s.replace "\n" " | ").replace "\t" " "
  for (run, r) in runs do
    for (leg, n) in r.checked do h.putStrLn s!"#checked\t{unit}\t{run}\t{leg}\t{n}"
    for (leg, n) in r.selected do h.putStrLn s!"#selected\t{unit}\t{run}\t{leg}\t{n}"
    for (leg, n, m) in r.failed do h.putStrLn s!"{unit}\t{run}\t{leg}\t{n}\t{clean m}"
    for row in r.leanOutcomes do
      h.putStrLn s!"#outcome\t{unit}\t{run}\tlean\t{row.label}\t{row.outcome}\t{clean row.reason}"
  h.flush

/-! ## 4. Computation rules in a test-only environment -/

/-- Compile one definition or theorem into `env` (names, blobs, constant,
`Named` entry), resolving the names of `known` first. -/
def addConst (cenv : _root_.Ix.CompileM.CompileEnv)
    (known : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address)
    (env : Ixon.Env) (ci : _root_.Ix.ConstantInfo) : Except String (Ixon.Env × Address) := do
  let name := ci.getCnst.name
  let blockEnv : _root_.Ix.CompileM.BlockEnv :=
    { all := ({} : _root_.Ix.Set _root_.Ix.Name).insert name, current := name,
      mutCtx := default, univCtx := [] }
  let init : _root_.Ix.CompileM.BlockState := { blockNameToAddr := known }
  match _root_.Ix.CompileM.CompileM.run cenv blockEnv init
      (_root_.Ix.CompileM.compileConstantInfo ci) with
  | .error e => throw s!"{name.pretty}: {e}"
  | .ok (r, bs) =>
    let (names, blobs) := Ixon.RawEnv.addNameComponentsWithBlobs
      (bs.blockNames.fold (fun m k v => m.insert k v) env.names)
      (bs.blockBlobs.fold (fun m k v => m.insert k v) env.blobs) name
    let env := { env with
      consts := env.consts.insert r.blockAddr { buf := r.blockBytes, len := r.blockBytes.size }
      named := env.named.insert name { addr := r.blockAddr, constMeta := r.blockMeta }
      names, blobs }
    return (env, r.blockAddr)

/-- The images and computation-rule statements (`RuleStmt`, proof
`Eq.refl`) of every changed block, added to a copy of the output's
environment (never to the output itself): the compiled image under its Lean
name when the output has it, else compiled here. Returns the environment,
the image names and the rule names. -/
def ruleEnv (out : _root_.Ix.CompileM.LeanPipelineOut) :
    Except String (Ixon.Env × Array String × Array String) := do
  let cenv := out.cenv
  let inp := _root_.Ix.Compile.Pass.viewInput cenv
  let mut env := out.env
  let mut known : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address := {}
  let mut images : Array String := #[]
  let mut rules : Array String := #[]
  let mut stmts : Array _root_.Ix.Compile.Image.RuleStmt := #[]
  for (_, all) in cenv.p3Blocks do
    let v ← _root_.Ix.Compile.Pass.buildView inp all
    for r in _root_.Ix.Compile.Pass.imageKinds inp.const? all do
      let some (.recInfo rv) := inp.const? r | continue
      let img ← v.image inp r
      if let some nd := env.named.get? r then
        known := known.insert r nd.addr
      else
        let dv : _root_.Ix.DefinitionVal := {
          cnst := { name := r, levelParams := img.levelParams, type := img.type }
          value := img.value, hints := .abbrev
          safety := if rv.isUnsafe then .unsafe else .safe, all := #[r] }
        let (env', a) ← addConst cenv known env (.defnInfo dv)
        env := env'
        known := known.insert r a
      images := images.push r.pretty
      stmts := stmts ++ img.rules
  for s in stmts do
    let tv : _root_.Ix.TheoremVal := {
      cnst := { name := s.name, levelParams := s.levelParams, type := s.type }
      value := s.proof, all := #[s.name] }
    let (env', _) ← addConst cenv known env (.thmInfo tv)
    env := env'
    rules := rules.push s.name.pretty
  return (env, images, rules)

/-! ## A kernel-failure record -/

/-- Recorded failures of one unit and leg with a message class. -/
structure Expect where
  unit : String
  leg : String
  cause : String
  /-- a substring of every covered failure's message -/
  msg : String
  /-- the names, exactly; empty: `count` names -/
  names : List String := []
  count : Nat := 0
  /-- the meta kernel's verdicts on the class vary between runs on one output:
  a failure of the class is covered where the certified checker and the
  anonymous kernel (run for this) accept the same constant, and at least one
  must occur -/
  varies : Bool := false
  /-- only with `varies`: the class may occur zero times on a run; the text is
  the cause. Relaxes only the "at least one". -/
  mayBeEmpty : Option String := none

/-- Causes that are defects of the meta-mode kernel only: a failure is
covered only where the certified checker accepts the constant. -/
def metaOnly (cause : String) : Bool :=
  cause.startsWith "BB-F1"

/-- Check the failures of one unit against `table`. `failed` holds
`(leg, name, message)`; `checked` each leg's checked count; `requested` the
number of names requested; `anon?` the `(leg, name)` failures of the
anonymous kernel on the same output, run where a row `varies`. Returns the
problems and one summary line. -/
def check (table : List Expect) (unit : String)
    (failed : Array (String × String × String)) (checked : List (String × Nat))
    (requested : Nat) (anon? : Option (Std.HashSet (String × String)) := none) :
    Array String × String := Id.run do
  let rows := (table.filter (·.unit == unit)).toArray
  let certFail : Std.HashSet String := failed.foldl (fun s (l, n, _) =>
    if l == "cert" then s.insert n else s) {}
  let mut problems : Array String := #[]
  let mut hits : Array (Array String) := rows.map fun _ => #[]
  for (leg, n, m) in failed do
    -- a row naming the constant first, then a counted row
    let fits := fun (e : Expect) => e.leg == leg && hasSub m e.msg &&
      !(metaOnly e.cause && certFail.contains n) &&
      -- a varying row covers only what the anonymous kernel accepts
      (!e.varies || anon?.any fun s => !s.contains (leg, n))
    let i? := match rows.findIdx? (fun e => fits e && e.names.contains n) with
      | some i => some i
      | none => rows.findIdx? fun e => fits e && e.names.isEmpty
    match i? with
    | some i => hits := hits.modify i (·.push n)
    | none => problems := problems.push s!"{unit}: {leg}: {n} fails, not recorded: {m.take 300}"
  for (e, hs) in rows.zip hits do
    if e.mayBeEmpty.isSome && !e.varies then
      problems := problems.push s!"{unit}: {e.leg} [{e.cause}] '{e.msg}': \
`mayBeEmpty` on a row that does not vary (record error)"
    if e.varies then
      if hs.isEmpty && e.mayBeEmpty.isNone then
        problems := problems.push s!"{unit}: {e.leg} [{e.cause}] '{e.msg}': \
no failure of the class occurs (stale)"
    else if e.names.isEmpty then
      if hs.size != e.count then
        problems := problems.push s!"{unit}: {e.leg} [{e.cause}] '{e.msg}': \
recorded {e.count} failure(s), {hs.size} occur{if hs.size < e.count then " (stale)" else ""}"
    else
      for n in e.names do
        unless hs.contains n do
          problems := problems.push s!"{unit}: {e.leg}: {n} recorded as failing \
({e.cause}) but does not (stale)"
  -- each leg checked every requested declaration
  for (leg, k) in checked do
    if k != requested then
      problems := problems.push s!"{unit}: {leg} checked {k} constant(s), expected {requested}"
  -- failures per leg and cause, for the log
  let mut byCause : Array (String × Nat) := #[]
  for (e, hs) in rows.zip hits do
    if hs.isEmpty then continue
    let k := s!"{e.leg} {(e.cause.splitOn " (").headD e.cause}"
    byCause := match byCause.findIdx? (·.1 == k) with
      | some i => byCause.modify i fun (k, n) => (k, n + hs.size)
      | none => byCause.push (k, hs.size)
  let summary := s!"{failed.size} failure(s) in {rows.size} recorded row(s) \
{byCause.toList.map fun (k, n) => s!"{k}: {n}"}; \
checked {checked.map fun (l, k) => s!"{l} {k}"} of {requested}"
  let maybe := (rows.zip hits).filterMap fun (e, hs) =>
    if e.mayBeEmpty.isSome then some s!"{e.leg} [{e.cause}] '{e.msg}' (may be empty): {hs.size} occur"
    else none
  let summary := if maybe.isEmpty then summary else s!"{summary}; {"; ".intercalate maybe.toList}"
  return (problems, summary)

/-- The `mayBeEmpty` control (run before a suite's units): every `mayBeEmpty`
row of `table` varies; and on a synthetic varying row, `check` passes with
none and with one failure of the class (the anonymous kernel accepting it),
and passes nothing else: the row without `mayBeEmpty` and with no failure is
stale, a failure the anonymous kernel also rejects is not covered, and
`mayBeEmpty` on a non-varying row is a record error. Returns the problems
(empty: the control holds) and a summary line. -/
def mayBeEmptyControl (table : List Expect) : Array String × String := Id.run do
  let marked := table.filter (·.mayBeEmpty.isSome)
  let mut problems : Array String := #[]
  for e in marked do
    unless e.varies do
      problems := problems.push s!"mayBeEmpty control: {e.unit} {e.leg} '{e.msg}' carries \
`mayBeEmpty` but does not vary"
  let row : Expect :=
    { unit := "X", leg := "rs", cause := "BB-F1", msg := "AppTypeMismatch", varies := true
      mayBeEmpty := some "synthetic control row" }
  let fail : Array (String × String × String) := #[("rs", "X.a", "AppTypeMismatch: X.a")]
  let ck (t : List Expect) (f : Array (String × String × String)) (anon : Std.HashSet (String × String)) :=
    (check t row.unit f [] 0 (some anon)).1.size
  let none0 := ck [row] #[] {}
  let one0 := ck [row] fail {}
  let strict := ck [{ row with mayBeEmpty := none }] #[] {}
  let anonRejects := ck [row] fail (({} : Std.HashSet (String × String)).insert ("rs", "X.a"))
  let notVarying := ck [{ row with varies := false, count := 0 }] #[] {}
  unless none0 == 0 do
    problems := problems.push s!"mayBeEmpty control: no failure gives {none0} problem(s), expected 0"
  unless one0 == 0 do
    problems := problems.push s!"mayBeEmpty control: one failure gives {one0} problem(s), expected 0"
  unless strict == 1 do
    problems := problems.push s!"mayBeEmpty control: without the flag, no failure gives {strict} \
problem(s), expected 1 (stale)"
  unless anonRejects == 1 do
    problems := problems.push s!"mayBeEmpty control: a failure the anonymous kernel rejects gives \
{anonRejects} problem(s), expected 1 (not covered)"
  unless notVarying ≥ 1 do
    problems := problems.push "mayBeEmpty control: the flag on a non-varying row is not refused"
  return (problems, s!"mayBeEmpty control: {marked.length} marked row(s) in the record; synthetic \
row: problems with 0/1 failures {none0}/{one0}, without the flag {strict}, anonymous-rejected \
{anonRejects}, on a non-varying row {notVarying}")

/-! ## Writing a record from dumps -/

/-- The message class of a failure: a substring every failure of the class
carries (addresses and terms vary). -/
def msgClass (m : String) : String := Id.run do
  if let some rest := (m.splitOn "Named entry for '")[1]? then
    if let some x := (rest.splitOn "'")[0]? then
      -- a refused block's members (`A`, `A2`) are named in hash order: the
      -- class is the name without its trailing digits
      let x := String.ofList (x.toList.reverse.dropWhile Char.isDigit).reverse
      return s!"Named entry for '{x}"
  for p in ["AppTypeMismatch", "ctor return type: head is not the inductive",
      "check_recursor: could not resolve inductive block", "universe param count",
      "blocked: ", "decline: reader: in-process model", "decline: non-standard axiom",
      "decline: projection on a non-structure", "reject: application type mismatch",
      "reject: function expected", "FunExpected", "declaration type mismatch",
      "projection: type mismatch with declared struct", "projection: struct type is not a constant",
      "populate_recursor_rules_from_block: canonical-order mismatch"] do
    if hasSub m p then return p
  return (m.take 60).toString

/-- The cause of one failure. `defectOf unit name` is the record's documented
defect of a constant (`UNCLASSIFIED` when none); `anonFails`: the same leg
rejects the name in anonymous mode; `certFails`: the certified checker
rejects it. -/
def causeOf (defectOf : String → String → String) (unit leg name msg : String)
    (anonFails certFails : Bool) : String :=
  let cls := msgClass msg
  if cls.startsWith "Named entry for '" then
    s!"REFUSED-SIBLING (A0 refuses the block of {(cls.drop 17).toString}: not a one-motive recursor)"
  else if leg == "cert" then
    if cls == "decline: non-standard axiom" then "CERT-AXIOM" else defectOf unit name
  else if !anonFails && !certFails then "BB-F1"
  else defectOf unit name

/-- Read a dump: `(unit, run, leg, name, message)` rows. -/
def readDump (path : String) : IO (Array (String × String × String × String × String)) := do
  let mut out := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | u :: s :: l :: n :: rest => out := out.push (u, s, l, n, "\t".intercalate rest)
    | _ => pure ()
  return out

/-- Print candidate record rows (`Expect`) from a suite dump (`rowsPath`, run
`suite`), its anonymous recheck (`recheckPath`, run `anon`) and further meta
rechecks of the same outputs (`more`, run `meta`): one row per unit, leg,
cause and message class. A row whose names are the same in every run lists
them (at most six) or counts them; a row whose names differ between runs is
marked `varies`. The rows are candidates: a record is reviewed, not copied. -/
def emit (defectOf : String → String → String) (rowsPath recheckPath : String)
    (more : List String) : IO UInt32 := do
  let rows ← readDump rowsPath
  let re ← readDump recheckPath
  let anon : Std.HashSet String := re.foldl (fun s (u, run, l, n, _) =>
    if run == "anon" then s.insert s!"{u}|{l}|{n}" else s) {}
  let cert : Std.HashSet String := rows.foldl (fun s (u, _, l, n, _) =>
    if l == "cert" then s.insert s!"{u}|{n}" else s) {}
  let mut runs : Array (Array (String × String × String × String × String)) := #[rows]
  for p in more do
    let r ← readDump p
    runs := runs.push (r.filter fun (_, run, _, _, _) => run == "meta")
  let mut groups : Array ((String × String × String × String) × Array (Array String)) := #[]
  for i in [0:runs.size] do
    for (u, _, l, n, m) in runs[i]! do
      let c := causeOf defectOf u l n m (anon.contains s!"{u}|{l}|{n}") (cert.contains s!"{u}|{n}")
      let key := (u, l, c, msgClass m)
      let mut idx := groups.size
      match groups.findIdx? (·.1 == key) with
      | some j => idx := j
      | none => groups := groups.push (key, Array.replicate runs.size #[])
      groups := groups.modify idx fun (k, per) => (k, per.modify i (·.push n))
  for ((u, l, c, cls), per) in groups do
    let sorted := per.map fun ns => ns.qsort (· < ·)
    let stable := sorted.all (· == sorted[0]!)
    let union := (sorted.foldl (· ++ ·) #[]).qsort (· < ·) |>.toList.eraseDups
    let who := if !stable then "varies := true"
      else if union.length ≤ 6 then s!"names := [{", ".intercalate (union.map (·.quote))}]"
      else s!"count := {sorted[0]!.size}"
    IO.println s!"  \{ unit := {u.quote}, leg := {l.quote}, cause := {c.quote},\n    msg := {cls.quote}, {who} },"
  return 0

end Tests.Ix.Compile.Harness
