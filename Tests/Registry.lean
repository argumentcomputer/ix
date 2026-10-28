/-
  The test registry: one typed list of every `IxTests` entry, each with the
  place it runs (its tier), and the command line that selects from it.

  `Tests/Main.lean` declares the entries (`registry`) and the entries that
  must stay in their tier (`required`), and calls `Tests.Registry.run`. CI
  derives its partitions from the tiers (`--tier ci:<job>`); a primary
  self-test (`ixtests-registry`) checks the registry against the workflows
  that name those jobs (comments removed), and checks that every required
  entry is registered once, in its tier, and that the required list names an
  entry in every tier that runs in CI. The two landing jobs
  hold the end-to-end checks of the compiler and of the certification, which
  are too slow for every pull request and run in the merge queue.

  Command line (`lake test -- <args>`, `lake exe IxTests <args>`):
  - no arguments: every primary entry;
  - `<name>…`: exactly the named entries, whatever their tier (names match
    exactly; an unknown name is an error);
  - `--tier <tier>` (repeatable): every entry of that tier, where `<tier>`
    is `primary`, `manual`, `ci:<job>`, or `landing` for the two landing jobs;
  - `--ignored`: with no name and no `--tier`, every entry that is not
    primary; with a name or a `--tier`, nothing more (kept so that
    `--ignored <name>…` works as before);
  - `--include-ignored [<name>…]`: every primary entry, then the named
    entries (or, with none named, every other entry);
  - `--exclude=<a,b>`: drop named entries from the selection;
  - `--list`: print `<name>\t<tier>` per entry and exit;
  - `--list-gate <tier>`: print the names of that tier, one per line, and exit.

  Every selected entry runs, in registry order, even after a failure; each
  prints a result line `[ixtests] <name>: ok|FAILED (exit <n>) <ms> ms`, and
  the exit code is the first non-zero one. The Lean environment that some
  runners take is loaded once, on first use.
-/
import LSpec
import Ix.Meta

namespace Tests.Registry

/-- A CI job that runs registry entries by tier. `cli` is a step of
`ci.yml`'s `lean-test` job; the others are `merge-tests.yml` partitions. -/
inductive CiJob where
  | cli
  | compilePipeline
  | compilerClosures
  | compile
  | decompile
  | misc
  /-- The compilers on everything at once: the Lean compiler's output does
  not depend on its schedule, and the Rust compiler's compile, serialize and
  decompile roundtrip over the test environment. -/
  | landingCompilers
  /-- End-to-end checks on Init+Std: the certified compile with its report
  checks against the pipeline and the Rust compiler, in process and through
  `ix compile-lean` (whose artifact must match the reference digest, and
  which the Rust kernel checks with every bound role admitted),
  `ix validate-lean` fidelity, role binding and evidence, a reading premise
  on every inductive, and the admission hash. -/
  | landingInitStd
  deriving DecidableEq, Repr

def CiJob.all : List CiJob :=
  [.cli, .compilePipeline, .compilerClosures, .compile, .decompile, .misc,
   .landingCompilers, .landingInitStd]

/-- The jobs that `--tier landing` selects together. -/
def CiJob.isLanding : CiJob → Bool
  | .landingCompilers | .landingInitStd => true
  | _ => false

/-- The job's name on the command line (`--tier ci:<key>`) and in the workflows. -/
def CiJob.key : CiJob → String
  | .cli => "cli"
  | .compilePipeline => "compile-pipeline"
  | .compilerClosures => "compiler-closures"
  | .compile => "compile"
  | .decompile => "decompile"
  | .misc => "misc"
  | .landingCompilers => "landing-compilers"
  | .landingInitStd => "landing-initstd"

/-- Where an entry runs. -/
inductive Tier where
  /-- `lake test` with no arguments: CI's `lean-test` job and Nix's `ix-tests`. -/
  | primary
  /-- Named by one CI job. -/
  | ci (job : CiJob)
  /-- Run by hand only; the reason says why it is in no gate. -/
  | manual (reason : String)
  deriving Repr

def Tier.key : Tier → String
  | .primary => "primary"
  | .ci job => s!"ci:{job.key}"
  | .manual _ => "manual"

/-- The tier a `--tier`/`--list-gate` argument names. -/
def Tier.parse? (s : String) : Option (Tier → Bool) :=
  if s == "primary" then some fun | .primary => true | _ => false
  else if s == "landing" then some fun | .ci j => j.isLanding | _ => false
  else if s == "manual" then some fun | .manual _ => true | _ => false
  else if s.startsWith "ci:" then
    let key := (s.drop 3).toString
    (CiJob.all.find? (·.key == key)).map fun job =>
      fun | .ci j => j == job | _ => false
  else none

/-- What an entry runs. -/
inductive Body where
  /-- LSpec suites (values; built when their module initializes, as before). -/
  | suite (tests : List LSpec.TestSeq)
  /-- LSpec suites built by an IO action when the entry is selected. -/
  | suiteIO (tests : IO (List LSpec.TestSeq))
  /-- A runner; its result is the exit code. -/
  | runner (run : IO UInt32)
  /-- A runner that takes the test binary's Lean environment. -/
  | env (run : Lean.Environment → IO UInt32)

structure Entry where
  name : String
  tier : Tier
  body : Body

/-- Smart constructors, so that a registration reads `.suite "name" tier tests`. -/
def Entry.suite (name : String) (tier : Tier) (tests : List LSpec.TestSeq) : Entry :=
  ⟨name, tier, .suite tests⟩
def Entry.suiteIO (name : String) (tier : Tier) (tests : IO (List LSpec.TestSeq)) : Entry :=
  ⟨name, tier, .suiteIO tests⟩
def Entry.runner (name : String) (tier : Tier) (run : IO UInt32) : Entry :=
  ⟨name, tier, .runner run⟩
def Entry.env (name : String) (tier : Tier) (run : Lean.Environment → IO UInt32) : Entry :=
  ⟨name, tier, .env run⟩

/-- A workflow line without its YAML comment: from the first `#` at the line's
start or after a space or a tab. A `#` inside a quoted string after a space is
cut too, which can only hide a mention, never invent one. -/
def stripComment (line : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut prev := ' '
  for c in line.toList do
    if c == '#' && (prev == ' ' || prev == '\t') then break
    out := out.push c
    prev := c
  return String.ofList out.toList

/-- A workflow's text without its YAML comments, so that a commented-out step
does not count as running a tier. A step disabled by an `if:` still counts:
the check is textual. -/
def stripComments (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map stripComment)

/-- The registry's own consistency checks, against the workflows that name
the CI jobs (comments removed). Returns the problems found (empty: consistent). -/
def problems (entries : List Entry) (workflows : List (String × String)) : List String := Id.run do
  let workflows := workflows.map fun (file, text) => (file, stripComments text)
  let mut out : List String := []
  let names := entries.map (·.name)
  for n in names.eraseDups do
    if names.count n > 1 then out := out ++ [s!"entry {n} is registered {names.count n} times"]
  for e in entries do
    if e.name.isEmpty || e.name.startsWith "-" || e.name.contains '=' then
      out := out ++ [s!"entry name '{e.name}' is not a plain word"]
    if let .manual reason := e.tier then
      if reason.trimAscii.isEmpty then out := out ++ [s!"manual entry {e.name} has no reason"]
  for job in CiJob.all do
    unless entries.any (fun e => match e.tier with | .ci j => j == job | _ => false) do
      out := out ++ [s!"CI job ci:{job.key} has no entry"]
    let mention := s!"--tier ci:{job.key}"
    unless workflows.any (fun (_, text) => (text.splitOn mention).length > 1) do
      out := out ++ [s!"no workflow runs '{mention}'"]
  -- every `--tier ci:<key>` a workflow names is a job of the registry
  for (file, text) in workflows do
    for chunk in (text.splitOn "--tier ci:").drop 1 do
      let key := chunk.takeWhile (fun c => c.isAlphanum || c == '-') |>.toString
      unless CiJob.all.any (·.key == key) do
        out := out ++ [s!"{file} names --tier ci:{key}, which is no CI job of the registry"]
  return out

def workflowFiles : List System.FilePath :=
  [".github/workflows/ci.yml", ".github/workflows/merge-tests.yml"]

/-- Retained behavior checks must occur exactly once in their required tier,
including entries that would otherwise disappear silently from CI. -/
def coverageProblems (entries : List Entry) (required : List (String × String)) : List String :=
  required.filterMap fun (name, tier) =>
    match entries.filter (·.name == name) with
    | [entry] => if entry.tier.key == tier then none else
        some s!"required entry {name} runs in {entry.tier.key}, expected {tier}"
    | hits => some s!"required entry {name} is registered {hits.length} times"

/-- The tiers that run in CI: `primary` and every CI job. -/
def ciTierKeys : List String := "primary" :: CiJob.all.map (s!"ci:{·.key}")

/-- The required list itself: it names an entry in every tier that runs in CI,
and only such tiers, so that an emptied or truncated list is a problem rather
than a check that passes on nothing. -/
def requiredProblems (required : List (String × String)) : List String :=
  ciTierKeys.filterMap (fun tier =>
    if required.any (·.2 == tier) then none else some s!"no required entry runs in {tier}") ++
  required.filterMap fun (name, tier) =>
    if ciTierKeys.contains tier then none else
      some s!"required entry {name} names {tier}, which is not a tier that runs in CI"

/-- Each required entry is load-bearing: with it removed, or moved to the
manual tier, the coverage check fails. -/
def mutationProblems (entries : List Entry) (required : List (String × String)) : List String :=
  required.filterMap fun (name, _) =>
    let removed := entries.filter (·.name != name)
    let manual := entries.map fun e => if e.name == name then { e with tier := .manual "x" } else e
    if (coverageProblems removed required).isEmpty then
      some s!"removing required entry {name} passes the coverage check"
    else if (coverageProblems manual required).isEmpty then
      some s!"moving required entry {name} to the manual tier passes the coverage check"
    else none

/-- Every check of the self-test that reads no file. -/
def selfTestProblems (entries : List Entry) (required : List (String × String))
    (workflows : List (String × String)) : List String :=
  problems entries workflows ++ requiredProblems required ++ coverageProblems entries required ++
    mutationProblems entries required

/-- The primary self-test `ixtests-registry`. -/
def selfTest (entries : List Entry) (required : List (String × String)) : IO UInt32 := do
  let workflows ← workflowFiles.mapM fun f => do pure (f.toString, ← IO.FS.readFile f)
  let ps := selfTestProblems entries required workflows
  for p in ps do IO.eprintln s!"[ixtests-registry] {p}"
  if ps.isEmpty then
    IO.println s!"[ixtests-registry] {entries.length} entries, {required.length} required; \
      CI jobs and workflows agree"
    return 0
  return 1

/-- The registry with its own self-test in front. -/
def withSelfTest (entries : List Entry) (required : List (String × String)) : List Entry :=
  ⟨"ixtests-registry", .primary, .runner (selfTest entries required)⟩ :: entries

structure Options where
  names : List String := []
  tiers : List (Tier → Bool) := []
  ignored : Bool := false
  includeIgnored : Bool := false
  exclude : List String := []
  list : Bool := false
  listGate : Option (Tier → Bool) := none

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--tier" :: t :: rest, o => match Tier.parse? t with
    | some p => parseArgs rest { o with tiers := o.tiers ++ [p] }
    | none => .error s!"unknown tier '{t}' (primary, landing, manual, ci:<job>)"
  | "--list-gate" :: t :: rest, o => match Tier.parse? t with
    | some p => parseArgs rest { o with listGate := some p }
    | none => .error s!"unknown tier '{t}' (primary, landing, manual, ci:<job>)"
  | "--list" :: rest, o => parseArgs rest { o with list := true }
  | "--ignored" :: rest, o => parseArgs rest { o with ignored := true }
  | "--include-ignored" :: rest, o => parseArgs rest { o with includeIgnored := true }
  | a :: rest, o =>
    if a.startsWith "--exclude=" then
      let xs := ((a.drop "--exclude=".length).toString.splitOn ",").filter (!·.isEmpty)
      parseArgs rest { o with exclude := o.exclude ++ xs }
    else if a.startsWith "-" then .error s!"unknown option '{a}'"
    else parseArgs rest { o with names := o.names ++ [a] }

def isPrimary (e : Entry) : Bool := match e.tier with | .primary => true | _ => false

/-- The entries an invocation selects, in registry order. -/
def select (entries : List Entry) (o : Options) : Except String (List Entry) := do
  for n in o.names ++ o.exclude do
    unless entries.any (·.name == n) do throw s!"no test entry named '{n}'"
  -- a tier that selects nothing is an error, not an empty passing run
  for p in o.tiers do
    unless entries.any (p ·.tier) do throw "a --tier selects no entry"
  let explicit := !o.names.isEmpty || !o.tiers.isEmpty
  let chosen (e : Entry) : Bool :=
    o.names.contains e.name || o.tiers.any (· e.tier) ||
    (o.includeIgnored && isPrimary e) ||
    (!explicit && o.includeIgnored) ||
    (!explicit && o.ignored && !isPrimary e) ||
    (!explicit && !o.ignored && !o.includeIgnored && isPrimary e)
  let out := entries.filter fun e => chosen e && !o.exclude.contains e.name
  if out.isEmpty then throw "nothing selected"
  return out

def runEntry (getEnv : IO Lean.Environment) (e : Entry) : IO UInt32 := do
  match e.body with
  | .suite tests => LSpec.lspecIO (.ofList [(e.name, tests)]) []
  | .suiteIO tests => LSpec.lspecIO (.ofList [(e.name, ← tests)]) []
  | .runner run => run
  | .env run => run (← getEnv)

/-- Run the selected entries; `required` lists the entries that must stay in
their tier (checked by `ixtests-registry`), and `loadEnv` is `get_env!` of
`Tests/Main.lean`, run at most once. -/
def run (registry : List Entry) (required : List (String × String))
    (loadEnv : IO Lean.Environment) (args : List String) : IO UInt32 := do
  let entries := withSelfTest registry required
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error msg => IO.eprintln s!"error: {msg}"; return 2
  if o.list then
    for e in entries do IO.println s!"{e.name}\t{e.tier.key}"
    return 0
  if let some p := o.listGate then
    for e in entries do
      if p e.tier then IO.println e.name
    return 0
  let selected ← match select entries o with
    | .ok s => pure s
    | .error msg => IO.eprintln s!"error: {msg}"; return 1
  -- Non-primary entries ran after the dispatcher's `get_env!`, which also
  -- set the Lean search path; keep the search path without the import.
  if selected.any (!isPrimary ·) then initLeanSearchPath
  let envRef ← IO.mkRef (none : Option Lean.Environment)
  let getEnv : IO Lean.Environment := do
    if let some env ← envRef.get then return env
    let env ← loadEnv
    envRef.set (some env)
    return env
  let mut first : UInt32 := 0
  let mut failed : Array String := #[]
  for e in selected do
    let start ← IO.monoMsNow
    let code ← try runEntry getEnv e catch ex => do
      IO.eprintln s!"[ixtests] {e.name}: uncaught exception: {ex}"
      pure 1
    let ms := (← IO.monoMsNow) - start
    if code == 0 then
      IO.println s!"[ixtests] {e.name}: ok {ms} ms"
    else
      IO.println s!"[ixtests] {e.name}: FAILED (exit {code}) {ms} ms"
      failed := failed.push e.name
      if first == 0 then first := code
  IO.println s!"[ixtests] {selected.length - failed.size} of {selected.length} passed\
    {if failed.isEmpty then "" else s!"; failed: {", ".intercalate failed.toList}"}"
  return first


/-! Selection, checked at elaboration on a small registry. -/

private def demo : List Entry :=
  [.runner "a" .primary (pure 0), .runner "b" .primary (pure 0),
   .runner "x" (.ci .compile) (pure 0), .runner "x-y" (.ci .compile) (pure 0),
   .runner "g" (.ci .landingCompilers) (pure 0), .runner "m" (.manual "by hand") (pure 0)]

private def picks (args : List String) : List String :=
  match parseArgs args {} >>= select demo with
  | .ok es => es.map (·.name)
  | .error e => ["error: " ++ e]

#guard picks [] == ["a", "b"]
#guard picks ["b"] == ["b"]
-- exact names: `x` no longer selects `x-y`
#guard picks ["x"] == ["x"]
#guard picks ["--ignored", "x"] == ["x"]
#guard picks ["g"] == ["g"]
#guard picks ["--ignored"] == ["x", "x-y", "g", "m"]
#guard picks ["--ignored", "--exclude=m"] == ["x", "x-y", "g"]
#guard picks ["--include-ignored"] == ["a", "b", "x", "x-y", "g", "m"]
#guard picks ["--include-ignored", "g"] == ["a", "b", "g"]
#guard picks ["--tier", "ci:compile"] == ["x", "x-y"]
#guard picks ["--ignored", "--tier", "landing", "a"] == ["a", "g"]
#guard picks ["nope"] == ["error: no test entry named 'nope'"]
#guard picks ["--tier", "ci:nope"] == ["error: unknown tier 'ci:nope' (primary, landing, manual, ci:<job>)"]
#guard picks ["--tier", "ci:tc"] == ["error: unknown tier 'ci:tc' (primary, landing, manual, ci:<job>)"]
#guard picks ["--tier", "ci:decompile"] == ["error: a --tier selects no entry"]
#guard picks ["--ignored", "--exclude=x,x-y,g,m"] == ["error: nothing selected"]
#guard (problems demo [("w", "--tier ci:compile")]).length == CiJob.all.length - 2 + (CiJob.all.length - 1)

#guard coverageProblems demo [("a", "primary"), ("x", "ci:compile")] == []
#guard coverageProblems demo [("missing", "ci:compile")] ==
  ["required entry missing is registered 0 times"]
#guard coverageProblems (demo ++ demo) [("a", "primary")] ==
  ["required entry a is registered 2 times"]
#guard coverageProblems demo [("g", "ci:compile-pipeline")] ==
  ["required entry g runs in ci:landing-compilers, expected ci:compile-pipeline"]

-- removing a required entry, or moving it to the manual tier, fails the coverage check
#guard (coverageProblems (demo.filter (·.name != "x")) [("x", "ci:compile")]) ==
  ["required entry x is registered 0 times"]
#guard (coverageProblems (demo.map fun e => if e.name == "x" then { e with tier := .manual "x" } else e)
  [("x", "ci:compile")]) == ["required entry x runs in manual, expected ci:compile"]
#guard mutationProblems demo [("a", "primary"), ("x", "ci:compile")] == []

-- the required list names every tier that runs in CI, and only those
#guard (requiredProblems []).length == ciTierKeys.length
#guard requiredProblems (ciTierKeys.map ("a", ·)) == []
#guard requiredProblems (("m", "manual") :: ciTierKeys.map ("a", ·)) ==
  ["required entry m names manual, which is not a tier that runs in CI"]

-- a commented-out step does not run a tier; a `#` inside a word is kept
#guard stripComment "  # run: lake test -- --tier ci:compile" == "  "
#guard stripComment "run: lake test -- --tier ci:compile  # the compile tier" ==
  "run: lake test -- --tier ci:compile  "
#guard stripComment "echo a#b" == "echo a#b"
#guard (problems demo [("w", "#--tier ci:compile\n  # --tier ci:landing-compilers")]).length ==
  CiJob.all.length - 2 + CiJob.all.length

end Tests.Registry
