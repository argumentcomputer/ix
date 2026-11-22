import Lean.Data.Json

/-!
Checker for the benchmark fixture pack described by `manifest.json`.

Run from the repository root with the pinned toolchain:

    lean --run benchmarks/fixtures/Check.lean [options]

Options:
- `--root DIR`   fixture pack root (default `benchmarks/fixtures`)
- `--work DIR`   build directory (default `plans/c4-fixtures/build`)
- `--cc CC`      C compiler used where a twin command names `clang` (default `clang`)
- `--cxx CXX`    C++ compiler used where a twin command names `clang++` (default `clang++`)
- `--refs DIR`   reference checkouts (`DIR/<ref_dir>/<path>`); compares every vendored
                 upstream file byte for byte
- `--interpret`  also run each Lean program with `lean --run`
- `--bench`      use the bench arguments: compares the Lean program with its twin and
                 with `bench_expected` where recorded, and raises the stack limit
- `--only A,B`   restrict to the named fixtures

For every fixture, the checker scans the Lean source for forbidden constructs,
checks the recorded verbatim relation to upstream, checks the oracle, compiles
the Lean program (`lean -c`, then `leanc -O3 -DNDEBUG`), runs it and compares
its output, then builds and runs the C/C++ twin and compares its output. The
exit code is 0 only when every check passes.
-/

open Lean System

structure Opts where
  root : FilePath := "benchmarks/fixtures"
  work : FilePath := "plans/c4-fixtures/build"
  cc : String := "clang"
  cxx : String := "clang++"
  refs : Option FilePath := none
  interpret : Bool := false
  bench : Bool := false
  only : List String := []

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--root" :: d :: rest, o => parseOpts rest { o with root := d }
  | "--work" :: d :: rest, o => parseOpts rest { o with work := d }
  | "--cc" :: c :: rest, o => parseOpts rest { o with cc := c }
  | "--cxx" :: c :: rest, o => parseOpts rest { o with cxx := c }
  | "--refs" :: d :: rest, o => parseOpts rest { o with refs := some d }
  | "--interpret" :: rest, o => parseOpts rest { o with interpret := true }
  | "--bench" :: rest, o => parseOpts rest { o with bench := true }
  | "--only" :: names :: rest, o =>
    parseOpts rest { o with only := names.splitOn "," }
  | arg :: _, _ => .error s!"unknown or incomplete option: {arg}"

structure Outcome where
  fixture : String
  check : String
  ok : Bool
  detail : String := ""

def report (r : Outcome) : IO Outcome := do
  let tag := if r.ok then "PASS" else "FAIL"
  IO.println s!"{tag}  {r.fixture}  {r.check}{if r.detail.isEmpty then "" else "  " ++ r.detail}"
  return r

def note (fixture check : String) (ok : Bool) (detail : String := "") : IO Outcome :=
  report { fixture, check, ok, detail }

def orThrow (context : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{context}: {e}")

def field (j : Json) (k : String) [FromJson α] : IO α :=
  orThrow s!"manifest field {k}" (j.getObjValAs? α k)

def optField (j : Json) (k : String) : Option Json :=
  (j.getObjVal? k).toOption.filter (· != Json.null)

/-! ## Static checks on Lean sources -/

inductive Mode where
  | code
  | line
  | block (depth : Nat)
  | str

/-- The source with comments and string literals removed (replaced by spaces). -/
def stripAux : List Char → Mode → List Char → List Char
  | [], _, acc => acc.reverse
  | '/' :: '-' :: rest, .code, acc => stripAux rest (.block 1) (' ' :: acc)
  | '-' :: '-' :: rest, .code, acc => stripAux rest .line (' ' :: acc)
  | '"' :: rest, .code, acc => stripAux rest .str (' ' :: acc)
  | c :: rest, .code, acc => stripAux rest .code (c :: acc)
  | '\n' :: rest, .line, acc => stripAux rest .code ('\n' :: acc)
  | _ :: rest, .line, acc => stripAux rest .line acc
  | '/' :: '-' :: rest, .block d, acc => stripAux rest (.block (d + 1)) acc
  | '-' :: '/' :: rest, .block 1, acc => stripAux rest .code (' ' :: acc)
  | '-' :: '/' :: rest, .block (d + 2), acc => stripAux rest (.block (d + 1)) acc
  | _ :: rest, .block d, acc => stripAux rest (.block d) acc
  | '\\' :: _ :: rest, .str, acc => stripAux rest .str acc
  | '"' :: rest, .str, acc => stripAux rest .code (' ' :: acc)
  | _ :: rest, .str, acc => stripAux rest .str acc

def stripLean (s : String) : String := String.ofList (stripAux s.toList .code [])

def forbiddenWords : List String :=
  ["partial", "unsafe", "Task", "implemented_by", "extrinsicFix"]

/-- Forbidden constructs in the code (outside comments and strings). -/
def forbidden (source : String) : List String :=
  let code := stripLean source
  let words := (code.split (fun c => !(c.isAlphanum || c == '_'))).toList.map (·.toString)
  let found := forbiddenWords.filter (words.contains ·)
  if (code.splitOn "...").length > 1 then found ++ ["..."] else found

def containsText (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

/-- The upstream text before its `main`. -/
def beforeMain (source : String) : String :=
  let lines := source.splitOn "\n"
  let kept := lines.takeWhile fun l =>
    !(l.startsWith "def main" || l.startsWith "unsafe def main")
  "\n".intercalate kept

/-- The text strictly between two markers. -/
def between (source start stop : String) : Option String :=
  match source.splitOn start with
  | _ :: rest :: _ =>
    match rest.splitOn stop with
    | inner :: _ :: _ => some inner
    | _ => none
  | _ => none

def sameBytes (a b : FilePath) : IO Bool := do
  return (← IO.FS.readBinFile a).data == (← IO.FS.readBinFile b).data

/-! ## Running programs -/

def run (cmd : String) (args : Array String) (env : Array (String × Option String) := #[]) :
    IO IO.Process.Output :=
  IO.Process.output { cmd, args, env }

def firstLines (s : String) (n : Nat := 12) : String :=
  "\n    ".intercalate ((s.splitOn "\n").take n)

def compareOutput (fixture check expected : String) (out : IO.Process.Output) (ms : Nat) :
    IO Outcome :=
  if out.exitCode != 0 then
    note fixture check false s!"exit {out.exitCode}\n    stderr: {firstLines out.stderr}"
  else if out.stdout != expected then
    note fixture check false
      s!"output differs\n  expected:\n    {firstLines expected}\n  actual:\n    {firstLines out.stdout}"
  else
    note fixture check true s!"({ms} ms)"

def timed (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← act
  return (a, (← IO.monoMsNow) - t0)

/-- In bench mode, programs run under the hard stack limit, as upstream
`set_stack_size_to_maximum` does. -/
def runProgram (o : Opts) (bin : String) (args : Array String)
    (env : Array (String × Option String)) : IO IO.Process.Output :=
  if o.bench then
    run "sh" (#["-c", "ulimit -s \"$(ulimit -H -s)\"; exec \"$0\" \"$@\"", bin] ++ args) env
  else run bin args env

structure Tools where
  lean : String
  leanc : String

def buildFailure (fixture check : String) (out : IO.Process.Output) : IO Outcome :=
  note fixture check false
    s!"build failed (exit {out.exitCode})\n    {firstLines (out.stdout ++ out.stderr) 20}"

/-! ## Per-fixture checks -/

def checkFixture (o : Opts) (tools : Tools) (repoRoot : FilePath) (repos : Json) (fx : Json) :
    IO (List Outcome) := do
  let name : String ← field fx "name"
  let leanSpec ← orThrow "lean" (fx.getObjVal? "lean")
  let leanPath : String ← field leanSpec "path"
  let leanFile := o.root / leanPath
  let source ← IO.FS.readFile leanFile
  let mut results : List Outcome := []
  -- forbidden constructs
  let bad := forbidden source
  results := results ++ [← note name "no-forbidden-constructs" bad.isEmpty (if bad.isEmpty then "" else s!"found {bad}")]
  -- verbatim relation to upstream
  if let some v := optField leanSpec "verbatim" then
    let kind : String ← field v "kind"
    let upstream : String ← field v "upstream"
    let base := if kind == "namespace-block" then repoRoot else o.root
    let up ← IO.FS.readFile (base / upstream)
    let ok ← match kind with
      | "prefix-before-main" => pure (containsText source (beforeMain up))
      | "namespace-block" =>
        let ns : String ← field v "namespace"
        match between source s!"namespace {ns}\n" s!"end {ns}" with
        | some block => pure (!block.trimAscii.isEmpty && containsText up block.trimAscii.toString)
        | none => pure false
      | other => throw (IO.userError s!"{name}: unknown verbatim kind {other}")
    results := results ++ [← note name s!"verbatim-{kind}" ok s!"({upstream})"]
  -- oracle
  let expectedPath : String ← field fx "expected"
  let oracle ← orThrow "oracle" (fx.getObjVal? "oracle")
  let oracleKind : String ← field oracle "kind"
  if oracleKind == "upstream-expected" then
    let file : String ← field oracle "file"
    let ok ← sameBytes (o.root / expectedPath) (o.root / file)
    results := results ++ [← note name "oracle-is-upstream" ok s!"({file})"]
  -- vendored files, byte for byte
  if let some refs := o.refs then
    let vendored : Array Json ← field fx "vendored"
    let mut bad : List String := []
    for v in vendored do
      let file : String ← field v "file"
      let repo : String ← field v "repository"
      let path : String ← field v "path"
      let refDir : String ← field (← orThrow "repositories" (repos.getObjVal? repo)) "ref_dir"
      unless ← sameBytes (o.root / file) (refs / refDir / path) do bad := bad ++ [file]
    results := results ++ [← note name "vendored-byte-identical" bad.isEmpty (if bad.isEmpty then s!"({vendored.size} files)" else s!"differ: {bad}")]
  -- arguments, environment and expected output
  let args : Array String ← field fx (if o.bench then "bench_args" else "test_args")
  let envJson := (optField fx "env").getD (Json.mkObj [])
  let envObj ← orThrow "env" envJson.getObj?
  let env := envObj.toArray.map fun ⟨k, v⟩ => (k, some (v.getStr?.toOption.getD ""))
  let expected ← if o.bench then
      match optField fx "bench_expected" with
      | some (.str s) => pure (some s)
      | _ => pure none
    else pure (some (← IO.FS.readFile (o.root / expectedPath)))
  -- the Lean program, compiled as upstream `run_test.sh` does
  let cFile := o.work / s!"{name}.c"
  let leanBin := o.work / s!"{name}.lean.out"
  let (leanOut, leanMs) ← timed do
    let c ← run tools.lean #["-c", cFile.toString, leanFile.toString]
    if c.exitCode != 0 then return Sum.inl c
    let l ← run tools.leanc #["-O3", "-DNDEBUG", "-o", leanBin.toString, cFile.toString]
    if l.exitCode != 0 then return Sum.inl l
    return Sum.inr (← timed (runProgram o leanBin.toString args env))
  let mut leanStdout : Option String := none
  match leanOut with
  | .inl failure => results := results ++ [← buildFailure name "lean-compiled" failure]
  | .inr (out, runMs) =>
    leanStdout := if out.exitCode == 0 then some out.stdout else none
    match expected with
    | some e => results := results ++ [← compareOutput name "lean-compiled" e out runMs]
    | none =>
      results := results ++ [← note name "lean-compiled" (out.exitCode == 0)
        s!"(build+run {leanMs} ms, run {runMs} ms; no recorded bench output) {out.stdout.trimAscii}"]
  -- the Lean program, interpreted
  if o.interpret then
    let (out, ms) ← timed (runProgram o tools.lean
      (#["-Dlinter.all=false", "--run", leanFile.toString] ++ args) env)
    match expected with
    | some e => results := results ++ [← compareOutput name "lean-interpreted" e out ms]
    | none => results := results ++ [← note name "lean-interpreted"
        (out.exitCode == 0 && some out.stdout == leanStdout) s!"({ms} ms)"]
  -- the C/C++ twin
  let twin ← orThrow "twin" (fx.getObjVal? "twin")
  let twinPath : String ← field twin "path"
  let compile : Array String ← field twin "compile"
  let twinBin := o.work / s!"{name}.twin"
  let argv := compile.map fun a =>
    if a == "{out}" then twinBin.toString
    else if a == "{src}" then (o.root / twinPath).toString
    else a
  let cmd := match argv[0]? with
    | some "clang" => o.cc
    | some "clang++" => o.cxx
    | some c => c
    | none => ""
  let built ← run cmd (argv.extract 1 argv.size)
  if built.exitCode != 0 then
    results := results ++ [← buildFailure name "twin" built]
  else
    let (out, ms) ← timed (runProgram o twinBin.toString args #[])
    match expected with
    | some e => results := results ++ [← compareOutput name "twin" e out ms]
    | none =>
      let same := out.exitCode == 0 && some out.stdout == leanStdout
      results := results ++ [← note name "twin-matches-lean" same s!"({ms} ms) {out.stdout.trimAscii}"]
  return results

def versionLine (cmd : String) : IO String := do
  try
    let out ← run cmd #["--version"]
    return ((out.stdout.splitOn "\n").headD "").trimAscii.toString
  catch _ => return "(unavailable)"

def main (argv : List String) : IO UInt32 := do
  let o ← match parseOpts argv {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let bin := (← IO.appPath).parent.getD "."
  let tools : Tools := { lean := (bin / "lean").toString, leanc := (bin / "leanc").toString }
  IO.FS.createDirAll o.work
  let manifest ← orThrow "manifest.json" (Json.parse (← IO.FS.readFile (o.root / "manifest.json")))
  let repos ← orThrow "repositories" (manifest.getObjVal? "repositories")
  let fixtures : Array Json ← field manifest "fixtures"
  let repoRoot := o.root / ".." / ".."
  IO.println s!"fixture check: {if o.bench then "bench" else "test"} arguments; {fixtures.size} fixtures in {o.root}"
  IO.println s!"lean:  {tools.lean} ({← versionLine tools.lean})"
  IO.println s!"leanc: {tools.leanc}"
  IO.println s!"cc:    {o.cc} ({← versionLine o.cc})"
  IO.println s!"cxx:   {o.cxx} ({← versionLine o.cxx})"
  IO.println s!"refs:  {o.refs.map (·.toString) |>.getD "(not checked)"}"
  let mut all : List Outcome := []
  let mut rows : List String := []
  for fx in fixtures do
    let name : String ← field fx "name"
    unless o.only.isEmpty || o.only.contains name do continue
    let rs ← try checkFixture o tools repoRoot repos fx catch e =>
      pure [← note name "manifest" false (toString e)]
    all := all ++ rs
    let rung : String ← field fx "rung"
    let variant : String ← field fx "variant"
    let failed := rs.filter (!·.ok)
    rows := rows ++ [s!"{name}\t{rung}\t{variant}\t{rs.length - failed.length}/{rs.length}\t{if failed.isEmpty then "pass" else "FAIL: " ++ ", ".intercalate (failed.map (·.check))}"]
  IO.println "\nsummary (fixture, rung, variant, checks passed, status):"
  for r in rows do IO.println s!"  {r}"
  let failures := all.filter (!·.ok)
  IO.println s!"\n{all.length - failures.length}/{all.length} checks passed"
  return if failures.isEmpty then 0 else 1
