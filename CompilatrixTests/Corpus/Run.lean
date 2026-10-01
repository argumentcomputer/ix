import CompilatrixTests.Corpus.Manifest
import CompilatrixTests.Pipeline.Levels

/-! The corpus suite (MT.2): every root of every registered corpus family,
against its frozen cases (`compilatrix/corpus/1`).

For each root the compiler (`Recheck.ingress`, `produce`, `run`) either

* **declines** it, and then the manifest must record exactly that
  `stage: code` (an unexpected decline fails, so a decline is always a
  reviewed fact of the manifest; a root the manifest expects declined must
  not compile); or
* **compiles** it, and then every case runs at every level the pipeline suite
  checks (`CompilatrixTests.Pipeline.Levels.runLevel`): SrcEval on the checked
  program, Lam, Anf after P1 and after each certificate step, Fir, Own
  (immortal) and Cfg, then Lir, Xv and Xl from `cx_init`'s memory, the typed
  x86 machine and ByteEval on the object's `.text` (only on the cases the
  manifest marks `machine`, since they step one instruction at a time), and
  natively (with `--cc`) under `fixtures/x86/runtime_driver.c`.

The expected observations come from Lean 4.34's interpreter (recorded in the
manifest by `corpus rebuild`) and, where given, an independent constant:

* the source levels (SrcEval to Cfg) have unbounded `Nat`, so they must give
  `ok` and the interpreter's value;
* the word levels (Lir onwards, and native code) must give that value when
  the arguments and the result are below `2⁶³`, and `natOverflow` (status 3)
  when the result is not; a case marked `allow_overflow` may also give
  status 3 (an intermediate value reaches `2⁶³`), which is counted;
* a case with an argument of at least `2⁶³` has no word: only the entry
  wrapper runs (typed x86, ByteEval, native) and must return status 3.

The big-step evaluators nest native frames per recursive call, so the
suite re-runs itself once with a large Lean stack (`LEAN_STACK_SIZE_KB`, as
`tests-src` does for `sum-loop`). -/

namespace CompilatrixTests.Corpus

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src CompilatrixTests.Pipeline
open System

/-- Levels with unbounded `Nat` (before `Rt.lower`). -/
def sourceLevel (level : String) : Bool :=
  ["src", "lam", "fir", "own", "cfg"].contains level || level.startsWith "anf"

def wordLevel (level : String) : Bool := ["lir", "xv", "xl"].contains level

def machineLevel (level : String) : Bool := level == "x86" || level == "bytes"

/-- An outcome that is the `natOverflow` failure (status 3). -/
def overflow (outcome : String) : Bool :=
  outcome == "status 3" || (outcome.startsWith "resource" && (outcome.splitOn "natOverflow").length > 1)

structure Options where
  cc : Option String := none
  work : Option FilePath := none
  manifests : List FilePath := []
  only : List String := []
  roots : List String := []
  machines : Bool := true
  progress : Bool := false

structure Tally where
  compiled : Nat := 0
  declined : Nat := 0
  cases : Nat := 0
  runs : Nat := 0
  native : Nat := 0
  allowed : Nat := 0

/-- Judge one word-level or native outcome against the case. -/
def judge (a : Assert) (label : String) (want : Bool × String) (allow : Bool) (outcome : String)
    (obs : String) : IO Bool := do
  match want with
  | (true, _) => expect a (overflow outcome) s!"{label}: {outcome} {obs}, expected status 3 (no word)"; pure false
  | (false, v) =>
    if allow && overflow outcome then expect a true ""; pure true
    else
      expect a (outcome == "ok") s!"{label}: {outcome}, expected ok {v}"
      expect a (obs == v) s!"{label}: reads back {obs}, expected {v}"
      pure false

/-- Every case of one compiled root at every level, and natively. -/
def runRoot (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (label : String) (r : Root)
    (c : Levels.Compiled) (t : IO.Ref Tally) : IO (Array String) := do
  let levels := Levels.levelNames c
  let some root := c.art.roots.head? | throw (IO.userError s!"{label}: no root")
  expectEq a root.params r.params s!"{label}: parameters"
  let mut times : Array (String × Nat) := levels.toArray.map (·, 0)
  for cs in r.cases do
    let some want := cs.expect r | throw (IO.userError s!"{label} {cs.args}: no expectation")
    let src := cs.sourceObs r
    let noWord := cs.args.any (· ≥ limit)
    for (level, i) in levels.zipIdx do
      let run := if sourceLevel level then !noWord && src.isSome
        else if wordLevel level then !noWord
        else o.machines && (cs.machine || noWord)
      if !run then continue
      let ((outcome, obs), ms) ← timed (Levels.runLevel c level cs.args)
      let obs := (obs.map Rt.renderObs).getD "-"
      let l := s!"{label} {cs.args} at {level}"
      if sourceLevel level then
        expect a (outcome == "ok") s!"{l}: {outcome}, expected ok {src.getD ""}"
        expect a (some obs == src) s!"{l}: reads back {obs}, expected {src.getD ""}"
      else if ← judge a l want cs.allowOverflow outcome obs then
        t.modify fun t => { t with allowed := t.allowed + 1 }
      times := times.modify i fun (n, ms') => (n, ms' + ms)
      t.modify fun t => { t with runs := t.runs + 1 }
      if o.progress then IO.eprintln s!"      {l}: {outcome} {obs} ({ms} ms)"
    t.modify fun t => { t with cases := t.cases + 1 }
  let mut out := #[s!"{label}: {r.cases.length} cases, {levels.length} levels (ms: \
    {", ".intercalate (times.toList.filter (·.2 > 0) |>.map fun (l, ms) => s!"{l} {ms}")})"]
  if let some nt := native then
    let exe ← link nt s!"corpus_{label.replace "/" "_"}" c.art.object root.symbol
    let ((lines, ms)) ← timed (Rt.Native.run exe { stack := 1 <<< 28, ty := root.ty } (r.cases.map (·.args)))
    for (cs, ln) in r.cases.zip lines do
      let some want := cs.expect r | continue
      expect a ln.ok s!"{label} {cs.args} natively: registers not restored"
      let outcome := if ln.status == 0 then "ok" else s!"status {ln.status}"
      if ← judge a s!"{label} {cs.args} natively" want cs.allowOverflow outcome (ln.obs.getD "-") then
        t.modify fun t => { t with allowed := t.allowed + 1 }
    t.modify fun t => { t with native := t.native + lines.length }
    out := out.push s!"  natively: {lines.length} cases agree ({ms} ms)"
  return out

/-- One root: declined as the manifest expects, or compiled and run. -/
def root (a : Assert) (o : Options) (native : Option Rt.Native.Tools) (m : Family) (f : Fixture) (r : Root)
    (t : IO.Ref Tally) : IO (Array String) := do
  let dir : FilePath := m.directory
  let label := s!"{f.name}/{r.name}"
  let inp ← ingressFile (dir / f.closure.path) (dir / f.equations.path) [r.name]
  let result ← IO.lazyPure fun _ => compileInput {} inp
  match result, r.decline with
  | .error e, some d =>
    expect a (e.stage.name == d.stage && e.code == d.code)
      s!"{label}: declined with {e.render}, the manifest expects {d.stage}: {d.code}"
    t.modify fun t => { t with declined := t.declined + 1 }
    return #[s!"{label}: declined as expected: {(e.render.take 160).toString}"]
  | .error e, none =>
    expect a false s!"{label}: declined with {e.render}, but the manifest expects it to compile"
    return #[]
  | .ok _, some d =>
    expect a false s!"{label}: compiled, but the manifest expects the decline {d.stage}: {d.code}"
    return #[]
  | .ok (cert, art), none =>
    let c ← Levels.assemble label cert art
    t.modify fun t => { t with compiled := t.compiled + 1 }
    runRoot a o native label r c t

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  let native : Option Rt.Native.Tools := o.cc.map fun cc => { cc, work }
  let t ← IO.mkRef ({} : Tally)
  IO.println "tests-corpus"
  let manifests := if o.manifests.isEmpty then families else o.manifests
  for path in manifests do
    let m ← Family.read path
    for f in m.fixtures do
      if !o.only.isEmpty && !o.only.contains f.name then continue
      for r in f.roots do
        if !o.roots.isEmpty && !o.roots.contains r.name then continue
        let before ← a.get
        let (lines, ms) ← timed (root a o native m f r t)
        IO.println s!"  {m.family}/{f.name}/{r.name}: {(← a.get) - before} assertions, {ms} ms"
        for l in lines do IO.println s!"    {l}"
        (← IO.getStdout).flush
  let t ← t.get
  IO.println s!"  {t.compiled} roots compiled, {t.declined} declined as expected; {t.cases} cases, \
    {t.runs} level runs{if native.isSome then s!", {t.native} native runs" else ""}; \
    {t.allowed} allowed intermediate overflows"

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--cc" :: cc :: rest => do return { (← parseOptions rest) with cc := some cc }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--only" :: n :: rest => do let o ← parseOptions rest; return { o with only := n :: o.only }
  | "--root" :: n :: rest => do let o ← parseOptions rest; return { o with roots := n :: o.roots }
  | "--no-machines" :: rest => do return { (← parseOptions rest) with machines := false }
  | "--progress" :: rest => do return { (← parseOptions rest) with progress := true }
  | arg :: rest =>
    if arg.startsWith "--" then throw s!"unknown argument {arg}"
    else do let o ← parseOptions rest; return { o with manifests := arg :: o.manifests }

/-- The large stack the big-step evaluators need (as `tests-src`). -/
def stackKb : Nat := CompilatrixTests.Src.Bench.deepStackKb

/-- Usage: `tests-corpus [MANIFEST…] [--cc CC] [--work DIR] [--only FIXTURE]…
[--root ROOT]… [--no-machines] [--progress]`. Without a manifest, every
registered family (`Corpus.families`). -/
def main (args : List String) : IO UInt32 := do
  -- re-run once with a large stack for the big-step evaluators
  if (← IO.getEnv "COMPILATRIX_CORPUS_CHILD").isNone then
    let self ← IO.appPath
    let env : Array (String × Option String) :=
      #[("LEAN_STACK_SIZE_KB", some (toString stackKb)), ("COMPILATRIX_CORPUS_CHILD", some "1")]
    let child ← IO.Process.spawn { cmd := self.toString, args := args.toArray, env := env }
    return ← child.wait
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-corpus: {e}"; return 2
  let a ← IO.mkRef 0
  try
    match o.work with
    | some work => IO.FS.createDirAll work; suite a o work
    | none => IO.FS.withTempDir fun work => suite a o work
    IO.println s!"tests-corpus: {← a.get} assertions passed{if o.cc.isSome then ", native runs agree" else ""}"
    return 0
  catch e =>
    IO.eprintln s!"tests-corpus: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Corpus
