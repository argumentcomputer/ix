import IxCCCorrect.CompileCertified
import IxCCTests.Compile.Run

/-! # `tests-compile-certified`: the certified route's compiler on every committed root

`IxCC.Correct.compileCertified` is `Compile.compile` followed by the untrusted shape
producer and the hook's shape decision (`IxCCCorrect.CompileCertified`). For every
root of every corpus family (`IxCCTests.Corpus.families` and `phase2-arity`; the
machines family as machines, the others as plain executables), under `rc off`:

* **Twice in one process** (two separate evaluations), compared: the executable, the
  certificate text and the claim, or the typed decline.
* **Again in another process, in another environment** (`--child`, the environment of
  `tests-pure-compile`'s other process), compared.
* **Against `Compile.compile`**: where the certified route accepts, the same output;
  where it declines with `compile`'s reason, `compile` refuses with that reason; where
  it declines at the shape decision, `compile` accepts.

Then a table per family: the roots, how many `compile` accepts, how many the certified
route accepts, and the declines by reason. Exits 1 on any disagreement; the counts are
reported, not required.

`tests-compile-certified [--step N] [--only LABEL-PREFIX] [--no-child]`. This
executable imports the target statements, so it is built beside the shared program
build (`IxCC.Tools.BuildGraph.groundingTargets`). -/

set_option autoImplicit false

namespace IxCCTests.Compile.Certified

open IxCC IxCC.Recheck System
open IxCCTests.Compile (fail expect modeOf kindName kindOf Case familyCases childEnv compileRun)

/-- One evaluation of the certified route's compiler. -/
@[noinline] def certifiedRun (run : Nat) (bytes : ByteArray) (target : Ixon.Address)
    (opts : Compile.Options) : Nat × Except Correct.Decline Compile.Output :=
  (run, Correct.compileCertified bytes target opts)

/-- An output or a decline, as what is compared. -/
structure Res where
  exe : ByteArray := .empty
  cert : String := ""
  claim : String := ""
  error : String := ""
  deriving BEq

def Res.of : Except Correct.Decline Compile.Output → Res
  | .ok out => { exe := out.exe, cert := out.cert, claim := reprStr out.claim }
  | .error e => { error := e.render }

def Res.ofCompile : Except Err Compile.Output → Res
  | .ok out => { exe := out.exe, cert := out.cert, claim := reprStr out.claim }
  | .error e => { error := e.render }

def Res.describe (x : Res) : String :=
  if x.error.isEmpty then
    s!"executable {x.exe.size} bytes (blake3 {Ixon.Address.blake3Pure x.exe})"
  else s!"declined: {x.error}"

/-- The class of a decline, for the table. -/
def reasonOf : Correct.Decline → String
  | .compile e => s!"compile {e.stage.name}: {e.code}"
  | .shapeLarge _ => "shape: large"
  | .shapeCert => "shape: cert"
  | .shapeRoot _ => "shape: root"

/-- `--child CLOSURE TARGET MODE KIND DIR`: run the certified route and write the output
(`exe`, `cert`, `claim`) or the decline (`error`) into `DIR`. -/
def child (closure target mode kind dir : String) : IO UInt32 := do
  let some target := Ixon.Address.fromString target | throw (IO.userError "child: target")
  let some rc := modeOf mode | throw (IO.userError "child: mode")
  let some kind := kindOf kind | throw (IO.userError "child: kind")
  let bytes ← IO.FS.readBinFile closure
  let dir : FilePath := dir
  match Correct.compileCertified bytes target { rc, kind } with
  | .ok out =>
    IO.FS.writeBinFile (dir / "exe") out.exe
    IO.FS.writeFile (dir / "cert") out.cert
    IO.FS.writeFile (dir / "claim") (reprStr out.claim)
  | .error e => IO.FS.writeFile (dir / "error") e.render
  return 0

/-- The other process's result for a case. -/
def inChild (work : FilePath) (c : Case) (opts : Compile.Options) : IO Res := do
  let dir := work / "child"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let closure ← IO.FS.realPath c.closure
  let out ← IO.Process.output {
    cmd := (← IO.appPath).toString
    args := #["--child", closure.toString, toString c.target, "off", kindName opts.kind,
              (← IO.FS.realPath dir).toString]
    cwd := some dir, env := childEnv }
  if out.exitCode != 0 then
    return { error := s!"the other process exited {out.exitCode}: {out.stderr}" }
  if ← (dir / "error").pathExists then
    return { error := ← IO.FS.readFile (dir / "error") }
  return { exe := ← IO.FS.readBinFile (dir / "exe"), cert := ← IO.FS.readFile (dir / "cert")
           claim := ← IO.FS.readFile (dir / "claim") }

/-- What one family counted. -/
structure Tally where
  roots : Nat := 0
  compiled : Nat := 0
  certified : Nat := 0
  reasons : List (String × Nat) := []

def Tally.decline (t : Tally) (reason : String) : Tally :=
  match t.reasons.find? (·.1 == reason) with
  | some _ => { t with reasons := t.reasons.map fun (r, n) => if r == reason then (r, n + 1) else (r, n) }
  | none => { t with reasons := t.reasons ++ [(reason, 1)] }

def phase2Arity : FilePath := "fixtures/corpus/phase2-arity/corpus.json"

def run (args : List String) : IO UInt32 := do
  let rec parse : List String → Nat × Option String × Bool → Option (Nat × Option String × Bool)
    | [], acc => some acc
    | "--step" :: n :: rest, (_, o, ch) => n.toNat?.bind fun k => parse rest (k, o, ch)
    | "--only" :: p :: rest, (s, _, ch) => parse rest (s, some p, ch)
    | "--no-child" :: rest, (s, o, _) => parse rest (s, o, false)
    | _, _ => none
  let some (step, only, withChild) := parse args (1, none, true)
    | throw (IO.userError "usage: tests-compile-certified [--step N] [--only LABEL-PREFIX] [--no-child]")
  let r ← IO.mkRef 0
  IO.println "tests-compile-certified"
  IO.FS.withTempDir fun work => do
    let mut table : Array (String × Tally) := #[]
    for path in IxCCTests.Corpus.families ++ [phase2Arity] do
      let kind : X86.Exe.Cert.ExeKind :=
        if path == IxCCTests.Compile.machinesManifest then .machine else .plain
      let cases := (← familyCases path 0 step kind).filter fun c =>
        match only with
        | some p => c.label.startsWith p
        | none => true
      let some c0 := cases[0]? | continue
      let family := (c0.label.splitOn "/").headD c0.label
      IO.println s!"{family} ({path}): {cases.size} roots, {kindName kind}, rc off"
      let mut t : Tally := {}
      for c in cases do
        let opts : Compile.Options := { kind }
        let bytes ← IO.FS.readBinFile c.closure
        let t0 ← IO.monoMsNow
        let (_, first) ← IO.lazyPure fun _ => certifiedRun 0 bytes c.target opts
        let t1 ← IO.monoMsNow
        let (_, second) ← IO.lazyPure fun _ => certifiedRun 1 bytes c.target opts
        let a := Res.of first
        let b := Res.of second
        expect r (a == b) s!"{c.label}: two evaluations differ: {a.describe} / {b.describe}"
        if withChild then
          let other ← inChild work c opts
          expect r (other == a) s!"{c.label}: the other process differs: {other.describe}"
        -- against `Compile.compile`
        let (_, plain) ← IO.lazyPure fun _ => compileRun 2 bytes c.target opts
        let k := Res.ofCompile plain
        match first, plain with
        | .ok _, _ => expect r (k == a) s!"{c.label}: the certified route's output is not compile's"
        | .error (.compile e), .error e' =>
          expect r (e == e') s!"{c.label}: declined with compile's reason {e.render}, compile refuses with {e'.render}"
        | .error (.compile e), .ok _ =>
          fail r s!"{c.label}: declined with compile's reason {e.render}, and compile accepts"
        | .error _, .ok _ => pure ()
        | .error d, .error e' => fail r s!"{c.label}: declined at {reasonOf d}, and compile refuses: {e'.render}"
        t := { t with roots := t.roots + 1 }
        if plain matches .ok _ then t := { t with compiled := t.compiled + 1 }
        match first with
        | .ok _ => t := { t with certified := t.certified + 1 }
        | .error d => t := t.decline (reasonOf d)
        IO.println s!"  {c.label}: {a.describe} ({t1 - t0} ms)"
      IO.println s!"  {family}: {t.roots} roots, compile accepts {t.compiled}, the certified route accepts \
        {t.certified}"
      for (reason, n) in t.reasons do
        IO.println s!"    declined {n}: {reason}"
      table := table.push (family, t)
    IO.println "summary (family: roots, compile accepts, certified accepts; declines)"
    let mut all : Tally := {}
    for (family, t) in table do
      IO.println s!"  {family}: {t.roots}, {t.compiled}, {t.certified}; \
        {", ".intercalate (t.reasons.map fun (reason, n) => s!"{reason} {n}")}"
      all := { all with roots := all.roots + t.roots, compiled := all.compiled + t.compiled
                        certified := all.certified + t.certified }
    IO.println s!"  all: {all.roots} roots, compile accepts {all.compiled}, the certified route accepts {all.certified}"
  let failures ← r.get
  if failures == 0 then
    IO.println "tests-compile-certified: ok"
    return 0
  else
    IO.println s!"tests-compile-certified: {failures} failures"
    return 1

end IxCCTests.Compile.Certified
