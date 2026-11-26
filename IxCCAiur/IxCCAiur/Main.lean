import IxCCAiur.Driver
import IxCCAiur.ScheduleJson

/-! # `ixcc-aiur`

```text
ixcc-aiur CLOSURE.ixe EQUATIONS.json [--root NAME] [--args N,N,…] [-o PACKAGE.ixa] [--stats]
```

Takes one root of a closure through the front half (`Recheck.runFir`), the
lowering and Formal Aiur's preparation; evaluates the world check on the
prepared source (`World.checkWorld`, the hypothesis of the theorems in
`IxCCAiur.Claim`); evaluates the root on the `Nat` arguments at Fir and on
Aiur's evaluator; and, when the check holds and the two observations agree,
writes the execution package for that invocation (`Driver.package`).
`--stats` prints the compiled chips. With several roots, `--root` selects
one; the entry is export 0 of what is selected.

It proves nothing itself: the package goes to the Rust host
(`cargo run --release -p aiur --features parallel --example ixcc_prove`). -/

open IxCC IxCC.AiurBackend

namespace IxCC.AiurBackend.Main

structure Options where
  closure : Option String := none
  equations : Option String := none
  root : Option String := none
  args : Option (List Nat) := none
  out : Option String := none
  adviceOut : Option String := none
  execPackage : Bool := false
  typed : Bool := false
  inlineFuse : Bool := false
  enableGuesses : Bool := false
  skipAiurEval : Bool := false
  schedule : Option String := none
  noInline : Bool := false
  pairTable : Bool := false
  stats : Bool := false

def usage : String :=
  "usage: ixcc-aiur CLOSURE.ixe [--equations EQUATIONS.json | EQUATIONS.json] \
[--root NAME|ADDR|NAME=ADDR] [--args N,N,...] [-o PACKAGE.ixa] [--advice-out ADVICE.ixa] \
[--exec] [--typed] [--inline-fuse] [--enable-guesses] [--skip-aiur-eval] \
[--schedule SCHEDULE.json] [--no-inline] [--pair-table] [--stats]"

def parseNats (s : String) : Except String (List Nat) :=
  (s.splitOn ",").filter (· != "") |>.mapM fun w =>
    match w.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: {w}"

def parse : List String → Options → Except String Options
  | [], o => .ok o
  | "--equations" :: path :: rest, o => parse rest { o with equations := some path }
  | "--root" :: name :: rest, o => parse rest { o with root := some name }
  | "--args" :: ns :: rest, o => do parse rest { o with args := some (← parseNats ns) }
  | "-o" :: path :: rest, o => parse rest { o with out := some path }
  | "--advice-out" :: path :: rest, o => parse rest { o with adviceOut := some path }
  | "--exec" :: rest, o => parse rest { o with execPackage := true }
  | "--typed" :: rest, o => parse rest { o with typed := true }
  | "--inline-fuse" :: rest, o => parse rest { o with inlineFuse := true }
  | "--enable-guesses" :: rest, o => parse rest { o with enableGuesses := true }
  | "--skip-aiur-eval" :: rest, o => parse rest { o with skipAiurEval := true }
  | "--schedule" :: path :: rest, o => parse rest { o with schedule := some path }
  | "--no-inline" :: rest, o => parse rest { o with noInline := true }
  | "--pair-table" :: rest, o => parse rest { o with pairTable := true }
  | "--stats" :: rest, o => parse rest { o with stats := true }
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown option {arg}"
    else if o.closure.isNone then parse rest { o with closure := some arg }
    else if o.equations.isNone then parse rest { o with equations := some arg }
    else .error s!"unexpected argument {arg}"

def showObs : Option Sem.Obs → String
  | some o => reprStr o
  | none => "none"

def printChipStats (chips : List (String × Nat × Nat × Nat)) (ms : Nat) : IO Unit := do
  IO.println s!"chips: {chips.length} ({ms} ms)"
  for (name, columns, sends, memory) in chips do
    IO.println s!"chip {name}: columns {columns}, calls {sends}, memory {memory}"

def runTyped (o : Options) (front : Driver.Front) : IO UInt32 := do
  let fir := front.levels.fir
  let baseSched ← match o.schedule with
    | some schedPath =>
      let text ← IO.FS.readFile schedPath
      IO.ofExcept (ScheduleJson.fromJsonString text)
    | none => pure ({} : Schedule.CircuitSchedule)
  let sched : Schedule.CircuitSchedule := {
    baseSched with
    autoInline := if o.noInline then false else baseSched.autoInline
    rangeCheck := if o.pairTable then .pairTable else baseSched.rangeCheck
  }
  let start ← IO.monoMsNow
  let (linked, advice?, firWork) ←
    if o.enableGuesses then
      let res ← IO.ofExcept (Driver.linkTypedWithGuesses front.levels.src fir 0 sched o.inlineFuse)
      let chs := res.manifest.channels.map (·.channel)
      IO.println s!"guesses: rewritten {res.resolved.length} ({chs}), skipped {res.skipped.length}"
      for (cid, reason) in res.skipped do
        IO.println s!"guesses: skipped cid={cid}: {reason}"
      pure (res.linked, res.advice, res.foldedFir)
    else
      let linked ← IO.ofExcept (Driver.linkTyped front.levels.src fir 0 sched o.inlineFuse)
      pure (linked, none, fir)
  IO.println s!"lowered (typed, inline-fuse {o.inlineFuse}, guesses {o.enableGuesses}, \
    tier {reprStr linked.lowered.tier}, \
    fir-shapes {linked.shapeAccepted}, ret {reprStr linked.exportRep}): \
    {linked.lowered.program.functions.length} functions, \
    entry {linked.entry} ({(← IO.monoMsNow) - start} ms)"
  let world := Driver.typedWorldReport linked
  IO.println s!"world: tables {world.tables}, library {world.library}, functions {world.functions}, \
    refuses changed bodies and a changed table {world.refuses}"
  unless world.failing.isEmpty do
    IO.println s!"world: lowered functions that differ from the prepared source: {world.failing}"
  let arity := match o.args with
    | some ns => ns.length
    | none =>
      match fir.exports[0]?.bind fir.fun? with
      | some fd => fd.params.length
      | none => 0
  IO.println s!"shape: {Driver.shapeCheck front.levels arity} \
    (root 0 at {arity} Nat arguments; where true the claim has no stuck-source disjunct)"
  let mut agree := true
  if let some args := o.args then
    let start ← IO.monoMsNow
    let expected := Driver.firRun fir 0 args
    IO.println s!"fir: {reprStr expected} ({(← IO.monoMsNow) - start} ms)"
    if o.skipAiurEval then
      IO.println "aiur: skipped (--skip-aiur-eval)"
      agree := expected matches .ok (some _)
    else
      let start ← IO.monoMsNow
      let actual :=
        if o.enableGuesses then
          Driver.typedAiurRunWithAdvice firWork linked advice? args
        else
          Driver.typedAiurRun fir linked args
      match actual with
      | .ok (value, obs) =>
        IO.println s!"aiur: value {reprStr value}, observation {showObs obs} ({(← IO.monoMsNow) - start} ms)"
      | .error e => IO.println s!"aiur: no derivation found: {e} ({(← IO.monoMsNow) - start} ms)"
      agree := match expected, actual with
        | .ok (some a), .ok (_, some b) => a == b
        | _, _ => false
    IO.println s!"agree: {agree}"
  if let some advPath := o.adviceOut then
    match advice? with
    | some adv =>
      let advStart ← IO.monoMsNow
      let advBytes ← IO.ofExcept (Driver.compileAdvicePackage adv)
      Aiur.Artifact.write advPath advBytes
      IO.println s!"advice: {advPath}, {advBytes.size} bytes, entries {adv.entries} \
        ({(← IO.monoMsNow) - advStart} ms)"
    | none =>
      IO.println s!"advice: skipped writing {advPath} (no guesses rewritten)"
  if let some path := o.out then
    unless world.ok do
      IO.eprintln "ixcc-aiur: the world check failed; no package written"
      return 1
    unless agree do
      IO.eprintln "ixcc-aiur: the evaluators do not agree on a value; no package written"
      return 1
    let kind : CompiledCert.ArtifactKind := if o.execPackage then .execution else .program
    let start ← IO.monoMsNow
    let compiled ← IO.ofExcept (Driver.compileTypedPackage linked sched kind (o.args.getD []))
    let elapsed := (← IO.monoMsNow) - start
    if o.stats then
      printChipStats compiled.chips elapsed
    Aiur.Artifact.write path compiled.bytes
    IO.println s!"package: {path}, {compiled.bytes.size} bytes, kind {compiled.kind.label}, \
      blake3 {compiled.digest} ({elapsed} ms)"
  else if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.typedChipStats linked sched)
    printChipStats chips ((← IO.monoMsNow) - start)
  return 0

def run (o : Options) : IO UInt32 := do
  let some closure := o.closure
    | IO.eprintln usage; return 2
  let bytes ← IO.FS.readBinFile closure
  let start ← IO.monoMsNow
  let front ← match o.equations with
    | some eqPath =>
      let text ← IO.FS.readFile eqPath
      let json ← IO.ofExcept (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text)
      if o.enableGuesses then
        IO.ofExcept (Driver.frontWithGuesses bytes json o.root.toList)
      else
        IO.ofExcept (Driver.front bytes json o.root.toList)
    | none =>
      IO.ofExcept (Driver.frontAuto bytes o.root.toList)
  let fir := front.levels.fir
  IO.println s!"front: roots {front.input.names}, fir functions {fir.funList.length}, \
    constructors {fir.ctors.length}, exports {fir.exports.length} ({(← IO.monoMsNow) - start} ms)"
  if o.typed || o.enableGuesses then
    return ← runTyped o front
  let start ← IO.monoMsNow
  let linked ← IO.ofExcept (Driver.link fir 0)
  IO.println s!"lowered: {linked.lowered.functions.length} functions, entry {linked.entry} \
    ({(← IO.monoMsNow) - start} ms)"
  let world := Driver.worldReport linked
  IO.println s!"world: tables {world.tables}, library {world.library}, functions {world.functions}, \
    refuses changed bodies and a changed table {world.refuses}"
  unless world.failing.isEmpty do
    IO.println s!"world: lowered functions that differ from the prepared source: {world.failing}"
  let arity := match o.args with
    | some ns => ns.length
    | none =>
      match fir.exports[0]?.bind fir.fun? with
      | some fd => fd.params.length
      | none => 0
  IO.println s!"shape: {Driver.shapeCheck front.levels arity} \
    (root 0 at {arity} Nat arguments; where true the claim has no stuck-source disjunct)"
  let mut agree := true
  if let some args := o.args then
    let start ← IO.monoMsNow
    let expected := Driver.firRun fir 0 args
    IO.println s!"fir: {reprStr expected} ({(← IO.monoMsNow) - start} ms)"
    if o.skipAiurEval then
      IO.println "aiur: skipped (--skip-aiur-eval)"
      agree := expected matches .ok (some _)
    else
      let start ← IO.monoMsNow
      let actual := Driver.aiurRun fir linked args
      match actual with
      | .ok (value, obs) =>
        IO.println s!"aiur: value {reprStr value}, observation {showObs obs} ({(← IO.monoMsNow) - start} ms)"
      | .error e => IO.println s!"aiur: no derivation found: {e} ({(← IO.monoMsNow) - start} ms)"
      agree := match expected, actual with
        | .ok (some a), .ok (_, some b) => a == b
        | _, _ => false
    IO.println s!"agree: {agree}"
  if let some path := o.out then
    unless world.ok do
      IO.eprintln "ixcc-aiur: the world check failed; no package written"
      return 1
    unless agree do
      IO.eprintln "ixcc-aiur: the evaluators do not agree on a value; no package written"
      return 1
    let kind : CompiledCert.ArtifactKind := if o.execPackage then .execution else .program
    let start ← IO.monoMsNow
    let compiled ← IO.ofExcept (Driver.compilePackage linked kind (o.args.getD []))
    let elapsed := (← IO.monoMsNow) - start
    if o.stats then
      printChipStats compiled.chips elapsed
    Aiur.Artifact.write path compiled.bytes
    IO.println s!"package: {path}, {compiled.bytes.size} bytes, kind {compiled.kind.label}, \
      blake3 {compiled.digest} ({elapsed} ms)"
  else if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.chipStats linked)
    printChipStats chips ((← IO.monoMsNow) - start)
  return 0

end IxCC.AiurBackend.Main

def main (argv : List String) : IO UInt32 := do
  match IxCC.AiurBackend.Main.parse argv {} with
  | .ok o => IxCC.AiurBackend.Main.run o
  | .error e =>
    IO.eprintln s!"ixcc-aiur: {e}"
    IO.eprintln IxCC.AiurBackend.Main.usage
    return 2
