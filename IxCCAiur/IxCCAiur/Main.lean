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
  partialEval : Bool := false
  fieldLower : Bool := false
  field : Driver.FieldTarget := .goldilocks
  degreeBudget : Bool := false
  logBlowup : Nat := 2
  enableGuesses : Bool := false
  skipAiurEval : Bool := false
  schedule : Option String := none
  noInline : Bool := false
  pairTable : Bool := false
  stats : Bool := false

def usage : String :=
  "usage: ixcc-aiur CLOSURE.ixe [--equations EQUATIONS.json | EQUATIONS.json] \
[--root NAME|ADDR|NAME=ADDR] [--args N,N,...] [-o PACKAGE.ixa] [--advice-out ADVICE.ixa] \
[--exec] [--typed] [--inline-fuse] [--partial-eval] [--field-lower] \
[--field goldilocks|bn254|bls12-381] [--degree-budget] [--log-blowup N] \
[--enable-guesses] [--skip-aiur-eval] [--schedule SCHEDULE.json] \
[--no-inline] [--pair-table] [--stats]"

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
  | "--partial-eval" :: rest, o => parse rest { o with partialEval := true }
  | "--field-lower" :: rest, o => parse rest { o with fieldLower := true }
  | "--field" :: name :: rest, o =>
    match Driver.FieldTarget.parse? name with
    | some target => parse rest { o with field := target }
    | none => .error s!"invalid --field '{name}' (expected goldilocks, bn254, or bls12-381)"
  | "--degree-budget" :: rest, o => parse rest { o with degreeBudget := true }
  | "--log-blowup" :: nStr :: rest, o =>
    match nStr.toNat? with
    | some n =>
      if n == 0 then .error "--log-blowup must be positive (>= 1)"
      else parse rest { o with logBlowup := n }
    | none => .error s!"invalid --log-blowup '{nStr}' (expected positive natural number)"
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

def writePackageAndPin (path : String) (closureBytes : ByteArray)
    (equationsBytes? : Option ByteArray) (roots : List String) (exportIdx : Nat)
    (entry : String) (args : List Nat) (compiled : Driver.Compiled)
    (compileMs : Nat) (showStats : Bool) : IO Unit := do
  if showStats then
    printChipStats compiled.chips compileMs
  Aiur.Artifact.write path compiled.bytes
  IO.println s!"package: {path}, {compiled.bytes.size} bytes, kind {compiled.kind.label}, \
    format v{compiled.artifactFormatVersion}, maxDegree {compiled.chosenMaxDegree}, \
    blake3 {compiled.digest} ({compileMs} ms)"
  let pinStart ← IO.monoMsNow
  let pin := Driver.pinJson closureBytes equationsBytes? roots exportIdx entry args compiled
  let pinPath := s!"{path}.pin.json"
  IO.FS.writeFile pinPath (pin.pretty ++ "\n")
  IO.println s!"pin: {pinPath}, program {compiled.programBytes.size} bytes, \
    program_blake3 {compiled.programDigest}, package_blake3 {compiled.digest} \
    ({(← IO.monoMsNow) - pinStart} ms)"

def runTypedWide (o : Options) (front : Driver.Front) (baseSched : Schedule.CircuitSchedule)
    (closureBytes : ByteArray) (equationsBytes? : Option ByteArray) : IO UInt32 := do
  let fir := front.levels.fir
  let sched : Schedule.CircuitSchedule := {
    baseSched with
    autoInline := if o.noInline then false else baseSched.autoInline
    rangeCheck := if o.pairTable then .pairTable else baseSched.rangeCheck
  }
  let start ← IO.monoMsNow
  let (lowered, shapeAccepted, entry, exportRep, resolvedGroups) ←
    if o.enableGuesses then
      let res ← IO.ofExcept (Driver.linkTypedWithGuesses front.levels.src fir 0 sched
        o.inlineFuse o.partialEval o.fieldLower o.field)
      let chs := res.manifest.channels.map (·.channel)
      IO.println s!"guesses: rewritten {res.resolved.length} ({chs}), skipped {res.skipped.length}"
      for (cid, reason) in res.skipped do
        IO.println s!"guesses: skipped cid={cid}: {reason}"
      pure (res.linked.lowered, res.linked.shapeAccepted, res.linked.entry,
        res.linked.exportRep, res.linked.resolvedGroups)
    else
      let res ← IO.ofExcept (Driver.lowerTyped front.levels.src fir 0 sched
        o.inlineFuse o.partialEval o.fieldLower o.field)
      pure (res.lowered, res.shapeAccepted, res.entry, res.exportRep, res.resolvedGroups)
  IO.println s!"lowered (typed, field {o.field.label}, inline-fuse {o.inlineFuse}, \
    partial-eval {o.partialEval}, field-lower {o.fieldLower}, guesses {o.enableGuesses}, \
    tier {reprStr lowered.tier}, fir-shapes {shapeAccepted}, ret {reprStr exportRep}): \
    {lowered.program.functions.length} functions, entry {entry} ({(← IO.monoMsNow) - start} ms)"
  let world ← match o.field with
    | .bn254 => IO.ofExcept (Driver.typedWorldReportForPrime FieldLower.bn254Modulus lowered 0)
    | .bls12381 => IO.ofExcept (Driver.typedWorldReportForPrime FieldLower.bls12381Modulus lowered 0)
    | .goldilocks => IO.ofExcept (Driver.typedWorldReportForPrime FieldLower.goldilocksModulus lowered 0)
  IO.println s!"world ({o.field.label}): tables {world.tables}, library {world.library}, \
    functions {world.functions}, refuses changed bodies and a changed table {world.refuses}"
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
      let actual := match o.field with
        | .bn254 => Driver.typedAiurRunForPrime FieldLower.bn254Modulus fir lowered exportRep args 0
        | .bls12381 => Driver.typedAiurRunForPrime FieldLower.bls12381Modulus fir lowered exportRep args 0
        | .goldilocks => Driver.typedAiurRunForPrime FieldLower.goldilocksModulus fir lowered exportRep args 0
      match actual with
      | .ok (valStr, obs) =>
        IO.println s!"aiur ({o.field.label}): value {valStr}, observation {showObs obs} ({(← IO.monoMsNow) - start} ms)"
      | .error e => IO.println s!"aiur ({o.field.label}): no derivation found: {e} ({(← IO.monoMsNow) - start} ms)"
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
    let compiled ← IO.ofExcept (Driver.compileTypedForField o.field lowered 0 sched resolvedGroups
      kind (o.args.getD []) o.degreeBudget o.logBlowup)
    let elapsed := (← IO.monoMsNow) - start
    if o.degreeBudget then
      IO.println s!"degree-budget: logBlowup {o.logBlowup}, chosen maxDegree {compiled.chosenMaxDegree}"
    writePackageAndPin path closureBytes equationsBytes? front.input.names 0 entry
      (o.args.getD []) compiled elapsed o.stats
  else if o.stats then
    let start ← IO.monoMsNow
    let (chips, chosenMaxDeg) ← IO.ofExcept (Driver.typedChipStatsForField o.field lowered 0 sched
      o.degreeBudget o.logBlowup)
    let elapsed := (← IO.monoMsNow) - start
    if o.degreeBudget then
      IO.println s!"degree-budget: logBlowup {o.logBlowup}, chosen maxDegree {chosenMaxDeg}"
    printChipStats chips elapsed
  return 0

def runTyped (o : Options) (front : Driver.Front) (baseSched : Schedule.CircuitSchedule)
    (closureBytes : ByteArray) (equationsBytes? : Option ByteArray) : IO UInt32 := do
  if o.field.isWide then
    return ← runTypedWide o front baseSched closureBytes equationsBytes?
  let fir := front.levels.fir
  let sched : Schedule.CircuitSchedule := {
    baseSched with
    autoInline := if o.noInline then false else baseSched.autoInline
    rangeCheck := if o.pairTable then .pairTable else baseSched.rangeCheck
  }
  let start ← IO.monoMsNow
  let (linked, advice?, firWork) ←
    if o.enableGuesses then
      let res ← IO.ofExcept (Driver.linkTypedWithGuesses front.levels.src fir 0 sched
        o.inlineFuse o.partialEval o.fieldLower .goldilocks)
      let chs := res.manifest.channels.map (·.channel)
      IO.println s!"guesses: rewritten {res.resolved.length} ({chs}), skipped {res.skipped.length}"
      for (cid, reason) in res.skipped do
        IO.println s!"guesses: skipped cid={cid}: {reason}"
      pure (res.linked, res.advice, res.foldedFir)
    else
      let linked ← IO.ofExcept (Driver.linkTyped front.levels.src fir 0 sched
        o.inlineFuse o.partialEval o.fieldLower)
      pure (linked, none, fir)
  IO.println s!"lowered (typed, field {o.field.label}, inline-fuse {o.inlineFuse}, \
    partial-eval {o.partialEval}, field-lower {o.fieldLower}, guesses {o.enableGuesses}, \
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
    let compiled ← IO.ofExcept (Driver.compileTypedPackage linked sched kind (o.args.getD [])
      o.degreeBudget o.logBlowup)
    let elapsed := (← IO.monoMsNow) - start
    if o.degreeBudget then
      IO.println s!"degree-budget: logBlowup {o.logBlowup}, chosen maxDegree {compiled.chosenMaxDegree}"
    writePackageAndPin path closureBytes equationsBytes? front.input.names 0 linked.entry
      (o.args.getD []) compiled elapsed o.stats
  else if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.typedChipStats linked sched o.degreeBudget o.logBlowup)
    printChipStats chips ((← IO.monoMsNow) - start)
  return 0

def run (o : Options) : IO UInt32 := do
  let some closure := o.closure
    | IO.eprintln usage; return 2
  let bytes ← IO.FS.readBinFile closure
  let baseSched ← match o.schedule with
    | some schedPath =>
      let text ← IO.FS.readFile schedPath
      IO.ofExcept (ScheduleJson.fromJsonString text)
    | none => pure ({} : Schedule.CircuitSchedule)
  let noInlineAddrs :=
    if o.fieldLower then Driver.intrinsicAddresses baseSched else []
  let start ← IO.monoMsNow
  let (front, equationsBytes?) ← match o.equations with
    | some eqPath =>
      let text ← IO.FS.readFile eqPath
      let json ← IO.ofExcept (Src.Hints.checkJsonText text >>= fun () => Lean.Json.parse text)
      let f ← if o.enableGuesses then
        IO.ofExcept (Driver.frontWithGuesses bytes json o.root.toList Src.KernelFront.defaultLimits noInlineAddrs)
      else
        IO.ofExcept (Driver.front bytes json o.root.toList noInlineAddrs)
      pure (f, some text.toUTF8)
    | none =>
      let f ← IO.ofExcept (Driver.frontAuto bytes o.root.toList Src.KernelFront.defaultLimits noInlineAddrs)
      pure (f, none)
  let fir := front.levels.fir
  IO.println s!"front: roots {front.input.names}, fir functions {fir.funList.length}, \
    constructors {fir.ctors.length}, exports {fir.exports.length} ({(← IO.monoMsNow) - start} ms)"
  if o.typed || o.enableGuesses || o.partialEval || o.fieldLower || o.field != .goldilocks then
    return ← runTyped o front baseSched bytes equationsBytes?
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
    let compiled ← IO.ofExcept (Driver.compilePackage linked kind (o.args.getD []) {} []
      o.degreeBudget o.logBlowup)
    let elapsed := (← IO.monoMsNow) - start
    if o.degreeBudget then
      IO.println s!"degree-budget: logBlowup {o.logBlowup}, chosen maxDegree {compiled.chosenMaxDegree}"
    writePackageAndPin path bytes equationsBytes? front.input.names 0 linked.entry
      (o.args.getD []) compiled elapsed o.stats
  else if o.stats then
    let start ← IO.monoMsNow
    let chips ← IO.ofExcept (Driver.chipStats linked {} o.degreeBudget o.logBlowup)
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
